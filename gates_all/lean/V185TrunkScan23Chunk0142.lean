import V185TrunkScan23Chunk0141

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_839087 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 5]
def baseStart_839087 : Nat := 118140960795 + 839087 * 2 ^ 59
def prefixEnd_839087 : Nat := 4983230072969 + 3 ^ 40 * 839087 * 2
def baseEnd_839087 : Nat := 47872771326584866883735

theorem tailTrace_839087 : CollatzResearch.WordTrace tailWord_839087 prefixEnd_839087 47872771326584866883735 := by
  unfold tailWord_839087
  simp only [CollatzResearch.WordTrace]
  refine ⟨30604017111138578495643515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20402678074092385663762343 30604017111138578495643515)
  ·
    refine ⟨45906025666707867743465273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30604017111138578495643515 45906025666707867743465273)
    ·
      refine ⟨34429519250030900807598955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45906025666707867743465273 34429519250030900807598955)
      ·
        refine ⟨51644278875046351211398433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34429519250030900807598955 51644278875046351211398433)
        ·
          refine ⟨38733209156284763408548825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51644278875046351211398433 38733209156284763408548825)
          ·
            refine ⟨29049906867213572556411619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38733209156284763408548825 29049906867213572556411619)
            ·
              refine ⟨43574860300820358834617429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29049906867213572556411619 43574860300820358834617429)
              ·
                refine ⟨510642894150238580093173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43574860300820358834617429 510642894150238580093173)
                ·
                  refine ⟨47872771326584866883735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510642894150238580093173 47872771326584866883735)
                  ·
                    rfl

theorem cell23_839087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 5].length) (baseStart_839087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839087 prefixEnd_839087 := by exact prefixLift 839087
  have htrace : WordTrace (prefixWord ++ tailWord_839087) baseStart_839087 baseEnd_839087 := by
    simpa [prefixWord, tailWord_839087, baseEnd_839087] using wordTrace_append hprefix tailTrace_839087
  have hstable : (prefixWord ++ tailWord_839087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839087).length < 2 ^ (prefixWord ++ tailWord_839087).sum := by decide
  have hdescent : baseEnd_839087 < baseStart_839087 := by decide
  rcases family_descends (prefixWord ++ tailWord_839087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839090 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_839090 : Nat := 118140960795 + 839090 * 2 ^ 59
def prefixEnd_839090 : Nat := 4983230072969 + 3 ^ 40 * 839090 * 2
def baseEnd_839090 : Nat := 430856482381227290216101

theorem tailTrace_839090 : CollatzResearch.WordTrace tailWord_839090 prefixEnd_839090 430856482381227290216101 := by
  unfold tailWord_839090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651031632531927502000681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20402751020085140005335149 7651031632531927502000681)
  ·
    refine ⟨5738273724398945626500511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7651031632531927502000681 5738273724398945626500511)
    ·
      refine ⟨8607410586598418439750767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738273724398945626500511 8607410586598418439750767)
      ·
        refine ⟨12911115879897627659626151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607410586598418439750767 12911115879897627659626151)
        ·
          refine ⟨19366673819846441489439227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911115879897627659626151 19366673819846441489439227)
          ·
            refine ⟨29050010729769662234158841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19366673819846441489439227 29050010729769662234158841)
            ·
              refine ⟨21787508047327246675619131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29050010729769662234158841 21787508047327246675619131)
              ·
                refine ⟨32681262070990870013428697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21787508047327246675619131 32681262070990870013428697)
                ·
                  refine ⟨24510946553243152510071523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32681262070990870013428697 24510946553243152510071523)
                  ·
                    refine ⟨36766419829864728765107285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24510946553243152510071523 36766419829864728765107285)
                    ·
                      refine ⟨430856482381227290216101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36766419829864728765107285 430856482381227290216101)
                      ·
                        rfl

theorem cell23_839090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_839090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839090 prefixEnd_839090 := by exact prefixLift 839090
  have htrace : WordTrace (prefixWord ++ tailWord_839090) baseStart_839090 baseEnd_839090 := by
    simpa [prefixWord, tailWord_839090, baseEnd_839090] using wordTrace_append hprefix tailTrace_839090
  have hstable : (prefixWord ++ tailWord_839090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839090).length < 2 ^ (prefixWord ++ tailWord_839090).sum := by decide
  have hdescent : baseEnd_839090 < baseStart_839090 := by decide
  rcases family_descends (prefixWord ++ tailWord_839090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839197 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_839197 : Nat := 118140960795 + 839197 * 2 ^ 59
def prefixEnd_839197 : Nat := 4983230072969 + 3 ^ 40 * 839197 * 2
def baseEnd_839197 : Nat := 430911424811258371578109

theorem tailTrace_839197 : CollatzResearch.WordTrace tailWord_839197 prefixEnd_839197 430911424811258371578109 := by
  unfold tailWord_839197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608029140740067282147845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20405352760493378188098563 30608029140740067282147845)
  ·
    refine ⟨5739005463888762615402721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30608029140740067282147845 5739005463888762615402721)
    ·
      refine ⟨4304254097916571961552041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5739005463888762615402721 4304254097916571961552041)
      ·
        refine ⟨3228190573437428971164031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4304254097916571961552041 3228190573437428971164031)
        ·
          refine ⟨4842285860156143456746047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228190573437428971164031 4842285860156143456746047)
          ·
            refine ⟨7263428790234215185119071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842285860156143456746047 7263428790234215185119071)
            ·
              refine ⟨10895143185351322777678607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7263428790234215185119071 10895143185351322777678607)
              ·
                refine ⟨16342714778026984166517911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895143185351322777678607 16342714778026984166517911)
                ·
                  refine ⟨24514072167040476249776867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16342714778026984166517911 24514072167040476249776867)
                  ·
                    refine ⟨36771108250560714374665301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24514072167040476249776867 36771108250560714374665301)
                    ·
                      refine ⟨430911424811258371578109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36771108250560714374665301 430911424811258371578109)
                      ·
                        rfl

theorem cell23_839197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_839197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839197 prefixEnd_839197 := by exact prefixLift 839197
  have htrace : WordTrace (prefixWord ++ tailWord_839197) baseStart_839197 baseEnd_839197 := by
    simpa [prefixWord, tailWord_839197, baseEnd_839197] using wordTrace_append hprefix tailTrace_839197
  have hstable : (prefixWord ++ tailWord_839197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839197).length < 2 ^ (prefixWord ++ tailWord_839197).sum := by decide
  have hdescent : baseEnd_839197 < baseStart_839197 := by decide
  rcases family_descends (prefixWord ++ tailWord_839197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839221 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_839221 : Nat := 118140960795 + 839221 * 2 ^ 59
def prefixEnd_839221 : Nat := 4983230072969 + 3 ^ 40 * 839221 * 2
def baseEnd_839221 : Nat := 430923748346966277677999

theorem tailTrace_839221 : CollatzResearch.WordTrace tailWord_839221 prefixEnd_839221 430923748346966277677999 := by
  unfold tailWord_839221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608904492653119381021517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20405936328435412920681011 30608904492653119381021517)
  ·
    refine ⟨11478339184744919767883069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30608904492653119381021517 11478339184744919767883069)
    ·
      refine ⟨4304377194279344912956151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11478339184744919767883069 4304377194279344912956151)
      ·
        refine ⟨6456565791419017369434227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304377194279344912956151 6456565791419017369434227)
        ·
          refine ⟨9684848687128526054151341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456565791419017369434227 9684848687128526054151341)
          ·
            refine ⟨3631818257673197270306753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9684848687128526054151341 3631818257673197270306753)
            ·
              refine ⟨2723863693254897952730065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631818257673197270306753 2723863693254897952730065)
              ·
                refine ⟨2042897769941173464547549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723863693254897952730065 2042897769941173464547549)
                ·
                  refine ⟨766086663727940049205331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2042897769941173464547549 766086663727940049205331)
                  ·
                    refine ⟨1149129995591910073807997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766086663727940049205331 1149129995591910073807997)
                    ·
                      refine ⟨430923748346966277677999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149129995591910073807997 430923748346966277677999)
                      ·
                        rfl

theorem cell23_839221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_839221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839221 prefixEnd_839221 := by exact prefixLift 839221
  have htrace : WordTrace (prefixWord ++ tailWord_839221) baseStart_839221 baseEnd_839221 := by
    simpa [prefixWord, tailWord_839221, baseEnd_839221] using wordTrace_append hprefix tailTrace_839221
  have hstable : (prefixWord ++ tailWord_839221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839221).length < 2 ^ (prefixWord ++ tailWord_839221).sum := by decide
  have hdescent : baseEnd_839221 < baseStart_839221 := by decide
  rcases family_descends (prefixWord ++ tailWord_839221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839224 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 1, 5]
def baseStart_839224 : Nat := 118140960795 + 839224 * 2 ^ 59
def prefixEnd_839224 : Nat := 4983230072969 + 3 ^ 40 * 839224 * 2
def baseEnd_839224 : Nat := 143641762929643255313495

theorem tailTrace_839224 : CollatzResearch.WordTrace tailWord_839224 prefixEnd_839224 143641762929643255313495 := by
  unfold tailWord_839224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15304506955821125446690363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20406009274428167262253817 15304506955821125446690363)
  ·
    refine ⟨22956760433731688170035545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15304506955821125446690363 22956760433731688170035545)
    ·
      refine ⟨17217570325298766127526659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22956760433731688170035545 17217570325298766127526659)
      ·
        refine ⟨25826355487948149191289989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17217570325298766127526659 25826355487948149191289989)
        ·
          refine ⟨4842441653990277973366873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25826355487948149191289989 4842441653990277973366873)
          ·
            refine ⟨3631831240492708480025155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4842441653990277973366873 3631831240492708480025155)
            ·
              refine ⟨5447746860739062720037733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631831240492708480025155 5447746860739062720037733)
              ·
                refine ⟨1021452536388574260007075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5447746860739062720037733 1021452536388574260007075)
                ·
                  refine ⟨1532178804582861390010613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021452536388574260007075 1532178804582861390010613)
                  ·
                    refine ⟨143641762929643255313495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1532178804582861390010613 143641762929643255313495)
                    ·
                      rfl

theorem cell23_839224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_839224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839224 prefixEnd_839224 := by exact prefixLift 839224
  have htrace : WordTrace (prefixWord ++ tailWord_839224) baseStart_839224 baseEnd_839224 := by
    simpa [prefixWord, tailWord_839224, baseEnd_839224] using wordTrace_append hprefix tailTrace_839224
  have hstable : (prefixWord ++ tailWord_839224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839224).length < 2 ^ (prefixWord ++ tailWord_839224).sum := by decide
  have hdescent : baseEnd_839224 < baseStart_839224 := by decide
  rcases family_descends (prefixWord ++ tailWord_839224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839237 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_839237 : Nat := 118140960795 + 839237 * 2 ^ 59
def prefixEnd_839237 : Nat := 4983230072969 + 3 ^ 40 * 839237 * 2
def baseEnd_839237 : Nat := 143643988012479405025975

theorem tailTrace_839237 : CollatzResearch.WordTrace tailWord_839237 prefixEnd_839237 143643988012479405025975 := by
  unfold tailWord_839237
  simp only [CollatzResearch.WordTrace]
  refine ⟨30609488060595154113603965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406325373730102742402643 30609488060595154113603965)
  ·
    refine ⟨11478558022723182792601487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30609488060595154113603965 11478558022723182792601487)
    ·
      refine ⟨17217837034084774188902231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11478558022723182792601487 17217837034084774188902231)
      ·
        refine ⟨25826755551127161283353347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17217837034084774188902231 25826755551127161283353347)
        ·
          refine ⟨38740133326690741925030021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25826755551127161283353347 38740133326690741925030021)
          ·
            refine ⟨7263774998754514110943129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38740133326690741925030021 7263774998754514110943129)
            ·
              refine ⟨5447831249065885583207347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263774998754514110943129 5447831249065885583207347)
              ·
                refine ⟨8171746873598828374811021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447831249065885583207347 8171746873598828374811021)
                ·
                  refine ⟨3064405077599560640554133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8171746873598828374811021 3064405077599560640554133)
                  ·
                    refine ⟨143643988012479405025975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3064405077599560640554133 143643988012479405025975)
                    ·
                      rfl

theorem cell23_839237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_839237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839237 prefixEnd_839237 := by exact prefixLift 839237
  have htrace : WordTrace (prefixWord ++ tailWord_839237) baseStart_839237 baseEnd_839237 := by
    simpa [prefixWord, tailWord_839237, baseEnd_839237] using wordTrace_append hprefix tailTrace_839237
  have hstable : (prefixWord ++ tailWord_839237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839237).length < 2 ^ (prefixWord ++ tailWord_839237).sum := by decide
  have hdescent : baseEnd_839237 < baseStart_839237 := by decide
  rcases family_descends (prefixWord ++ tailWord_839237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839255 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_839255 : Nat := 118140960795 + 839255 * 2 ^ 59
def prefixEnd_839255 : Nat := 4983230072969 + 3 ^ 40 * 839255 * 2
def baseEnd_839255 : Nat := 430941206689219144652843

theorem tailTrace_839255 : CollatzResearch.WordTrace tailWord_839255 prefixEnd_839255 430941206689219144652843 := by
  unfold tailWord_839255
  simp only [CollatzResearch.WordTrace]
  refine ⟨30610144574529943187759219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406763049686628791839479 30610144574529943187759219)
  ·
    refine ⟨45915216861794914781638829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30610144574529943187759219 45915216861794914781638829)
    ·
      refine ⟨17218206323173093043114561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45915216861794914781638829 17218206323173093043114561)
      ·
        refine ⟨12913654742379819782335921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17218206323173093043114561 12913654742379819782335921)
        ·
          refine ⟨9685241056784864836751941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12913654742379819782335921 9685241056784864836751941)
          ·
            refine ⟨1815982698147162156890989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9685241056784864836751941 1815982698147162156890989)
            ·
              refine ⟨680993511805185808834121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815982698147162156890989 680993511805185808834121)
              ·
                refine ⟨510745133853889356625591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680993511805185808834121 510745133853889356625591)
                ·
                  refine ⟨766117700780834034938387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510745133853889356625591 766117700780834034938387)
                  ·
                    refine ⟨1149176551171251052407581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766117700780834034938387 1149176551171251052407581)
                    ·
                      refine ⟨430941206689219144652843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149176551171251052407581 430941206689219144652843)
                      ·
                        rfl

theorem cell23_839255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_839255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839255 prefixEnd_839255 := by exact prefixLift 839255
  have htrace : WordTrace (prefixWord ++ tailWord_839255) baseStart_839255 baseEnd_839255 := by
    simpa [prefixWord, tailWord_839255, baseEnd_839255] using wordTrace_append hprefix tailTrace_839255
  have hstable : (prefixWord ++ tailWord_839255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839255).length < 2 ^ (prefixWord ++ tailWord_839255).sum := by decide
  have hdescent : baseEnd_839255 < baseStart_839255 := by decide
  rcases family_descends (prefixWord ++ tailWord_839255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839264 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_839264 : Nat := 118140960795 + 839264 * 2 ^ 59
def prefixEnd_839264 : Nat := 4983230072969 + 3 ^ 40 * 839264 * 2
def baseEnd_839264 : Nat := 430945828015109609440301

theorem tailTrace_839264 : CollatzResearch.WordTrace tailWord_839264 prefixEnd_839264 430945828015109609440301 := by
  unfold tailWord_839264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305236415748668862418423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20406981887664891816557897 15305236415748668862418423)
  ·
    refine ⟨22957854623623003293627635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15305236415748668862418423 22957854623623003293627635)
    ·
      refine ⟨34436781935434504940441453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22957854623623003293627635 34436781935434504940441453)
      ·
        refine ⟨12913793225787939352665545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34436781935434504940441453 12913793225787939352665545)
        ·
          refine ⟨9685344919340954514499159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12913793225787939352665545 9685344919340954514499159)
          ·
            refine ⟨14528017379011431771748739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685344919340954514499159 14528017379011431771748739)
            ·
              refine ⟨21792026068517147657623109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14528017379011431771748739 21792026068517147657623109)
              ·
                refine ⟨4086004887846965185804333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21792026068517147657623109 4086004887846965185804333)
                ·
                  refine ⟨1532251832942611944676625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4086004887846965185804333 1532251832942611944676625)
                  ·
                    refine ⟨1149188874706958958507469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532251832942611944676625 1149188874706958958507469)
                    ·
                      refine ⟨430945828015109609440301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149188874706958958507469 430945828015109609440301)
                      ·
                        rfl

theorem cell23_839264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_839264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839264 prefixEnd_839264 := by exact prefixLift 839264
  have htrace : WordTrace (prefixWord ++ tailWord_839264) baseStart_839264 baseEnd_839264 := by
    simpa [prefixWord, tailWord_839264, baseEnd_839264] using wordTrace_append hprefix tailTrace_839264
  have hstable : (prefixWord ++ tailWord_839264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839264).length < 2 ^ (prefixWord ++ tailWord_839264).sum := by decide
  have hdescent : baseEnd_839264 < baseStart_839264 := by decide
  rcases family_descends (prefixWord ++ tailWord_839264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839267 : List Nat := [1, 1, 1, 5, 1, 3, 1, 10]
def baseStart_839267 : Nat := 118140960795 + 839267 * 2 ^ 59
def prefixEnd_839267 : Nat := 4983230072969 + 3 ^ 40 * 839267 * 2
def baseEnd_839267 : Nat := 15961013646558262877881

theorem tailTrace_839267 : CollatzResearch.WordTrace tailWord_839267 prefixEnd_839267 15961013646558262877881 := by
  unfold tailWord_839267
  simp only [CollatzResearch.WordTrace]
  refine ⟨30610582250486469237196055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20407054833657646158130703 30610582250486469237196055)
  ·
    refine ⟨45915873375729703855794083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30610582250486469237196055 45915873375729703855794083)
    ·
      refine ⟨68873810063594555783691125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45915873375729703855794083 68873810063594555783691125)
      ·
        refine ⟨6456919693461989604721043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68873810063594555783691125 6456919693461989604721043)
        ·
          refine ⟨9685379540192984407081565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456919693461989604721043 9685379540192984407081565)
          ·
            refine ⟨3632017327572369152655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9685379540192984407081565 3632017327572369152655587)
            ·
              refine ⟨5448025991358553728983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632017327572369152655587 5448025991358553728983381)
              ·
                refine ⟨15961013646558262877881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5448025991358553728983381 15961013646558262877881)
                ·
                  rfl

theorem cell23_839267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 10].length) (baseStart_839267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839267 prefixEnd_839267 := by exact prefixLift 839267
  have htrace : WordTrace (prefixWord ++ tailWord_839267) baseStart_839267 baseEnd_839267 := by
    simpa [prefixWord, tailWord_839267, baseEnd_839267] using wordTrace_append hprefix tailTrace_839267
  have hstable : (prefixWord ++ tailWord_839267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839267).length < 2 ^ (prefixWord ++ tailWord_839267).sum := by decide
  have hdescent : baseEnd_839267 < baseStart_839267 := by decide
  rcases family_descends (prefixWord ++ tailWord_839267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839274 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_839274 : Nat := 118140960795 + 839274 * 2 ^ 59
def prefixEnd_839274 : Nat := 4983230072969 + 3 ^ 40 * 839274 * 2
def baseEnd_839274 : Nat := 430950962821654570315255

theorem tailTrace_839274 : CollatzResearch.WordTrace tailWord_839274 prefixEnd_839274 430950962821654570315255 := by
  unfold tailWord_839274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652709390365277358175219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20407225040974072955133917 7652709390365277358175219)
  ·
    refine ⟨11479064085547916037262829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7652709390365277358175219 11479064085547916037262829)
    ·
      refine ⟨4304649032080468513973561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11479064085547916037262829 4304649032080468513973561)
      ·
        refine ⟨3228486774060351385480171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4304649032080468513973561 3228486774060351385480171)
        ·
          refine ⟨4842730161090527078220257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228486774060351385480171 4842730161090527078220257)
          ·
            refine ⟨3632047620817895308665193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4842730161090527078220257 3632047620817895308665193)
            ·
              refine ⟨2724035715613421481498895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632047620817895308665193 2724035715613421481498895)
              ·
                refine ⟨4086053573420132222248343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724035715613421481498895 4086053573420132222248343)
                ·
                  refine ⟨6129080360130198333372515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086053573420132222248343 6129080360130198333372515)
                  ·
                    refine ⟨9193620540195297500058773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6129080360130198333372515 9193620540195297500058773)
                    ·
                      refine ⟨430950962821654570315255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9193620540195297500058773 430950962821654570315255)
                      ·
                        rfl

theorem cell23_839274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_839274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839274 prefixEnd_839274 := by exact prefixLift 839274
  have htrace : WordTrace (prefixWord ++ tailWord_839274) baseStart_839274 baseEnd_839274 := by
    simpa [prefixWord, tailWord_839274, baseEnd_839274] using wordTrace_append hprefix tailTrace_839274
  have hstable : (prefixWord ++ tailWord_839274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839274).length < 2 ^ (prefixWord ++ tailWord_839274).sum := by decide
  have hdescent : baseEnd_839274 < baseStart_839274 := by decide
  rcases family_descends (prefixWord ++ tailWord_839274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839328 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_839328 : Nat := 118140960795 + 839328 * 2 ^ 59
def prefixEnd_839328 : Nat := 4983230072969 + 3 ^ 40 * 839328 * 2
def baseEnd_839328 : Nat := 430978690776997359040007

theorem tailTrace_839328 : CollatzResearch.WordTrace tailWord_839328 prefixEnd_839328 430978690776997359040007 := by
  unfold tailWord_839328
  simp only [CollatzResearch.WordTrace]
  refine ⟨15306403551632738327583319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20408538068843651103444425 15306403551632738327583319)
  ·
    refine ⟨22959605327449107491374979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15306403551632738327583319 22959605327449107491374979)
    ·
      refine ⟨34439407991173661237062469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22959605327449107491374979 34439407991173661237062469)
      ·
        refine ⟨6457388998345061481949213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34439407991173661237062469 6457388998345061481949213)
        ·
          refine ⟨2421520874379398055730955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6457388998345061481949213 2421520874379398055730955)
          ·
            refine ⟨3632281311569097083596433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421520874379398055730955 3632281311569097083596433)
            ·
              refine ⟨2724210983676822812697325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632281311569097083596433 2724210983676822812697325)
              ·
                refine ⟨1021579118878808554761497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724210983676822812697325 1021579118878808554761497)
                ·
                  refine ⟨766184339159106416071123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021579118878808554761497 766184339159106416071123)
                  ·
                    refine ⟨1149276508738659624106685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766184339159106416071123 1149276508738659624106685)
                    ·
                      refine ⟨430978690776997359040007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149276508738659624106685 430978690776997359040007)
                      ·
                        rfl

theorem cell23_839328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_839328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839328 prefixEnd_839328 := by exact prefixLift 839328
  have htrace : WordTrace (prefixWord ++ tailWord_839328) baseStart_839328 baseEnd_839328 := by
    simpa [prefixWord, tailWord_839328, baseEnd_839328] using wordTrace_append hprefix tailTrace_839328
  have hstable : (prefixWord ++ tailWord_839328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839328).length < 2 ^ (prefixWord ++ tailWord_839328).sum := by decide
  have hdescent : baseEnd_839328 < baseStart_839328 := by decide
  rcases family_descends (prefixWord ++ tailWord_839328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839368 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_839368 : Nat := 118140960795 + 839368 * 2 ^ 59
def prefixEnd_839368 : Nat := 4983230072969 + 3 ^ 40 * 839368 * 2
def baseEnd_839368 : Nat := 430999230003177202539823

theorem tailTrace_839368 : CollatzResearch.WordTrace tailWord_839368 prefixEnd_839368 430999230003177202539823 := by
  unfold tailWord_839368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307133011560281743311379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20409510682080375657748505 15307133011560281743311379)
  ·
    refine ⟨22960699517340422614967069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15307133011560281743311379 22960699517340422614967069)
    ·
      refine ⟨8610262319002658480612651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22960699517340422614967069 8610262319002658480612651)
      ·
        refine ⟨12915393478503987720918977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610262319002658480612651 12915393478503987720918977)
        ·
          refine ⟨9686545108877990790689233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915393478503987720918977 9686545108877990790689233)
          ·
            refine ⟨7264908831658493093016925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9686545108877990790689233 7264908831658493093016925)
            ·
              refine ⟨2724340811871934909881347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7264908831658493093016925 2724340811871934909881347)
              ·
                refine ⟨4086511217807902364822021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724340811871934909881347 4086511217807902364822021)
                ·
                  refine ⟨766220853338981693404129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4086511217807902364822021 766220853338981693404129)
                  ·
                    refine ⟨574665640004236270053097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766220853338981693404129 574665640004236270053097)
                    ·
                      refine ⟨430999230003177202539823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574665640004236270053097 430999230003177202539823)
                      ·
                        rfl

theorem cell23_839368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_839368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839368 prefixEnd_839368 := by exact prefixLift 839368
  have htrace : WordTrace (prefixWord ++ tailWord_839368) baseStart_839368 baseEnd_839368 := by
    simpa [prefixWord, tailWord_839368, baseEnd_839368] using wordTrace_append hprefix tailTrace_839368
  have hstable : (prefixWord ++ tailWord_839368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839368).length < 2 ^ (prefixWord ++ tailWord_839368).sum := by decide
  have hdescent : baseEnd_839368 < baseStart_839368 := by decide
  rcases family_descends (prefixWord ++ tailWord_839368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839404 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_839404 : Nat := 118140960795 + 839404 * 2 ^ 59
def prefixEnd_839404 : Nat := 4983230072969 + 3 ^ 40 * 839404 * 2
def baseEnd_839404 : Nat := 143672571768913020563219

theorem tailTrace_839404 : CollatzResearch.WordTrace tailWord_839404 prefixEnd_839404 143672571768913020563219 := by
  unfold tailWord_839404
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307789525495070817466633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20410386033993427756622177 15307789525495070817466633)
  ·
    refine ⟨11480842144121303113099975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15307789525495070817466633 11480842144121303113099975)
    ·
      refine ⟨17221263216181954669649963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11480842144121303113099975 17221263216181954669649963)
      ·
        refine ⟨25831894824272932004474945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17221263216181954669649963 25831894824272932004474945)
        ·
          refine ⟨19373921118204699003356209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25831894824272932004474945 19373921118204699003356209)
          ·
            refine ⟨14530440838653524252517157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19373921118204699003356209 14530440838653524252517157)
            ·
              refine ⟨2724457657247535797346967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14530440838653524252517157 2724457657247535797346967)
              ·
                refine ⟨4086686485871303696020451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724457657247535797346967 4086686485871303696020451)
                ·
                  refine ⟨6130029728806955544030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086686485871303696020451 6130029728806955544030677)
                  ·
                    refine ⟨143672571768913020563219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6130029728806955544030677 143672571768913020563219)
                    ·
                      rfl

theorem cell23_839404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_839404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839404 prefixEnd_839404 := by exact prefixLift 839404
  have htrace : WordTrace (prefixWord ++ tailWord_839404) baseStart_839404 baseEnd_839404 := by
    simpa [prefixWord, tailWord_839404, baseEnd_839404] using wordTrace_append hprefix tailTrace_839404
  have hstable : (prefixWord ++ tailWord_839404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839404).length < 2 ^ (prefixWord ++ tailWord_839404).sum := by decide
  have hdescent : baseEnd_839404 < baseStart_839404 := by decide
  rcases family_descends (prefixWord ++ tailWord_839404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839430 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_839430 : Nat := 118140960795 + 839430 * 2 ^ 59
def prefixEnd_839430 : Nat := 4983230072969 + 3 ^ 40 * 839430 * 2
def baseEnd_839430 : Nat := 431031065803755959964539

theorem tailTrace_839430 : CollatzResearch.WordTrace tailWord_839430 prefixEnd_839430 431031065803755959964539 := by
  unfold tailWord_839430
  simp only [CollatzResearch.WordTrace]
  refine ⟨956766479652998377355617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20411018232597298716919829 956766479652998377355617)
  ·
    refine ⟨717574859739748783016713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 956766479652998377355617 717574859739748783016713)
    ·
      refine ⟨538181144804811587262535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717574859739748783016713 538181144804811587262535)
      ·
        refine ⟨807271717207217380893803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538181144804811587262535 807271717207217380893803)
        ·
          refine ⟨1210907575810826071340705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807271717207217380893803 1210907575810826071340705)
          ·
            refine ⟨908180681858119553505529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210907575810826071340705 908180681858119553505529)
            ·
              refine ⟨681135511393589665129147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908180681858119553505529 681135511393589665129147)
              ·
                refine ⟨1021703267090384497693721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681135511393589665129147 1021703267090384497693721)
                ·
                  refine ⟨766277450317788373270291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021703267090384497693721 766277450317788373270291)
                  ·
                    refine ⟨1149416175476682559905437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766277450317788373270291 1149416175476682559905437)
                    ·
                      refine ⟨431031065803755959964539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149416175476682559905437 431031065803755959964539)
                      ·
                        rfl

theorem cell23_839430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_839430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839430 prefixEnd_839430 := by exact prefixLift 839430
  have htrace : WordTrace (prefixWord ++ tailWord_839430) baseStart_839430 baseEnd_839430 := by
    simpa [prefixWord, tailWord_839430, baseEnd_839430] using wordTrace_append hprefix tailTrace_839430
  have hstable : (prefixWord ++ tailWord_839430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839430).length < 2 ^ (prefixWord ++ tailWord_839430).sum := by decide
  have hdescent : baseEnd_839430 < baseStart_839430 := by decide
  rcases family_descends (prefixWord ++ tailWord_839430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839441 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_839441 : Nat := 118140960795 + 839441 * 2 ^ 59
def prefixEnd_839441 : Nat := 4983230072969 + 3 ^ 40 * 839441 * 2
def baseEnd_839441 : Nat := 431036714090955416926987

theorem tailTrace_839441 : CollatzResearch.WordTrace tailWord_839441 prefixEnd_839441 431036714090955416926987 := by
  unfold tailWord_839441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30616928551856096954030177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20411285701237397969353451 30616928551856096954030177)
  ·
    refine ⟨22962696413892072715522633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30616928551856096954030177 22962696413892072715522633)
    ·
      refine ⟨17222022310419054536641975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22962696413892072715522633 17222022310419054536641975)
      ·
        refine ⟨25833033465628581804962963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17222022310419054536641975 25833033465628581804962963)
        ·
          refine ⟨38749550198442872707444445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25833033465628581804962963 38749550198442872707444445)
          ·
            refine ⟨14531081324416077265291667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38749550198442872707444445 14531081324416077265291667)
            ·
              refine ⟨21796621986624115897937501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14531081324416077265291667 21796621986624115897937501)
              ·
                refine ⟨8173733244984043461726563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21796621986624115897937501 8173733244984043461726563)
                ·
                  refine ⟨12260599867476065192589845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173733244984043461726563 12260599867476065192589845)
                  ·
                    refine ⟨574715618787940555902649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12260599867476065192589845 574715618787940555902649)
                    ·
                      refine ⟨431036714090955416926987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574715618787940555902649 431036714090955416926987)
                      ·
                        rfl

theorem cell23_839441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_839441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839441 prefixEnd_839441 := by exact prefixLift 839441
  have htrace : WordTrace (prefixWord ++ tailWord_839441) baseStart_839441 baseEnd_839441 := by
    simpa [prefixWord, tailWord_839441, baseEnd_839441] using wordTrace_append hprefix tailTrace_839441
  have hstable : (prefixWord ++ tailWord_839441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839441).length < 2 ^ (prefixWord ++ tailWord_839441).sum := by decide
  have hdescent : baseEnd_839441 < baseStart_839441 := by decide
  rcases family_descends (prefixWord ++ tailWord_839441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839458 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_839458 : Nat := 118140960795 + 839458 * 2 ^ 59
def prefixEnd_839458 : Nat := 4983230072969 + 3 ^ 40 * 839458 * 2
def baseEnd_839458 : Nat := 431045443262081850414409

theorem tailTrace_839458 : CollatzResearch.WordTrace tailWord_839458 prefixEnd_839458 431045443262081850414409 := by
  unfold tailWord_839458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654387148198627214349757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20411699061863005904932685 7654387148198627214349757)
  ·
    refine ⟨2870395180574485205381159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7654387148198627214349757 2870395180574485205381159)
    ·
      refine ⟨4305592770861727808071739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870395180574485205381159 4305592770861727808071739)
      ·
        refine ⟨6458389156292591712107609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305592770861727808071739 6458389156292591712107609)
        ·
          refine ⟨4843791867219443784080707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6458389156292591712107609 4843791867219443784080707)
          ·
            refine ⟨7265687800829165676121061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843791867219443784080707 7265687800829165676121061)
            ·
              refine ⟨1362316462655468564272699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7265687800829165676121061 1362316462655468564272699)
              ·
                refine ⟨2043474693983202846409049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362316462655468564272699 2043474693983202846409049)
                ·
                  refine ⟨1532606020487402134806787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2043474693983202846409049 1532606020487402134806787)
                  ·
                    refine ⟨2298909030731103202210181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1532606020487402134806787 2298909030731103202210181)
                    ·
                      refine ⟨431045443262081850414409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2298909030731103202210181 431045443262081850414409)
                      ·
                        rfl

theorem cell23_839458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_839458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839458 prefixEnd_839458 := by exact prefixLift 839458
  have htrace : WordTrace (prefixWord ++ tailWord_839458) baseStart_839458 baseEnd_839458 := by
    simpa [prefixWord, tailWord_839458, baseEnd_839458] using wordTrace_append hprefix tailTrace_839458
  have hstable : (prefixWord ++ tailWord_839458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839458).length < 2 ^ (prefixWord ++ tailWord_839458).sum := by decide
  have hdescent : baseEnd_839458 < baseStart_839458 := by decide
  rcases family_descends (prefixWord ++ tailWord_839458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839504 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_839504 : Nat := 118140960795 + 839504 * 2 ^ 59
def prefixEnd_839504 : Nat := 4983230072969 + 3 ^ 40 * 839504 * 2
def baseEnd_839504 : Nat := 431069063372188670439197

theorem tailTrace_839504 : CollatzResearch.WordTrace tailWord_839504 prefixEnd_839504 431069063372188670439197 := by
  unfold tailWord_839504
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309613175313929356786783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20412817567085239142382377 15309613175313929356786783)
  ·
    refine ⟨22964419762970894035180175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15309613175313929356786783 22964419762970894035180175)
    ·
      refine ⟨34446629644456341052770263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22964419762970894035180175 34446629644456341052770263)
      ·
        refine ⟨51669944466684511579155395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34446629644456341052770263 51669944466684511579155395)
        ·
          refine ⟨77504916700026767368733093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51669944466684511579155395 77504916700026767368733093)
          ·
            refine ⟨14532171881255018881637455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77504916700026767368733093 14532171881255018881637455)
            ·
              refine ⟨21798257821882528322456183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532171881255018881637455 21798257821882528322456183)
              ·
                refine ⟨32697386732823792483684275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21798257821882528322456183 32697386732823792483684275)
                ·
                  refine ⟨49046080099235688725526413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32697386732823792483684275 49046080099235688725526413)
                  ·
                    refine ⟨18392280037213383272072405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49046080099235688725526413 18392280037213383272072405)
                    ·
                      refine ⟨431069063372188670439197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18392280037213383272072405 431069063372188670439197)
                      ·
                        rfl

theorem cell23_839504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_839504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839504 prefixEnd_839504 := by exact prefixLift 839504
  have htrace : WordTrace (prefixWord ++ tailWord_839504) baseStart_839504 baseEnd_839504 := by
    simpa [prefixWord, tailWord_839504, baseEnd_839504] using wordTrace_append hprefix tailTrace_839504
  have hstable : (prefixWord ++ tailWord_839504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839504).length < 2 ^ (prefixWord ++ tailWord_839504).sum := by decide
  have hdescent : baseEnd_839504 < baseStart_839504 := by decide
  rcases family_descends (prefixWord ++ tailWord_839504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839528 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 1, 5]
def baseStart_839528 : Nat := 118140960795 + 839528 * 2 ^ 59
def prefixEnd_839528 : Nat := 4983230072969 + 3 ^ 40 * 839528 * 2
def baseEnd_839528 : Nat := 143693795635965525513029

theorem tailTrace_839528 : CollatzResearch.WordTrace tailWord_839528 prefixEnd_839528 143693795635965525513029 := by
  unfold tailWord_839528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310050851270455406223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20413401135027273874964825 15310050851270455406223619)
  ·
    refine ⟨22965076276905683109335429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310050851270455406223619 22965076276905683109335429)
    ·
      refine ⟨4305951801919815583000393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22965076276905683109335429 4305951801919815583000393)
      ·
        refine ⟨3229463851439861687250295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4305951801919815583000393 3229463851439861687250295)
        ·
          refine ⟨4844195777159792530875443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229463851439861687250295 4844195777159792530875443)
          ·
            refine ⟨7266293665739688796313165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844195777159792530875443 7266293665739688796313165)
            ·
              refine ⟨2724860124652383298617437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7266293665739688796313165 2724860124652383298617437)
              ·
                refine ⟨1021822546744643736981539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2724860124652383298617437 1021822546744643736981539)
                ·
                  refine ⟨1532733820116965605472309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021822546744643736981539 1532733820116965605472309)
                  ·
                    refine ⟨143693795635965525513029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1532733820116965605472309 143693795635965525513029)
                    ·
                      rfl

theorem cell23_839528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_839528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839528 prefixEnd_839528 := by exact prefixLift 839528
  have htrace : WordTrace (prefixWord ++ tailWord_839528) baseStart_839528 baseEnd_839528 := by
    simpa [prefixWord, tailWord_839528, baseEnd_839528] using wordTrace_append hprefix tailTrace_839528
  have hstable : (prefixWord ++ tailWord_839528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839528).length < 2 ^ (prefixWord ++ tailWord_839528).sum := by decide
  have hdescent : baseEnd_839528 < baseStart_839528 := by decide
  rcases family_descends (prefixWord ++ tailWord_839528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839561 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_839561 : Nat := 118140960795 + 839561 * 2 ^ 59
def prefixEnd_839561 : Nat := 4983230072969 + 3 ^ 40 * 839561 * 2
def baseEnd_839561 : Nat := 431098331769494947426435

theorem tailTrace_839561 : CollatzResearch.WordTrace tailWord_839561 prefixEnd_839561 431098331769494947426435 := by
  unfold tailWord_839561
  simp only [CollatzResearch.WordTrace]
  refine ⟨30621305311421357448398537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20414203540947571632265691 30621305311421357448398537)
  ·
    refine ⟨22965978983566018086298903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30621305311421357448398537 22965978983566018086298903)
    ·
      refine ⟨34448968475349027129448355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965978983566018086298903 34448968475349027129448355)
      ·
        refine ⟨51673452713023540694172533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34448968475349027129448355 51673452713023540694172533)
        ·
          refine ⟨4844386191845956940078675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51673452713023540694172533 4844386191845956940078675)
          ·
            refine ⟨7266579287768935410118013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844386191845956940078675 7266579287768935410118013)
            ·
              refine ⟨2724967232913350778794255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7266579287768935410118013 2724967232913350778794255)
              ·
                refine ⟨4087450849370026168191383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724967232913350778794255 4087450849370026168191383)
                ·
                  refine ⟨6131176274055039252287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087450849370026168191383 6131176274055039252287075)
                  ·
                    refine ⟨9196764411082558878430613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6131176274055039252287075 9196764411082558878430613)
                    ·
                      refine ⟨431098331769494947426435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9196764411082558878430613 431098331769494947426435)
                      ·
                        rfl

theorem cell23_839561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_839561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839561 prefixEnd_839561 := by exact prefixLift 839561
  have htrace : WordTrace (prefixWord ++ tailWord_839561) baseStart_839561 baseEnd_839561 := by
    simpa [prefixWord, tailWord_839561, baseEnd_839561] using wordTrace_append hprefix tailTrace_839561
  have hstable : (prefixWord ++ tailWord_839561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839561).length < 2 ^ (prefixWord ++ tailWord_839561).sum := by decide
  have hdescent : baseEnd_839561 < baseStart_839561 := by decide
  rcases family_descends (prefixWord ++ tailWord_839561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839568 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_839568 : Nat := 118140960795 + 839568 * 2 ^ 59
def prefixEnd_839568 : Nat := 4983230072969 + 3 ^ 40 * 839568 * 2
def baseEnd_839568 : Nat := 431101926134076420038903

theorem tailTrace_839568 : CollatzResearch.WordTrace tailWord_839568 prefixEnd_839568 431101926134076420038903 := by
  unfold tailWord_839568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310780311197998821951679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20414373748263998429268905 15310780311197998821951679)
  ·
    refine ⟨22966170466796998232927519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310780311197998821951679 22966170466796998232927519)
    ·
      refine ⟨34449255700195497349391279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22966170466796998232927519 34449255700195497349391279)
      ·
        refine ⟨51673883550293246024086919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34449255700195497349391279 51673883550293246024086919)
        ·
          refine ⟨77510825325439869036130379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51673883550293246024086919 77510825325439869036130379)
          ·
            refine ⟨116266237988159803554195569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77510825325439869036130379 116266237988159803554195569)
            ·
              refine ⟨87199678491119852665646677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116266237988159803554195569 87199678491119852665646677)
              ·
                refine ⟨1021871232317810773425547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87199678491119852665646677 1021871232317810773425547)
                ·
                  refine ⟨1532806848476716160138321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021871232317810773425547 1532806848476716160138321)
                  ·
                    refine ⟨1149605136357537120103741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1532806848476716160138321 1149605136357537120103741)
                    ·
                      refine ⟨431101926134076420038903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149605136357537120103741 431101926134076420038903)
                      ·
                        rfl

theorem cell23_839568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_839568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839568 prefixEnd_839568 := by exact prefixLift 839568
  have htrace : WordTrace (prefixWord ++ tailWord_839568) baseStart_839568 baseEnd_839568 := by
    simpa [prefixWord, tailWord_839568, baseEnd_839568] using wordTrace_append hprefix tailTrace_839568
  have hstable : (prefixWord ++ tailWord_839568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839568).length < 2 ^ (prefixWord ++ tailWord_839568).sum := by decide
  have hdescent : baseEnd_839568 < baseStart_839568 := by decide
  rcases family_descends (prefixWord ++ tailWord_839568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839576 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_839576 : Nat := 118140960795 + 839576 * 2 ^ 59
def prefixEnd_839576 : Nat := 4983230072969 + 3 ^ 40 * 839576 * 2
def baseEnd_839576 : Nat := 431106033979312388738867

theorem tailTrace_839576 : CollatzResearch.WordTrace tailWord_839576 prefixEnd_839576 431106033979312388738867 := by
  unfold tailWord_839576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310926203183507505097291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20414568270911343340129721 15310926203183507505097291)
  ·
    refine ⟨22966389304775261257645937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310926203183507505097291 22966389304775261257645937)
    ·
      refine ⟨17224791978581445943234453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22966389304775261257645937 17224791978581445943234453)
      ·
        refine ⟨807412123996005278589115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17224791978581445943234453 807412123996005278589115)
        ·
          refine ⟨1211118185994007917883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807412123996005278589115 1211118185994007917883673)
          ·
            refine ⟨908338639495505938412755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211118185994007917883673 908338639495505938412755)
            ·
              refine ⟨1362507959243258907619133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908338639495505938412755 1362507959243258907619133)
              ·
                refine ⟨510940484716222090357175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362507959243258907619133 510940484716222090357175)
                ·
                  refine ⟨766410727074333135535763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510940484716222090357175 766410727074333135535763)
                  ·
                    refine ⟨1149616090611499703303645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766410727074333135535763 1149616090611499703303645)
                    ·
                      refine ⟨431106033979312388738867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149616090611499703303645 431106033979312388738867)
                      ·
                        rfl

theorem cell23_839576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_839576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839576 prefixEnd_839576 := by exact prefixLift 839576
  have htrace : WordTrace (prefixWord ++ tailWord_839576) baseStart_839576 baseEnd_839576 := by
    simpa [prefixWord, tailWord_839576, baseEnd_839576] using wordTrace_append hprefix tailTrace_839576
  have hstable : (prefixWord ++ tailWord_839576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839576).length < 2 ^ (prefixWord ++ tailWord_839576).sum := by decide
  have hdescent : baseEnd_839576 < baseStart_839576 := by decide
  rcases family_descends (prefixWord ++ tailWord_839576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839585 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_839585 : Nat := 118140960795 + 839585 * 2 ^ 59
def prefixEnd_839585 : Nat := 4983230072969 + 3 ^ 40 * 839585 * 2
def baseEnd_839585 : Nat := 431110655305202853526325

theorem tailTrace_839585 : CollatzResearch.WordTrace tailWord_839585 prefixEnd_839585 431110655305202853526325 := by
  unfold tailWord_839585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30622180663334409547272209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20414787108889606364848139 30622180663334409547272209)
  ·
    refine ⟨22966635497500807160454157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30622180663334409547272209 22966635497500807160454157)
    ·
      refine ⟨8612488311562802685170309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22966635497500807160454157 8612488311562802685170309)
      ·
        refine ⟨1614841558418025503469433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8612488311562802685170309 1614841558418025503469433)
        ·
          refine ⟨1211131168813519127602075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614841558418025503469433 1211131168813519127602075)
          ·
            refine ⟨1816696753220278691403113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211131168813519127602075 1816696753220278691403113)
            ·
              refine ⟨1362522564915209018552335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816696753220278691403113 1362522564915209018552335)
              ·
                refine ⟨2043783847372813527828503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362522564915209018552335 2043783847372813527828503)
                ·
                  refine ⟨3065675771059220291742755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043783847372813527828503 3065675771059220291742755)
                  ·
                    refine ⟨4598513656588830437614133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3065675771059220291742755 4598513656588830437614133)
                    ·
                      refine ⟨431110655305202853526325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4598513656588830437614133 431110655305202853526325)
                      ·
                        rfl

theorem cell23_839585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_839585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839585 prefixEnd_839585 := by exact prefixLift 839585
  have htrace : WordTrace (prefixWord ++ tailWord_839585) baseStart_839585 baseEnd_839585 := by
    simpa [prefixWord, tailWord_839585, baseEnd_839585] using wordTrace_append hprefix tailTrace_839585
  have hstable : (prefixWord ++ tailWord_839585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839585).length < 2 ^ (prefixWord ++ tailWord_839585).sum := by decide
  have hdescent : baseEnd_839585 < baseStart_839585 := by decide
  rcases family_descends (prefixWord ++ tailWord_839585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839599 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 1, 2, 2]
def baseStart_839599 : Nat := 118140960795 + 839599 * 2 ^ 59
def prefixEnd_839599 : Nat := 4983230072969 + 3 ^ 40 * 839599 * 2
def baseEnd_839599 : Nat := 431117844034365798751261

theorem tailTrace_839599 : CollatzResearch.WordTrace tailWord_839599 prefixEnd_839599 431117844034365798751261 := by
  unfold tailWord_839599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30622691285283689938281851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415127523522459958854567 30622691285283689938281851)
  ·
    refine ⟨45934036927925534907422777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30622691285283689938281851 45934036927925534907422777)
    ·
      refine ⟨34450527695944151180567083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45934036927925534907422777 34450527695944151180567083)
      ·
        refine ⟨51675791543916226770850625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34450527695944151180567083 51675791543916226770850625)
        ·
          refine ⟨38756843657937170078137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51675791543916226770850625 38756843657937170078137969)
          ·
            refine ⟨29067632743452877558603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38756843657937170078137969 29067632743452877558603477)
            ·
              refine ⟨681272642424676817779769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29067632743452877558603477 681272642424676817779769)
              ·
                refine ⟨510954481818507613334827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681272642424676817779769 510954481818507613334827)
                ·
                  refine ⟨766431722727761420002241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510954481818507613334827 766431722727761420002241)
                  ·
                    refine ⟨574823792045821065001681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766431722727761420002241 574823792045821065001681)
                    ·
                      refine ⟨431117844034365798751261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574823792045821065001681 431117844034365798751261)
                      ·
                        rfl

theorem cell23_839599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 2, 2].length) (baseStart_839599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839599 prefixEnd_839599 := by exact prefixLift 839599
  have htrace : WordTrace (prefixWord ++ tailWord_839599) baseStart_839599 baseEnd_839599 := by
    simpa [prefixWord, tailWord_839599, baseEnd_839599] using wordTrace_append hprefix tailTrace_839599
  have hstable : (prefixWord ++ tailWord_839599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839599).length < 2 ^ (prefixWord ++ tailWord_839599).sum := by decide
  have hdescent : baseEnd_839599 < baseStart_839599 := by decide
  rcases family_descends (prefixWord ++ tailWord_839599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839615 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_839615 : Nat := 118140960795 + 839615 * 2 ^ 59
def prefixEnd_839615 : Nat := 4983230072969 + 3 ^ 40 * 839615 * 2
def baseEnd_839615 : Nat := 431126059724837736151187

theorem tailTrace_839615 : CollatzResearch.WordTrace tailWord_839615 prefixEnd_839615 431126059724837736151187 := by
  unfold tailWord_839615
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623274853225724670864299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415516568817149780576199 30623274853225724670864299)
  ·
    refine ⟨45934912279838587006296449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623274853225724670864299 45934912279838587006296449)
    ·
      refine ⟨34451184209878940254722337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45934912279838587006296449 34451184209878940254722337)
      ·
        refine ⟨25838388157409205191041753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34451184209878940254722337 25838388157409205191041753)
        ·
          refine ⟨19378791118056903893281315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25838388157409205191041753 19378791118056903893281315)
          ·
            refine ⟨29068186677085355839921973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378791118056903893281315 29068186677085355839921973)
            ·
              refine ⟨2725142500976752109992685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29068186677085355839921973 2725142500976752109992685)
              ·
                refine ⟨1021928437866282041247257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725142500976752109992685 1021928437866282041247257)
                ·
                  refine ⟨766446328399711530935443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021928437866282041247257 766446328399711530935443)
                  ·
                    refine ⟨1149669492599567296403165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766446328399711530935443 1149669492599567296403165)
                    ·
                      refine ⟨431126059724837736151187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149669492599567296403165 431126059724837736151187)
                      ·
                        rfl

theorem cell23_839615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_839615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839615 prefixEnd_839615 := by exact prefixLift 839615
  have htrace : WordTrace (prefixWord ++ tailWord_839615) baseStart_839615 baseEnd_839615 := by
    simpa [prefixWord, tailWord_839615, baseEnd_839615] using wordTrace_append hprefix tailTrace_839615
  have hstable : (prefixWord ++ tailWord_839615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839615).length < 2 ^ (prefixWord ++ tailWord_839615).sum := by decide
  have hdescent : baseEnd_839615 < baseStart_839615 := by decide
  rcases family_descends (prefixWord ++ tailWord_839615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839621 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_839621 : Nat := 118140960795 + 839621 * 2 ^ 59
def prefixEnd_839621 : Nat := 4983230072969 + 3 ^ 40 * 839621 * 2
def baseEnd_839621 : Nat := 431129140608764712676159

theorem tailTrace_839621 : CollatzResearch.WordTrace tailWord_839621 prefixEnd_839621 431129140608764712676159 := by
  unfold tailWord_839621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623493691203987695582717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415662460802658463721811 30623493691203987695582717)
  ·
    refine ⟨11483810134201495385843519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30623493691203987695582717 11483810134201495385843519)
    ·
      refine ⟨17225715201302243078765279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11483810134201495385843519 17225715201302243078765279)
      ·
        refine ⟨25838572801953364618147919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17225715201302243078765279 25838572801953364618147919)
        ·
          refine ⟨38757859202930046927221879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25838572801953364618147919 38757859202930046927221879)
          ·
            refine ⟨58136788804395070390832819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38757859202930046927221879 58136788804395070390832819)
            ·
              refine ⟨87205183206592605586249229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58136788804395070390832819 87205183206592605586249229)
              ·
                refine ⟨32701943702472227094843461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87205183206592605586249229 32701943702472227094843461)
                ·
                  refine ⟨6131614444213542580283149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32701943702472227094843461 6131614444213542580283149)
                  ·
                    refine ⟨2299355416580078467606181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6131614444213542580283149 2299355416580078467606181)
                    ·
                      refine ⟨431129140608764712676159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2299355416580078467606181 431129140608764712676159)
                      ·
                        rfl

theorem cell23_839621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_839621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839621 prefixEnd_839621 := by exact prefixLift 839621
  have htrace : WordTrace (prefixWord ++ tailWord_839621) baseStart_839621 baseEnd_839621 := by
    simpa [prefixWord, tailWord_839621, baseEnd_839621] using wordTrace_append hprefix tailTrace_839621
  have hstable : (prefixWord ++ tailWord_839621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839621).length < 2 ^ (prefixWord ++ tailWord_839621).sum := by decide
  have hdescent : baseEnd_839621 < baseStart_839621 := by decide
  rcases family_descends (prefixWord ++ tailWord_839621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839650 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_839650 : Nat := 118140960795 + 839650 * 2 ^ 59
def prefixEnd_839650 : Nat := 4983230072969 + 3 ^ 40 * 839650 * 2
def baseEnd_839650 : Nat := 431144031547745099213527

theorem tailTrace_839650 : CollatzResearch.WordTrace tailWord_839650 prefixEnd_839650 431144031547745099213527 := by
  unfold tailWord_839650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656137852024731412097101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20416367605399283765592269 7656137852024731412097101)
  ·
    refine ⟨2871051694509274279536413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7656137852024731412097101 2871051694509274279536413)
    ·
      refine ⟨1076644385440977854826155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2871051694509274279536413 1076644385440977854826155)
      ·
        refine ⟨1614966578161466782239233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076644385440977854826155 1614966578161466782239233)
        ·
          refine ⟨1211224933621100086679425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614966578161466782239233 1211224933621100086679425)
          ·
            refine ⟨908418700215825065009569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211224933621100086679425 908418700215825065009569)
            ·
              refine ⟨681314025161868798757177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908418700215825065009569 681314025161868798757177)
              ·
                refine ⟨510985518871401599067883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681314025161868798757177 510985518871401599067883)
                ·
                  refine ⟨766478278307102398601825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510985518871401599067883 766478278307102398601825)
                  ·
                    refine ⟨574858708730326798951369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766478278307102398601825 574858708730326798951369)
                    ·
                      refine ⟨431144031547745099213527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574858708730326798951369 431144031547745099213527)
                      ·
                        rfl

theorem cell23_839650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_839650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839650 prefixEnd_839650 := by exact prefixLift 839650
  have htrace : WordTrace (prefixWord ++ tailWord_839650) baseStart_839650 baseEnd_839650 := by
    simpa [prefixWord, tailWord_839650, baseEnd_839650] using wordTrace_append hprefix tailTrace_839650
  have hstable : (prefixWord ++ tailWord_839650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839650).length < 2 ^ (prefixWord ++ tailWord_839650).sum := by decide
  have hdescent : baseEnd_839650 < baseStart_839650 := by decide
  rcases family_descends (prefixWord ++ tailWord_839650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839658 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_839658 : Nat := 118140960795 + 839658 * 2 ^ 59
def prefixEnd_839658 : Nat := 4983230072969 + 3 ^ 40 * 839658 * 2
def baseEnd_839658 : Nat := 431148139392981067913489

theorem tailTrace_839658 : CollatzResearch.WordTrace tailWord_839658 prefixEnd_839658 431148139392981067913489 := by
  unfold tailWord_839658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656210798017485753669907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20416562128046628676453085 7656210798017485753669907)
  ·
    refine ⟨11484316197026228630504861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7656210798017485753669907 11484316197026228630504861)
    ·
      refine ⟨4306618573884835736439323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11484316197026228630504861 4306618573884835736439323)
      ·
        refine ⟨6459927860827253604658985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306618573884835736439323 6459927860827253604658985)
        ·
          refine ⟨4844945895620440203494239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6459927860827253604658985 4844945895620440203494239)
          ·
            refine ⟨7267418843430660305241359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844945895620440203494239 7267418843430660305241359)
            ·
              refine ⟨10901128265145990457862039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267418843430660305241359 10901128265145990457862039)
              ·
                refine ⟨16351692397718985686793059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10901128265145990457862039 16351692397718985686793059)
                ·
                  refine ⟨24527538596578478530189589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16351692397718985686793059 24527538596578478530189589)
                  ·
                    refine ⟨1149728371714616181102637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24527538596578478530189589 1149728371714616181102637)
                    ·
                      refine ⟨431148139392981067913489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149728371714616181102637 431148139392981067913489)
                      ·
                        rfl

theorem cell23_839658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_839658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839658 prefixEnd_839658 := by exact prefixLift 839658
  have htrace : WordTrace (prefixWord ++ tailWord_839658) baseStart_839658 baseEnd_839658 := by
    simpa [prefixWord, tailWord_839658, baseEnd_839658] using wordTrace_append hprefix tailTrace_839658
  have hstable : (prefixWord ++ tailWord_839658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839658).length < 2 ^ (prefixWord ++ tailWord_839658).sum := by decide
  have hdescent : baseEnd_839658 < baseStart_839658 := by decide
  rcases family_descends (prefixWord ++ tailWord_839658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839672 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_839672 : Nat := 118140960795 + 839672 * 2 ^ 59
def prefixEnd_839672 : Nat := 4983230072969 + 3 ^ 40 * 839672 * 2
def baseEnd_839672 : Nat := 431155328122144013138425

theorem tailTrace_839672 : CollatzResearch.WordTrace tailWord_839672 prefixEnd_839672 431155328122144013138425 := by
  unfold tailWord_839672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15312676907009611702844635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20416902542679482270459513 15312676907009611702844635)
  ·
    refine ⟨22969015360514417554266953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15312676907009611702844635 22969015360514417554266953)
    ·
      refine ⟨17226761520385813165700215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22969015360514417554266953 17226761520385813165700215)
      ·
        refine ⟨25840142280578719748550323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17226761520385813165700215 25840142280578719748550323)
        ·
          refine ⟨38760213420868079622825485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25840142280578719748550323 38760213420868079622825485)
          ·
            refine ⟨14535080032825529858559557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38760213420868079622825485 14535080032825529858559557)
            ·
              refine ⟨2725327506154786848479917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14535080032825529858559557 2725327506154786848479917)
              ·
                refine ⟨1021997814808045068179969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725327506154786848479917 1021997814808045068179969)
                ·
                  refine ⟨766498361106033801134977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021997814808045068179969 766498361106033801134977)
                  ·
                    refine ⟨574873770829525350851233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766498361106033801134977 574873770829525350851233)
                    ·
                      refine ⟨431155328122144013138425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574873770829525350851233 431155328122144013138425)
                      ·
                        rfl

theorem cell23_839672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_839672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839672 prefixEnd_839672 := by exact prefixLift 839672
  have htrace : WordTrace (prefixWord ++ tailWord_839672) baseStart_839672 baseEnd_839672 := by
    simpa [prefixWord, tailWord_839672, baseEnd_839672] using wordTrace_append hprefix tailTrace_839672
  have hstable : (prefixWord ++ tailWord_839672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839672).length < 2 ^ (prefixWord ++ tailWord_839672).sum := by decide
  have hdescent : baseEnd_839672 < baseStart_839672 := by decide
  rcases family_descends (prefixWord ++ tailWord_839672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839688 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_839688 : Nat := 118140960795 + 839688 * 2 ^ 59
def prefixEnd_839688 : Nat := 4983230072969 + 3 ^ 40 * 839688 * 2
def baseEnd_839688 : Nat := 431163543812615950538351

theorem tailTrace_839688 : CollatzResearch.WordTrace tailWord_839688 prefixEnd_839688 431163543812615950538351 := by
  unfold tailWord_839688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15312968690980629069135859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20417291587974172092181145 15312968690980629069135859)
  ·
    refine ⟨22969453036470943603703789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15312968690980629069135859 22969453036470943603703789)
    ·
      refine ⟨8613544888676603851388921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22969453036470943603703789 8613544888676603851388921)
      ·
        refine ⟨6460158666507452888541691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8613544888676603851388921 6460158666507452888541691)
        ·
          refine ⟨9690237999761179332812537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460158666507452888541691 9690237999761179332812537)
          ·
            refine ⟨7267678499820884499609403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690237999761179332812537 7267678499820884499609403)
            ·
              refine ⟨10901517749731326749414105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267678499820884499609403 10901517749731326749414105)
              ·
                refine ⟨8176138312298495062060579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901517749731326749414105 8176138312298495062060579)
                ·
                  refine ⟨12264207468447742593090869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8176138312298495062060579 12264207468447742593090869)
                  ·
                    refine ⟨1149769450166975868102269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12264207468447742593090869 1149769450166975868102269)
                    ·
                      refine ⟨431163543812615950538351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149769450166975868102269 431163543812615950538351)
                      ·
                        rfl

theorem cell23_839688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_839688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839688 prefixEnd_839688 := by exact prefixLift 839688
  have htrace : WordTrace (prefixWord ++ tailWord_839688) baseStart_839688 baseEnd_839688 := by
    simpa [prefixWord, tailWord_839688, baseEnd_839688] using wordTrace_append hprefix tailTrace_839688
  have hstable : (prefixWord ++ tailWord_839688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839688).length < 2 ^ (prefixWord ++ tailWord_839688).sum := by decide
  have hdescent : baseEnd_839688 < baseStart_839688 := by decide
  rcases family_descends (prefixWord ++ tailWord_839688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839693 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_839693 : Nat := 118140960795 + 839693 * 2 ^ 59
def prefixEnd_839693 : Nat := 4983230072969 + 3 ^ 40 * 839693 * 2
def baseEnd_839693 : Nat := 431166111215888430975829

theorem tailTrace_839693 : CollatzResearch.WordTrace tailWord_839693 prefixEnd_839693 431166111215888430975829 := by
  unfold tailWord_839693
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626119746943143992203733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20417413164628762661469155 30626119746943143992203733)
  ·
    refine ⟨717799681568979937317275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30626119746943143992203733 717799681568979937317275)
    ·
      refine ⟨1076699522353469905975913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717799681568979937317275 1076699522353469905975913)
      ·
        refine ⟨807524641765102429481935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076699522353469905975913 807524641765102429481935)
        ·
          refine ⟨1211286962647653644222903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807524641765102429481935 1211286962647653644222903)
          ·
            refine ⟨1816930443971480466334355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211286962647653644222903 1816930443971480466334355)
            ·
              refine ⟨2725395665957220699501533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816930443971480466334355 2725395665957220699501533)
              ·
                refine ⟨1022023374733957762313075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725395665957220699501533 1022023374733957762313075)
                ·
                  refine ⟨1533035062100936643469613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022023374733957762313075 1533035062100936643469613)
                  ·
                    refine ⟨574888148287851241301105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533035062100936643469613 574888148287851241301105)
                    ·
                      refine ⟨431166111215888430975829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574888148287851241301105 431166111215888430975829)
                      ·
                        rfl

theorem cell23_839693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_839693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839693 prefixEnd_839693 := by exact prefixLift 839693
  have htrace : WordTrace (prefixWord ++ tailWord_839693) baseStart_839693 baseEnd_839693 := by
    simpa [prefixWord, tailWord_839693, baseEnd_839693] using wordTrace_append hprefix tailTrace_839693
  have hstable : (prefixWord ++ tailWord_839693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839693).length < 2 ^ (prefixWord ++ tailWord_839693).sum := by decide
  have hdescent : baseEnd_839693 < baseStart_839693 := by decide
  rcases family_descends (prefixWord ++ tailWord_839693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839728 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_839728 : Nat := 118140960795 + 839728 * 2 ^ 59
def prefixEnd_839728 : Nat := 4983230072969 + 3 ^ 40 * 839728 * 2
def baseEnd_839728 : Nat := 431184083038795794038167

theorem tailTrace_839728 : CollatzResearch.WordTrace tailWord_839728 prefixEnd_839728 431184083038795794038167 := by
  unfold tailWord_839728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313698150908172484863919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20418264201210896646485225 15313698150908172484863919)
  ·
    refine ⟨22970547226362258727295879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15313698150908172484863919 22970547226362258727295879)
    ·
      refine ⟨34455820839543388090943819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22970547226362258727295879 34455820839543388090943819)
      ·
        refine ⟨51683731259315082136415729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34455820839543388090943819 51683731259315082136415729)
        ·
          refine ⟨38762798444486311602311797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51683731259315082136415729 38762798444486311602311797)
          ·
            refine ⟨3634012354170591712716731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38762798444486311602311797 3634012354170591712716731)
            ·
              refine ⟨5451018531255887569075097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634012354170591712716731 5451018531255887569075097)
              ·
                refine ⟨4088263898441915676806323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5451018531255887569075097 4088263898441915676806323)
                ·
                  refine ⟨6132395847662873515209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088263898441915676806323 6132395847662873515209485)
                  ·
                    refine ⟨2299648442873577568203557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6132395847662873515209485 2299648442873577568203557)
                    ·
                      refine ⟨431184083038795794038167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2299648442873577568203557 431184083038795794038167)
                      ·
                        rfl

theorem cell23_839728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_839728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839728 prefixEnd_839728 := by exact prefixLift 839728
  have htrace : WordTrace (prefixWord ++ tailWord_839728) baseStart_839728 baseEnd_839728 := by
    simpa [prefixWord, tailWord_839728, baseEnd_839728] using wordTrace_append hprefix tailTrace_839728
  have hstable : (prefixWord ++ tailWord_839728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839728).length < 2 ^ (prefixWord ++ tailWord_839728).sum := by decide
  have hdescent : baseEnd_839728 < baseStart_839728 := by decide
  rcases family_descends (prefixWord ++ tailWord_839728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839745 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_839745 : Nat := 118140960795 + 839745 * 2 ^ 59
def prefixEnd_839745 : Nat := 4983230072969 + 3 ^ 40 * 839745 * 2
def baseEnd_839745 : Nat := 431192812209922227525589

theorem tailTrace_839745 : CollatzResearch.WordTrace tailWord_839745 prefixEnd_839745 431192812209922227525589 := by
  unfold tailWord_839745
  simp only [CollatzResearch.WordTrace]
  refine ⟨30628016342754756873096689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20418677561836504582064459 30628016342754756873096689)
  ·
    refine ⟨22971012257066067654822517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30628016342754756873096689 22971012257066067654822517)
    ·
      refine ⟨2153532399099943842639611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22971012257066067654822517 2153532399099943842639611)
      ·
        refine ⟨3230298598649915763959417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153532399099943842639611 3230298598649915763959417)
        ·
          refine ⟨2422723948987436822969563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230298598649915763959417 2422723948987436822969563)
          ·
            refine ⟨3634085923481155234454345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422723948987436822969563 3634085923481155234454345)
            ·
              refine ⟨2725564442610866425840759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634085923481155234454345 2725564442610866425840759)
              ·
                refine ⟨4088346663916299638761139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725564442610866425840759 4088346663916299638761139)
                ·
                  refine ⟨6132519995874449458141709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088346663916299638761139 6132519995874449458141709)
                  ·
                    refine ⟨2299694998452918546803141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6132519995874449458141709 2299694998452918546803141)
                    ·
                      refine ⟨431192812209922227525589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2299694998452918546803141 431192812209922227525589)
                      ·
                        rfl

theorem cell23_839745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_839745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839745 prefixEnd_839745 := by exact prefixLift 839745
  have htrace : WordTrace (prefixWord ++ tailWord_839745) baseStart_839745 baseEnd_839745 := by
    simpa [prefixWord, tailWord_839745, baseEnd_839745] using wordTrace_append hprefix tailTrace_839745
  have hstable : (prefixWord ++ tailWord_839745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839745).length < 2 ^ (prefixWord ++ tailWord_839745).sum := by decide
  have hdescent : baseEnd_839745 < baseStart_839745 := by decide
  rcases family_descends (prefixWord ++ tailWord_839745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839762 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_839762 : Nat := 118140960795 + 839762 * 2 ^ 59
def prefixEnd_839762 : Nat := 4983230072969 + 3 ^ 40 * 839762 * 2
def baseEnd_839762 : Nat := 431201541381048661013011

theorem tailTrace_839762 : CollatzResearch.WordTrace tailWord_839762 prefixEnd_839762 431201541381048661013011 := by
  unfold tailWord_839762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657159095923292194116385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20419090922462112517643693 7657159095923292194116385)
  ·
    refine ⟨5742869321942469145587289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7657159095923292194116385 5742869321942469145587289)
    ·
      refine ⟨4307151991456851859190467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5742869321942469145587289 4307151991456851859190467)
      ·
        refine ⟨6460727987185277788785701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307151991456851859190467 6460727987185277788785701)
        ·
          refine ⟨1211386497597239585397319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6460727987185277788785701 1211386497597239585397319)
          ·
            refine ⟨1817079746395859378095979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211386497597239585397319 1817079746395859378095979)
            ·
              refine ⟨2725619619593789067143969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817079746395859378095979 2725619619593789067143969)
              ·
                refine ⟨2044214714695341800357977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725619619593789067143969 2044214714695341800357977)
                ·
                  refine ⟨1533161036021506350268483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2044214714695341800357977 1533161036021506350268483)
                  ·
                    refine ⟨2299741554032259525402725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533161036021506350268483 2299741554032259525402725)
                    ·
                      refine ⟨431201541381048661013011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2299741554032259525402725 431201541381048661013011)
                      ·
                        rfl

theorem cell23_839762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_839762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839762 prefixEnd_839762 := by exact prefixLift 839762
  have htrace : WordTrace (prefixWord ++ tailWord_839762) baseStart_839762 baseEnd_839762 := by
    simpa [prefixWord, tailWord_839762, baseEnd_839762] using wordTrace_append hprefix tailTrace_839762
  have hstable : (prefixWord ++ tailWord_839762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839762).length < 2 ^ (prefixWord ++ tailWord_839762).sum := by decide
  have hdescent : baseEnd_839762 < baseStart_839762 := by decide
  rcases family_descends (prefixWord ++ tailWord_839762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839765 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_839765 : Nat := 118140960795 + 839765 * 2 ^ 59
def prefixEnd_839765 : Nat := 4983230072969 + 3 ^ 40 * 839765 * 2
def baseEnd_839765 : Nat := 431203081823012149275497

theorem tailTrace_839765 : CollatzResearch.WordTrace tailWord_839765 prefixEnd_839765 431203081823012149275497 := by
  unfold tailWord_839765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30628745802682300288824749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20419163868454866859216499 30628745802682300288824749)
  ·
    refine ⟨11485779676005862608309281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30628745802682300288824749 11485779676005862608309281)
    ·
      refine ⟨8614334757004396956231961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11485779676005862608309281 8614334757004396956231961)
      ·
        refine ⟨6460751067753297717173971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8614334757004396956231961 6460751067753297717173971)
        ·
          refine ⟨9691126601629946575760957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460751067753297717173971 9691126601629946575760957)
          ·
            refine ⟨3634172475611229965910359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9691126601629946575760957 3634172475611229965910359)
            ·
              refine ⟨5451258713416844948865539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634172475611229965910359 5451258713416844948865539)
              ·
                refine ⟨8176888070125267423298309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451258713416844948865539 8176888070125267423298309)
                ·
                  refine ⟨1533166513148487641868433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8176888070125267423298309 1533166513148487641868433)
                  ·
                    refine ⟨1149874884861365731401325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533166513148487641868433 1149874884861365731401325)
                    ·
                      refine ⟨431203081823012149275497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149874884861365731401325 431203081823012149275497)
                      ·
                        rfl

theorem cell23_839765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_839765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839765 prefixEnd_839765 := by exact prefixLift 839765
  have htrace : WordTrace (prefixWord ++ tailWord_839765) baseStart_839765 baseEnd_839765 := by
    simpa [prefixWord, tailWord_839765, baseEnd_839765] using wordTrace_append hprefix tailTrace_839765
  have hstable : (prefixWord ++ tailWord_839765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839765).length < 2 ^ (prefixWord ++ tailWord_839765).sum := by decide
  have hdescent : baseEnd_839765 < baseStart_839765 := by decide
  rcases family_descends (prefixWord ++ tailWord_839765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839768 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 8]
def baseStart_839768 : Nat := 118140960795 + 839768 * 2 ^ 59
def prefixEnd_839768 : Nat := 4983230072969 + 3 ^ 40 * 839768 * 2
def baseEnd_839768 : Nat := 47911624696108404170887

theorem tailTrace_839768 : CollatzResearch.WordTrace tailWord_839768 prefixEnd_839768 47911624696108404170887 := by
  unfold tailWord_839768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314427610835715900591979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20419236814447621200789305 15314427610835715900591979)
  ·
    refine ⟨22971641416253573850887969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15314427610835715900591979 22971641416253573850887969)
    ·
      refine ⟨17228731062190180388165977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22971641416253573850887969 17228731062190180388165977)
      ·
        refine ⟨12921548296642635291124483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17228731062190180388165977 12921548296642635291124483)
        ·
          refine ⟨19382322444963952936686725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12921548296642635291124483 19382322444963952936686725)
          ·
            refine ⟨3634185458430741175628761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19382322444963952936686725 3634185458430741175628761)
            ·
              refine ⟨2725639093823055881721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634185458430741175628761 2725639093823055881721571)
              ·
                refine ⟨4088458640734583822582357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725639093823055881721571 4088458640734583822582357)
                ·
                  refine ⟨47911624696108404170887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4088458640734583822582357 47911624696108404170887)
                  ·
                    rfl

theorem cell23_839768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 8].length) (baseStart_839768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839768 prefixEnd_839768 := by exact prefixLift 839768
  have htrace : WordTrace (prefixWord ++ tailWord_839768) baseStart_839768 baseEnd_839768 := by
    simpa [prefixWord, tailWord_839768, baseEnd_839768] using wordTrace_append hprefix tailTrace_839768
  have hstable : (prefixWord ++ tailWord_839768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839768).length < 2 ^ (prefixWord ++ tailWord_839768).sum := by decide
  have hdescent : baseEnd_839768 < baseStart_839768 := by decide
  rcases family_descends (prefixWord ++ tailWord_839768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839772 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_839772 : Nat := 118140960795 + 839772 * 2 ^ 59
def prefixEnd_839772 : Nat := 4983230072969 + 3 ^ 40 * 839772 * 2
def baseEnd_839772 : Nat := 143735558729197873962655

theorem tailTrace_839772 : CollatzResearch.WordTrace tailWord_839772 prefixEnd_839772 143735558729197873962655 := by
  unfold tailWord_839772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314500556828470242164785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20419334075771293656219713 15314500556828470242164785)
  ·
    refine ⟨11485875417621352681623589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15314500556828470242164785 11485875417621352681623589)
    ·
      refine ⟨2153601640804003627804423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11485875417621352681623589 2153601640804003627804423)
      ·
        refine ⟨3230402461206005441706635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153601640804003627804423 3230402461206005441706635)
        ·
          refine ⟨4845603691809008162559953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230402461206005441706635 4845603691809008162559953)
          ·
            refine ⟨3634202768856756121919965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4845603691809008162559953 3634202768856756121919965)
            ·
              refine ⟨1362826038321283545719987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634202768856756121919965 1362826038321283545719987)
              ·
                refine ⟨2044239057481925318579981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362826038321283545719987 2044239057481925318579981)
                ·
                  refine ⟨766589646555721994467493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2044239057481925318579981 766589646555721994467493)
                  ·
                    refine ⟨143735558729197873962655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766589646555721994467493 143735558729197873962655)
                    ·
                      rfl

theorem cell23_839772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_839772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839772 prefixEnd_839772 := by exact prefixLift 839772
  have htrace : WordTrace (prefixWord ++ tailWord_839772) baseStart_839772 baseEnd_839772 := by
    simpa [prefixWord, tailWord_839772, baseEnd_839772] using wordTrace_append hprefix tailTrace_839772
  have hstable : (prefixWord ++ tailWord_839772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839772).length < 2 ^ (prefixWord ++ tailWord_839772).sum := by decide
  have hdescent : baseEnd_839772 < baseStart_839772 := by decide
  rcases family_descends (prefixWord ++ tailWord_839772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839815 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 1, 5]
def baseStart_839815 : Nat := 118140960795 + 839815 * 2 ^ 59
def prefixEnd_839815 : Nat := 4983230072969 + 3 ^ 40 * 839815 * 2
def baseEnd_839815 : Nat := 143742918618578984550089

theorem tailTrace_839815 : CollatzResearch.WordTrace tailWord_839815 prefixEnd_839815 143742918618578984550089 := by
  unfold tailWord_839815
  simp only [CollatzResearch.WordTrace]
  refine ⟨30630569452501158828144899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20420379635000772552096599 30630569452501158828144899)
  ·
    refine ⟨45945854178751738242217349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30630569452501158828144899 45945854178751738242217349)
    ·
      refine ⟨8614847658515950920415753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45945854178751738242217349 8614847658515950920415753)
      ·
        refine ⟨6461135743886963190311815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8614847658515950920415753 6461135743886963190311815)
        ·
          refine ⟨9691703615830444785467723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461135743886963190311815 9691703615830444785467723)
          ·
            refine ⟨14537555423745667178201585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691703615830444785467723 14537555423745667178201585)
            ·
              refine ⟨10903166567809250383651189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14537555423745667178201585 10903166567809250383651189)
              ·
                refine ⟨1022171865732117223467299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10903166567809250383651189 1022171865732117223467299)
                ·
                  refine ⟨1533257798598175835200949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022171865732117223467299 1533257798598175835200949)
                  ·
                    refine ⟨143742918618578984550089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1533257798598175835200949 143742918618578984550089)
                    ·
                      rfl

theorem cell23_839815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_839815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839815 prefixEnd_839815 := by exact prefixLift 839815
  have htrace : WordTrace (prefixWord ++ tailWord_839815) baseStart_839815 baseEnd_839815 := by
    simpa [prefixWord, tailWord_839815, baseEnd_839815] using wordTrace_append hprefix tailTrace_839815
  have hstable : (prefixWord ++ tailWord_839815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839815).length < 2 ^ (prefixWord ++ tailWord_839815).sum := by decide
  have hdescent : baseEnd_839815 < baseStart_839815 := by decide
  rcases family_descends (prefixWord ++ tailWord_839815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839829 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_839829 : Nat := 118140960795 + 839829 * 2 ^ 59
def prefixEnd_839829 : Nat := 4983230072969 + 3 ^ 40 * 839829 * 2
def baseEnd_839829 : Nat := 431235944584899898875203

theorem tailTrace_839829 : CollatzResearch.WordTrace tailWord_839829 prefixEnd_839829 431235944584899898875203 := by
  unfold tailWord_839829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631080074450439219154541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20420720049633626146103027 30631080074450439219154541)
  ·
    refine ⟨11486655027918914707182953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30631080074450439219154541 11486655027918914707182953)
    ·
      refine ⟨8614991270939186030387215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11486655027918914707182953 8614991270939186030387215)
      ·
        refine ⟨12922486906408779045580823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614991270939186030387215 12922486906408779045580823)
        ·
          refine ⟨19383730359613168568371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922486906408779045580823 19383730359613168568371235)
          ·
            refine ⟨29075595539419752852556853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383730359613168568371235 29075595539419752852556853)
            ·
              refine ⟨2725837081820601829927205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29075595539419752852556853 2725837081820601829927205)
              ·
                refine ⟨511094452841362843111351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2725837081820601829927205 511094452841362843111351)
                ·
                  refine ⟨766641679262044264667027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511094452841362843111351 766641679262044264667027)
                  ·
                    refine ⟨1149962518893066397000541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766641679262044264667027 1149962518893066397000541)
                    ·
                      refine ⟨431235944584899898875203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1149962518893066397000541 431235944584899898875203)
                      ·
                        rfl

theorem cell23_839829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_839829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839829 prefixEnd_839829 := by exact prefixLift 839829
  have htrace : WordTrace (prefixWord ++ tailWord_839829) baseStart_839829 baseEnd_839829 := by
    simpa [prefixWord, tailWord_839829, baseEnd_839829] using wordTrace_append hprefix tailTrace_839829
  have hstable : (prefixWord ++ tailWord_839829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839829).length < 2 ^ (prefixWord ++ tailWord_839829).sum := by decide
  have hdescent : baseEnd_839829 < baseStart_839829 := by decide
  rcases family_descends (prefixWord ++ tailWord_839829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839830 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_839830 : Nat := 118140960795 + 839830 * 2 ^ 59
def prefixEnd_839830 : Nat := 4983230072969 + 3 ^ 40 * 839830 * 2
def baseEnd_839830 : Nat := 431236458065554394962699

theorem tailTrace_839830 : CollatzResearch.WordTrace tailWord_839830 prefixEnd_839830 431236458065554394962699 := by
  unfold tailWord_839830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914444784215426024371309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20420744364964544259960629 1914444784215426024371309)
  ·
    refine ⟨717916794080784759139241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1914444784215426024371309 717916794080784759139241)
    ·
      refine ⟨538437595560588569354431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717916794080784759139241 538437595560588569354431)
      ·
        refine ⟨807656393340882854031647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538437595560588569354431 807656393340882854031647)
        ·
          refine ⟨1211484590011324281047471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807656393340882854031647 1211484590011324281047471)
          ·
            refine ⟨1817226885016986421571207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211484590011324281047471 1817226885016986421571207)
            ·
              refine ⟨2725840327525479632356811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817226885016986421571207 2725840327525479632356811)
              ·
                refine ⟨4088760491288219448535217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725840327525479632356811 4088760491288219448535217)
                ·
                  refine ⟨3066570368466164586401413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4088760491288219448535217 3066570368466164586401413)
                  ·
                    refine ⟨574981944087405859950265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066570368466164586401413 574981944087405859950265)
                    ·
                      refine ⟨431236458065554394962699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574981944087405859950265 431236458065554394962699)
                      ·
                        rfl

theorem cell23_839830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_839830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839830 prefixEnd_839830 := by exact prefixLift 839830
  have htrace : WordTrace (prefixWord ++ tailWord_839830) baseStart_839830 baseEnd_839830 := by
    simpa [prefixWord, tailWord_839830, baseEnd_839830] using wordTrace_append hprefix tailTrace_839830
  have hstable : (prefixWord ++ tailWord_839830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839830).length < 2 ^ (prefixWord ++ tailWord_839830).sum := by decide
  have hdescent : baseEnd_839830 < baseStart_839830 := by decide
  rcases family_descends (prefixWord ++ tailWord_839830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839845 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_839845 : Nat := 118140960795 + 839845 * 2 ^ 59
def prefixEnd_839845 : Nat := 4983230072969 + 3 ^ 40 * 839845 * 2
def baseEnd_839845 : Nat := 143748053425123945425043

theorem tailTrace_839845 : CollatzResearch.WordTrace tailWord_839845 prefixEnd_839845 143748053425123945425043 := by
  unfold tailWord_839845
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631663642392473951736989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20421109094928315967824659 30631663642392473951736989)
  ·
    refine ⟨11486873865897177731901371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30631663642392473951736989 11486873865897177731901371)
    ·
      refine ⟨17230310798845766597852057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486873865897177731901371 17230310798845766597852057)
      ·
        refine ⟨12922733099134324948389043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17230310798845766597852057 12922733099134324948389043)
        ·
          refine ⟨19384099648701487422583565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922733099134324948389043 19384099648701487422583565)
          ·
            refine ⟨7269037368263057783468837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19384099648701487422583565 7269037368263057783468837)
            ·
              refine ⟨1362944506549323334400407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7269037368263057783468837 1362944506549323334400407)
              ·
                refine ⟨2044416759823985001600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362944506549323334400407 2044416759823985001600611)
                ·
                  refine ⟨3066625139735977502400917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044416759823985001600611 3066625139735977502400917)
                  ·
                    refine ⟨143748053425123945425043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3066625139735977502400917 143748053425123945425043)
                    ·
                      rfl

theorem cell23_839845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_839845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839845 prefixEnd_839845 := by exact prefixLift 839845
  have htrace : WordTrace (prefixWord ++ tailWord_839845) baseStart_839845 baseEnd_839845 := by
    simpa [prefixWord, tailWord_839845, baseEnd_839845] using wordTrace_append hprefix tailTrace_839845
  have hstable : (prefixWord ++ tailWord_839845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839845).length < 2 ^ (prefixWord ++ tailWord_839845).sum := by decide
  have hdescent : baseEnd_839845 < baseStart_839845 := by decide
  rcases family_descends (prefixWord ++ tailWord_839845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839865 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_839865 : Nat := 118140960795 + 839865 * 2 ^ 59
def prefixEnd_839865 : Nat := 4983230072969 + 3 ^ 40 * 839865 * 2
def baseEnd_839865 : Nat := 431254429888461758025037

theorem tailTrace_839865 : CollatzResearch.WordTrace tailWord_839865 prefixEnd_839865 431254429888461758025037 := by
  unfold tailWord_839865
  simp only [CollatzResearch.WordTrace]
  refine ⟨30632393102320017367465049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20421595401546678244976699 30632393102320017367465049)
  ·
    refine ⟨22974294826740013025598787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30632393102320017367465049 22974294826740013025598787)
    ·
      refine ⟨34461442240110019538398181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22974294826740013025598787 34461442240110019538398181)
      ·
        refine ⟨6461520420020628663449659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34461442240110019538398181 6461520420020628663449659)
        ·
          refine ⟨9692280630030942995174489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461520420020628663449659 9692280630030942995174489)
          ·
            refine ⟨7269210472523207246380867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9692280630030942995174489 7269210472523207246380867)
            ·
              refine ⟨10903815708784810869571301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269210472523207246380867 10903815708784810869571301)
              ·
                refine ⟨2044465445397152038044619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10903815708784810869571301 2044465445397152038044619)
                ·
                  refine ⟨3066698168095728057066929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044465445397152038044619 3066698168095728057066929)
                  ·
                    refine ⟨2300023626071796042800197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3066698168095728057066929 2300023626071796042800197)
                    ·
                      refine ⟨431254429888461758025037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2300023626071796042800197 431254429888461758025037)
                      ·
                        rfl

theorem cell23_839865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_839865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839865 prefixEnd_839865 := by exact prefixLift 839865
  have htrace : WordTrace (prefixWord ++ tailWord_839865) baseStart_839865 baseEnd_839865 := by
    simpa [prefixWord, tailWord_839865, baseEnd_839865] using wordTrace_append hprefix tailTrace_839865
  have hstable : (prefixWord ++ tailWord_839865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839865).length < 2 ^ (prefixWord ++ tailWord_839865).sum := by decide
  have hdescent : baseEnd_839865 < baseStart_839865 := by decide
  rcases family_descends (prefixWord ++ tailWord_839865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839886 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_839886 : Nat := 118140960795 + 839886 * 2 ^ 59
def prefixEnd_839886 : Nat := 4983230072969 + 3 ^ 40 * 839886 * 2
def baseEnd_839886 : Nat := 431265212982206175862441

theorem tailTrace_839886 : CollatzResearch.WordTrace tailWord_839886 prefixEnd_839886 431265212982206175862441 := by
  unfold tailWord_839886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829144879405492244247439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20422106023495958635986341 3829144879405492244247439)
  ·
    refine ⟨5743717319108238366371159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3829144879405492244247439 5743717319108238366371159)
    ·
      refine ⟨8615575978662357549556739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743717319108238366371159 8615575978662357549556739)
      ·
        refine ⟨12923363967993536324335109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615575978662357549556739 12923363967993536324335109)
        ·
          refine ⟨2423130743998788060812833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12923363967993536324335109 2423130743998788060812833)
          ·
            refine ⟨1817348057999091045609625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423130743998788060812833 1817348057999091045609625)
            ·
              refine ⟨1363011043499318284207219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817348057999091045609625 1363011043499318284207219)
              ·
                refine ⟨2044516565248977426310829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363011043499318284207219 2044516565248977426310829)
                ·
                  refine ⟨766693711968366534866561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2044516565248977426310829 766693711968366534866561)
                  ·
                    refine ⟨575020283976274901149921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766693711968366534866561 575020283976274901149921)
                    ·
                      refine ⟨431265212982206175862441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575020283976274901149921 431265212982206175862441)
                      ·
                        rfl

theorem cell23_839886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_839886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839886 prefixEnd_839886 := by exact prefixLift 839886
  have htrace : WordTrace (prefixWord ++ tailWord_839886) baseStart_839886 baseEnd_839886 := by
    simpa [prefixWord, tailWord_839886, baseEnd_839886] using wordTrace_append hprefix tailTrace_839886
  have hstable : (prefixWord ++ tailWord_839886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839886).length < 2 ^ (prefixWord ++ tailWord_839886).sum := by decide
  have hdescent : baseEnd_839886 < baseStart_839886 := by decide
  rcases family_descends (prefixWord ++ tailWord_839886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839955 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_839955 : Nat := 118140960795 + 839955 * 2 ^ 59
def prefixEnd_839955 : Nat := 4983230072969 + 3 ^ 40 * 839955 * 2
def baseEnd_839955 : Nat := 431300643147366405899623

theorem tailTrace_839955 : CollatzResearch.WordTrace tailWord_839955 prefixEnd_839955 431300643147366405899623 := by
  unfold tailWord_839955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635675671993962738241319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20423783781329308492160879 30635675671993962738241319)
  ·
    refine ⟨45953513507990944107361979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30635675671993962738241319 45953513507990944107361979)
    ·
      refine ⟨68930270261986416161042969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45953513507990944107361979 68930270261986416161042969)
      ·
        refine ⟨51697702696489812120782227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68930270261986416161042969 51697702696489812120782227)
        ·
          refine ⟨77546554044734718181173341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51697702696489812120782227 77546554044734718181173341)
          ·
            refine ⟨29079957766775519317940003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77546554044734718181173341 29079957766775519317940003)
            ·
              refine ⟨43619936650163278976910005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079957766775519317940003 43619936650163278976910005)
              ·
                refine ⟨4089369060952807404085313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43619936650163278976910005 4089369060952807404085313)
                ·
                  refine ⟨3067026795714605553063985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089369060952807404085313 3067026795714605553063985)
                  ·
                    refine ⟨2300270096785954164797989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067026795714605553063985 2300270096785954164797989)
                    ·
                      refine ⟨431300643147366405899623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2300270096785954164797989 431300643147366405899623)
                      ·
                        rfl

theorem cell23_839955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_839955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839955 prefixEnd_839955 := by exact prefixLift 839955
  have htrace : WordTrace (prefixWord ++ tailWord_839955) baseStart_839955 baseEnd_839955 := by
    simpa [prefixWord, tailWord_839955, baseEnd_839955] using wordTrace_append hprefix tailTrace_839955
  have hstable : (prefixWord ++ tailWord_839955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839955).length < 2 ^ (prefixWord ++ tailWord_839955).sum := by decide
  have hdescent : baseEnd_839955 < baseStart_839955 := by decide
  rcases family_descends (prefixWord ++ tailWord_839955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839976 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_839976 : Nat := 118140960795 + 839976 * 2 ^ 59
def prefixEnd_839976 : Nat := 4983230072969 + 3 ^ 40 * 839976 * 2
def baseEnd_839976 : Nat := 431311426241110823737027

theorem tailTrace_839976 : CollatzResearch.WordTrace tailWord_839976 prefixEnd_839976 431311426241110823737027 := by
  unfold tailWord_839976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318220802458941662377891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20424294403278588883170521 15318220802458941662377891)
  ·
    refine ⟨22977331203688412493566837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318220802458941662377891 22977331203688412493566837)
    ·
      refine ⟨2154124800345788671271891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22977331203688412493566837 2154124800345788671271891)
      ·
        refine ⟨3231187200518683006907837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154124800345788671271891 3231187200518683006907837)
        ·
          refine ⟨1211695200194506127590439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3231187200518683006907837 1211695200194506127590439)
          ·
            refine ⟨1817542800291759191385659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211695200194506127590439 1817542800291759191385659)
            ·
              refine ⟨2726314200437638787078489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817542800291759191385659 2726314200437638787078489)
              ·
                refine ⟨2044735650328229090308867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726314200437638787078489 2044735650328229090308867)
                ·
                  refine ⟨3067103475492343635463301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044735650328229090308867 3067103475492343635463301)
                  ·
                    refine ⟨575081901654814431649369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067103475492343635463301 575081901654814431649369)
                    ·
                      refine ⟨431311426241110823737027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575081901654814431649369 431311426241110823737027)
                      ·
                        rfl

theorem cell23_839976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_839976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839976 prefixEnd_839976 := by exact prefixLift 839976
  have htrace : WordTrace (prefixWord ++ tailWord_839976) baseStart_839976 baseEnd_839976 := by
    simpa [prefixWord, tailWord_839976, baseEnd_839976] using wordTrace_append hprefix tailTrace_839976
  have hstable : (prefixWord ++ tailWord_839976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839976).length < 2 ^ (prefixWord ++ tailWord_839976).sum := by decide
  have hdescent : baseEnd_839976 < baseStart_839976 := by decide
  rcases family_descends (prefixWord ++ tailWord_839976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839993 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 2, 2, 2]
def baseStart_839993 : Nat := 118140960795 + 839993 * 2 ^ 59
def prefixEnd_839993 : Nat := 4983230072969 + 3 ^ 40 * 839993 * 2
def baseEnd_839993 : Nat := 431320155412237257224449

theorem tailTrace_839993 : CollatzResearch.WordTrace tailWord_839993 prefixEnd_839993 431320155412237257224449 := by
  unfold tailWord_839993
  simp only [CollatzResearch.WordTrace]
  refine ⟨30637061645856295228124633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20424707763904196818749755 30637061645856295228124633)
  ·
    refine ⟨22977796234392221421093475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30637061645856295228124633 22977796234392221421093475)
    ·
      refine ⟨34466694351588332131640213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22977796234392221421093475 34466694351588332131640213)
      ·
        refine ⟨1615626297730703068670635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34466694351588332131640213 1615626297730703068670635)
        ·
          refine ⟨2423439446596054603005953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615626297730703068670635 2423439446596054603005953)
          ·
            refine ⟨1817579584947040952254465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423439446596054603005953 1817579584947040952254465)
            ·
              refine ⟨1363184688710280714190849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817579584947040952254465 1363184688710280714190849)
              ·
                refine ⟨1022388516532710535643137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363184688710280714190849 1022388516532710535643137)
                ·
                  refine ⟨766791387399532901732353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022388516532710535643137 766791387399532901732353)
                  ·
                    refine ⟨575093540549649676299265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766791387399532901732353 575093540549649676299265)
                    ·
                      refine ⟨431320155412237257224449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575093540549649676299265 431320155412237257224449)
                      ·
                        rfl

theorem cell23_839993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_839993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839993 prefixEnd_839993 := by exact prefixLift 839993
  have htrace : WordTrace (prefixWord ++ tailWord_839993) baseStart_839993 baseEnd_839993 := by
    simpa [prefixWord, tailWord_839993, baseEnd_839993] using wordTrace_append hprefix tailTrace_839993
  have hstable : (prefixWord ++ tailWord_839993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839993).length < 2 ^ (prefixWord ++ tailWord_839993).sum := by decide
  have hdescent : baseEnd_839993 < baseStart_839993 := by decide
  rcases family_descends (prefixWord ++ tailWord_839993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840059 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 3, 4]
def baseStart_840059 : Nat := 118140960795 + 840059 * 2 ^ 59
def prefixEnd_840059 : Nat := 4983230072969 + 3 ^ 40 * 840059 * 2
def baseEnd_840059 : Nat := 143784681711811332999715

theorem tailTrace_840059 : CollatzResearch.WordTrace tailWord_840059 prefixEnd_840059 143784681711811332999715 := by
  unfold tailWord_840059
  simp only [CollatzResearch.WordTrace]
  refine ⟨30639468863617188500027231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20426312575744792333351487 30639468863617188500027231)
  ·
    refine ⟨45959203295425782750040847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30639468863617188500027231 45959203295425782750040847)
    ·
      refine ⟨68938804943138674125061271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45959203295425782750040847 68938804943138674125061271)
      ·
        refine ⟨103408207414708011187591907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68938804943138674125061271 103408207414708011187591907)
        ·
          refine ⟨155112311122062016781387861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103408207414708011187591907 155112311122062016781387861)
          ·
            refine ⟨1817722395961664259156889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 155112311122062016781387861 1817722395961664259156889)
            ·
              refine ⟨1363291796971248194367667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817722395961664259156889 1363291796971248194367667)
              ·
                refine ⟨2044937695456872291551501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363291796971248194367667 2044937695456872291551501)
                ·
                  refine ⟨766851635796327109331813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2044937695456872291551501 766851635796327109331813)
                  ·
                    refine ⟨143784681711811332999715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766851635796327109331813 143784681711811332999715)
                    ·
                      rfl

theorem cell23_840059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 4].length) (baseStart_840059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840059 prefixEnd_840059 := by exact prefixLift 840059
  have htrace : WordTrace (prefixWord ++ tailWord_840059) baseStart_840059 baseEnd_840059 := by
    simpa [prefixWord, tailWord_840059, baseEnd_840059] using wordTrace_append hprefix tailTrace_840059
  have hstable : (prefixWord ++ tailWord_840059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840059).length < 2 ^ (prefixWord ++ tailWord_840059).sum := by decide
  have hdescent : baseEnd_840059 < baseStart_840059 := by decide
  rcases family_descends (prefixWord ++ tailWord_840059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840136 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 1, 5]
def baseStart_840136 : Nat := 118140960795 + 840136 * 2 ^ 59
def prefixEnd_840136 : Nat := 4983230072969 + 3 ^ 40 * 840136 * 2
def baseEnd_840136 : Nat := 143797861048610065912097

theorem tailTrace_840136 : CollatzResearch.WordTrace tailWord_840136 prefixEnd_840136 143797861048610065912097 := by
  unfold tailWord_840136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321138642169115325290131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20428184856225487100386841 15321138642169115325290131)
  ·
    refine ⟨22981707963253672987935197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15321138642169115325290131 22981707963253672987935197)
    ·
      refine ⟨8618140486220127370475699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22981707963253672987935197 8618140486220127370475699)
      ·
        refine ⟨12927210729330191055713549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618140486220127370475699 12927210729330191055713549)
        ·
          refine ⟨4847704023498821645892581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12927210729330191055713549 4847704023498821645892581)
          ·
            refine ⟨908944504406029058604859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4847704023498821645892581 908944504406029058604859)
            ·
              refine ⟨1363416756609043587907289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908944504406029058604859 1363416756609043587907289)
              ·
                refine ⟨1022562567456782690930467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363416756609043587907289 1022562567456782690930467)
                ·
                  refine ⟨1533843851185174036395701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022562567456782690930467 1533843851185174036395701)
                  ·
                    refine ⟨143797861048610065912097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1533843851185174036395701 143797861048610065912097)
                    ·
                      rfl

theorem cell23_840136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_840136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840136 prefixEnd_840136 := by exact prefixLift 840136
  have htrace : WordTrace (prefixWord ++ tailWord_840136) baseStart_840136 baseEnd_840136 := by
    simpa [prefixWord, tailWord_840136, baseEnd_840136] using wordTrace_append hprefix tailTrace_840136
  have hstable : (prefixWord ++ tailWord_840136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840136).length < 2 ^ (prefixWord ++ tailWord_840136).sum := by decide
  have hdescent : baseEnd_840136 < baseStart_840136 := by decide
  rcases family_descends (prefixWord ++ tailWord_840136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840149 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_840149 : Nat := 118140960795 + 840149 * 2 ^ 59
def prefixEnd_840149 : Nat := 4983230072969 + 3 ^ 40 * 840149 * 2
def baseEnd_840149 : Nat := 143800086131446215624577

theorem tailTrace_840149 : CollatzResearch.WordTrace tailWord_840149 prefixEnd_840149 143800086131446215624577 := by
  unfold tailWord_840149
  simp only [CollatzResearch.WordTrace]
  refine ⟨30642751433291133870803501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20428500955527422580535667 30642751433291133870803501)
  ·
    refine ⟨11491031787484175201551313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30642751433291133870803501 11491031787484175201551313)
    ·
      refine ⟨8618273840613131401163485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11491031787484175201551313 8618273840613131401163485)
      ·
        refine ⟨3231852690229924275436307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8618273840613131401163485 3231852690229924275436307)
        ·
          refine ⟨4847779035344886413154461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231852690229924275436307 4847779035344886413154461)
          ·
            refine ⟨1817917138254332404932923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4847779035344886413154461 1817917138254332404932923)
            ·
              refine ⟨2726875707381498607399385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817917138254332404932923 2726875707381498607399385)
              ·
                refine ⟨2045156780536123955549539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726875707381498607399385 2045156780536123955549539)
                ·
                  refine ⟨3067735170804185933324309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045156780536123955549539 3067735170804185933324309)
                  ·
                    refine ⟨143800086131446215624577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3067735170804185933324309 143800086131446215624577)
                    ·
                      rfl

theorem cell23_840149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_840149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840149 prefixEnd_840149 := by exact prefixLift 840149
  have htrace : WordTrace (prefixWord ++ tailWord_840149) baseStart_840149 baseEnd_840149 := by
    simpa [prefixWord, tailWord_840149, baseEnd_840149] using wordTrace_append hprefix tailTrace_840149
  have hstable : (prefixWord ++ tailWord_840149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840149).length < 2 ^ (prefixWord ++ tailWord_840149).sum := by decide
  have hdescent : baseEnd_840149 < baseStart_840149 := by decide
  rcases family_descends (prefixWord ++ tailWord_840149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840150 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_840150 : Nat := 118140960795 + 840150 * 2 ^ 59
def prefixEnd_840150 : Nat := 4983230072969 + 3 ^ 40 * 840150 * 2
def baseEnd_840150 : Nat := 431400771874993142961227

theorem tailTrace_840150 : CollatzResearch.WordTrace tailWord_840150 prefixEnd_840150 431400771874993142961227 := by
  unfold tailWord_840150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915174244142969440099369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20428525270858340694393269 1915174244142969440099369)
  ·
    refine ⟨1436380683107227080074527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1915174244142969440099369 1436380683107227080074527)
    ·
      refine ⟨2154571024660840620111791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436380683107227080074527 2154571024660840620111791)
      ·
        refine ⟨3231856536991260930167687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154571024660840620111791 3231856536991260930167687)
        ·
          refine ⟨4847784805486891395251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231856536991260930167687 4847784805486891395251531)
          ·
            refine ⟨7271677208230337092877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847784805486891395251531 7271677208230337092877297)
            ·
              refine ⟨5453757906172752819657973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7271677208230337092877297 5453757906172752819657973)
              ·
                refine ⟨511289803703695576842935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5453757906172752819657973 511289803703695576842935)
                ·
                  refine ⟨766934705555543365264403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511289803703695576842935 766934705555543365264403)
                  ·
                    refine ⟨1150402058333315047896605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766934705555543365264403 1150402058333315047896605)
                    ·
                      refine ⟨431400771874993142961227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150402058333315047896605 431400771874993142961227)
                      ·
                        rfl

theorem cell23_840150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_840150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840150 prefixEnd_840150 := by exact prefixLift 840150
  have htrace : WordTrace (prefixWord ++ tailWord_840150) baseStart_840150 baseEnd_840150 := by
    simpa [prefixWord, tailWord_840150, baseEnd_840150] using wordTrace_append hprefix tailTrace_840150
  have hstable : (prefixWord ++ tailWord_840150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840150).length < 2 ^ (prefixWord ++ tailWord_840150).sum := by decide
  have hdescent : baseEnd_840150 < baseStart_840150 := by decide
  rcases family_descends (prefixWord ++ tailWord_840150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840159 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_840159 : Nat := 118140960795 + 840159 * 2 ^ 59
def prefixEnd_840159 : Nat := 4983230072969 + 3 ^ 40 * 840159 * 2
def baseEnd_840159 : Nat := 431405393200883607748685

theorem tailTrace_840159 : CollatzResearch.WordTrace tailWord_840159 prefixEnd_840159 431405393200883607748685 := by
  unfold tailWord_840159
  simp only [CollatzResearch.WordTrace]
  refine ⟨30643116163254905578667531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20428744108836603719111687 30643116163254905578667531)
  ·
    refine ⟨45964674244882358368001297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30643116163254905578667531 45964674244882358368001297)
    ·
      refine ⟨34473505683661768776000973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45964674244882358368001297 34473505683661768776000973)
      ·
        refine ⟨12927564631373163291000365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34473505683661768776000973 12927564631373163291000365)
        ·
          refine ⟨4847836736764936234125137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12927564631373163291000365 4847836736764936234125137)
          ·
            refine ⟨3635877552573702175593853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4847836736764936234125137 3635877552573702175593853)
            ·
              refine ⟨1363454082215138315847695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3635877552573702175593853 1363454082215138315847695)
              ·
                refine ⟨2045181123322707473771543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363454082215138315847695 2045181123322707473771543)
                ·
                  refine ⟨3067771684984061210657315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045181123322707473771543 3067771684984061210657315)
                  ·
                    refine ⟨4601657527476091815985973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067771684984061210657315 4601657527476091815985973)
                    ·
                      refine ⟨431405393200883607748685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4601657527476091815985973 431405393200883607748685)
                      ·
                        rfl

theorem cell23_840159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_840159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840159 prefixEnd_840159 := by exact prefixLift 840159
  have htrace : WordTrace (prefixWord ++ tailWord_840159) baseStart_840159 baseEnd_840159 := by
    simpa [prefixWord, tailWord_840159, baseEnd_840159] using wordTrace_append hprefix tailTrace_840159
  have hstable : (prefixWord ++ tailWord_840159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840159).length < 2 ^ (prefixWord ++ tailWord_840159).sum := by decide
  have hdescent : baseEnd_840159 < baseStart_840159 := by decide
  rcases family_descends (prefixWord ++ tailWord_840159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840196 : List Nat := [2, 3, 2, 3, 1, 2, 3, 7]
def baseStart_840196 : Nat := 118140960795 + 840196 * 2 ^ 59
def prefixEnd_840196 : Nat := 4983230072969 + 3 ^ 40 * 840196 * 2
def baseEnd_840196 : Nat := 15978681184633331962445

theorem tailTrace_840196 : CollatzResearch.WordTrace tailWord_840196 prefixEnd_840196 15978681184633331962445 := by
  unfold tailWord_840196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322232832060430448882221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20429643776080573931842961 15322232832060430448882221)
  ·
    refine ⟨5745837312022661418330833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15322232832060430448882221 5745837312022661418330833)
    ·
      refine ⟨4309377984016996063748125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5745837312022661418330833 4309377984016996063748125)
      ·
        refine ⟨1616016744006373523905547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4309377984016996063748125 1616016744006373523905547)
        ·
          refine ⟨2424025116009560285858321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616016744006373523905547 2424025116009560285858321)
          ·
            refine ⟨1818018837007170214393741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424025116009560285858321 1818018837007170214393741)
            ·
              refine ⟨681757063877688830397653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818018837007170214393741 681757063877688830397653)
              ·
                refine ⟨15978681184633331962445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 681757063877688830397653 15978681184633331962445)
                ·
                  rfl

theorem cell23_840196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 7].length) (baseStart_840196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840196 prefixEnd_840196 := by exact prefixLift 840196
  have htrace : WordTrace (prefixWord ++ tailWord_840196) baseStart_840196 baseEnd_840196 := by
    simpa [prefixWord, tailWord_840196, baseEnd_840196] using wordTrace_append hprefix tailTrace_840196
  have hstable : (prefixWord ++ tailWord_840196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840196).length < 2 ^ (prefixWord ++ tailWord_840196).sum := by decide
  have hdescent : baseEnd_840196 < baseStart_840196 := by decide
  rcases family_descends (prefixWord ++ tailWord_840196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840206 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_840206 : Nat := 118140960795 + 840206 * 2 ^ 59
def prefixEnd_840206 : Nat := 4983230072969 + 3 ^ 40 * 840206 * 2
def baseEnd_840206 : Nat := 431429526791644923860969

theorem tailTrace_840206 : CollatzResearch.WordTrace tailWord_840206 prefixEnd_840206 431429526791644923860969 := by
  unfold tailWord_840206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830603799260579075703559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20429886929389755070418981 3830603799260579075703559)
  ·
    refine ⟨5745905698890868613555339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830603799260579075703559 5745905698890868613555339)
    ·
      refine ⟨8618858548336302920333009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745905698890868613555339 8618858548336302920333009)
      ·
        refine ⟨6464143911252227190249757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8618858548336302920333009 6464143911252227190249757)
        ·
          refine ⟨2424053966719585196343659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6464143911252227190249757 2424053966719585196343659)
          ·
            refine ⟨3636080950079377794515489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424053966719585196343659 3636080950079377794515489)
            ·
              refine ⟨2727060712559533345886617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636080950079377794515489 2727060712559533345886617)
              ·
                refine ⟨2045295534419650009414963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727060712559533345886617 2045295534419650009414963)
                ·
                  refine ⟨3067943301629475014122445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045295534419650009414963 3067943301629475014122445)
                  ·
                    refine ⟨1150478738111053130295917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3067943301629475014122445 1150478738111053130295917)
                    ·
                      refine ⟨431429526791644923860969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150478738111053130295917 431429526791644923860969)
                      ·
                        rfl

theorem cell23_840206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_840206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840206 prefixEnd_840206 := by exact prefixLift 840206
  have htrace : WordTrace (prefixWord ++ tailWord_840206) baseStart_840206 baseEnd_840206 := by
    simpa [prefixWord, tailWord_840206, baseEnd_840206] using wordTrace_append hprefix tailTrace_840206
  have hstable : (prefixWord ++ tailWord_840206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840206).length < 2 ^ (prefixWord ++ tailWord_840206).sum := by decide
  have hdescent : baseEnd_840206 < baseStart_840206 := by decide
  rcases family_descends (prefixWord ++ tailWord_840206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840237 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_840237 : Nat := 118140960795 + 840237 * 2 ^ 59
def prefixEnd_840237 : Nat := 4983230072969 + 3 ^ 40 * 840237 * 2
def baseEnd_840237 : Nat := 431445444691934302573327

theorem tailTrace_840237 : CollatzResearch.WordTrace tailWord_840237 prefixEnd_840237 431445444691934302573327 := by
  unfold tailWord_840237
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645961056972324900006965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20430640704648216600004643 30645961056972324900006965)
  ·
    refine ⟨2873058849091155459375653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30645961056972324900006965 2873058849091155459375653)
    ·
      refine ⟨538698534204591648632935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2873058849091155459375653 538698534204591648632935)
      ·
        refine ⟨808047801306887472949403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538698534204591648632935 808047801306887472949403)
        ·
          refine ⟨1212071701960331209424105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808047801306887472949403 1212071701960331209424105)
          ·
            refine ⟨909053776470248407068079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212071701960331209424105 909053776470248407068079)
            ·
              refine ⟨1363580664705372610602119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909053776470248407068079 1363580664705372610602119)
              ·
                refine ⟨2045370997058058915903179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363580664705372610602119 2045370997058058915903179)
                ·
                  refine ⟨3068056495587088373854769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045370997058058915903179 3068056495587088373854769)
                  ·
                    refine ⟨2301042371690316280391077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3068056495587088373854769 2301042371690316280391077)
                    ·
                      refine ⟨431445444691934302573327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2301042371690316280391077 431445444691934302573327)
                      ·
                        rfl

theorem cell23_840237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_840237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840237 prefixEnd_840237 := by exact prefixLift 840237
  have htrace : WordTrace (prefixWord ++ tailWord_840237) baseStart_840237 baseEnd_840237 := by
    simpa [prefixWord, tailWord_840237, baseEnd_840237] using wordTrace_append hprefix tailTrace_840237
  have hstable : (prefixWord ++ tailWord_840237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840237).length < 2 ^ (prefixWord ++ tailWord_840237).sum := by decide
  have hdescent : baseEnd_840237 < baseStart_840237 := by decide
  rcases family_descends (prefixWord ++ tailWord_840237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840249 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_840249 : Nat := 118140960795 + 840249 * 2 ^ 59
def prefixEnd_840249 : Nat := 4983230072969 + 3 ^ 40 * 840249 * 2
def baseEnd_840249 : Nat := 431451606459788255623271

theorem tailTrace_840249 : CollatzResearch.WordTrace tailWord_840249 prefixEnd_840249 431451606459788255623271 := by
  unfold tailWord_840249
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646398732928850949443801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20430932488619233966295867 30646398732928850949443801)
  ·
    refine ⟨22984799049696638212082851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30646398732928850949443801 22984799049696638212082851)
    ·
      refine ⟨34477198574544957318124277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22984799049696638212082851 34477198574544957318124277)
      ·
        refine ⟨3232237366363589748574151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34477198574544957318124277 3232237366363589748574151)
        ·
          refine ⟨4848356049545384622861227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232237366363589748574151 4848356049545384622861227)
          ·
            refine ⟨7272534074318076934291841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848356049545384622861227 7272534074318076934291841)
            ·
              refine ⟨5454400555738557700718881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272534074318076934291841 5454400555738557700718881)
              ·
                refine ⟨4090800416803918275539161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454400555738557700718881 4090800416803918275539161)
                ·
                  refine ⟨3068100312602938706654371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090800416803918275539161 3068100312602938706654371)
                  ·
                    refine ⟨4602150468904408059981557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3068100312602938706654371 4602150468904408059981557)
                    ·
                      refine ⟨431451606459788255623271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4602150468904408059981557 431451606459788255623271)
                      ·
                        rfl

theorem cell23_840249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_840249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840249 prefixEnd_840249 := by exact prefixLift 840249
  have htrace : WordTrace (prefixWord ++ tailWord_840249) baseStart_840249 baseEnd_840249 := by
    simpa [prefixWord, tailWord_840249, baseEnd_840249] using wordTrace_append hprefix tailTrace_840249
  have hstable : (prefixWord ++ tailWord_840249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840249).length < 2 ^ (prefixWord ++ tailWord_840249).sum := by decide
  have hdescent : baseEnd_840249 < baseStart_840249 := by decide
  rcases family_descends (prefixWord ++ tailWord_840249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840263 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_840263 : Nat := 118140960795 + 840263 * 2 ^ 59
def prefixEnd_840263 : Nat := 4983230072969 + 3 ^ 40 * 840263 * 2
def baseEnd_840263 : Nat := 431458795188951200848207

theorem tailTrace_840263 : CollatzResearch.WordTrace tailWord_840263 prefixEnd_840263 431458795188951200848207 := by
  unfold tailWord_840263
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646909354878131340453443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20431272903252087560302295 30646909354878131340453443)
  ·
    refine ⟨45970364032317197010680165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30646909354878131340453443 45970364032317197010680165)
    ·
      refine ⟨8619443256059474439502531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45970364032317197010680165 8619443256059474439502531)
      ·
        refine ⟨12929164884089211659253797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619443256059474439502531 12929164884089211659253797)
        ·
          refine ⟨2424218415766727186110087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12929164884089211659253797 2424218415766727186110087)
          ·
            refine ⟨3636327623650090779165131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424218415766727186110087 3636327623650090779165131)
            ·
              refine ⟨5454491435475136168747697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636327623650090779165131 5454491435475136168747697)
              ·
                refine ⟨4090868576606352126560773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454491435475136168747697 4090868576606352126560773)
                ·
                  refine ⟨767037858113691023730145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4090868576606352126560773 767037858113691023730145)
                  ·
                    refine ⟨575278393585268267797609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767037858113691023730145 575278393585268267797609)
                    ·
                      refine ⟨431458795188951200848207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575278393585268267797609 431458795188951200848207)
                      ·
                        rfl

theorem cell23_840263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_840263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840263 prefixEnd_840263 := by exact prefixLift 840263
  have htrace : WordTrace (prefixWord ++ tailWord_840263) baseStart_840263 baseEnd_840263 := by
    simpa [prefixWord, tailWord_840263, baseEnd_840263] using wordTrace_append hprefix tailTrace_840263
  have hstable : (prefixWord ++ tailWord_840263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840263).length < 2 ^ (prefixWord ++ tailWord_840263).sum := by decide
  have hdescent : baseEnd_840263 < baseStart_840263 := by decide
  rcases family_descends (prefixWord ++ tailWord_840263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840356 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_840356 : Nat := 118140960795 + 840356 * 2 ^ 59
def prefixEnd_840356 : Nat := 4983230072969 + 3 ^ 40 * 840356 * 2
def baseEnd_840356 : Nat := 431506548889819336985279

theorem tailTrace_840356 : CollatzResearch.WordTrace tailWord_840356 prefixEnd_840356 431506548889819336985279 := by
  unfold tailWord_840356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325150671770604111794461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20433534229027472149059281 15325150671770604111794461)
  ·
    refine ⟨5746931501913976541922923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15325150671770604111794461 5746931501913976541922923)
    ·
      refine ⟨8620397252870964812884385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746931501913976541922923 8620397252870964812884385)
      ·
        refine ⟨6465297939653223609663289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8620397252870964812884385 6465297939653223609663289)
        ·
          refine ⟨4848973454739917707247467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465297939653223609663289 4848973454739917707247467)
          ·
            refine ⟨7273460182109876560871201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848973454739917707247467 7273460182109876560871201)
            ·
              refine ⟨5455095136582407420653401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273460182109876560871201 5455095136582407420653401)
              ·
                refine ⟨4091321352436805565490051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455095136582407420653401 4091321352436805565490051)
                ·
                  refine ⟨6136982028655208348235077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091321352436805565490051 6136982028655208348235077)
                  ·
                    refine ⟨1150684130372851565294077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6136982028655208348235077 1150684130372851565294077)
                    ·
                      refine ⟨431506548889819336985279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150684130372851565294077 431506548889819336985279)
                      ·
                        rfl

theorem cell23_840356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_840356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840356 prefixEnd_840356 := by exact prefixLift 840356
  have htrace : WordTrace (prefixWord ++ tailWord_840356) baseStart_840356 baseEnd_840356 := by
    simpa [prefixWord, tailWord_840356, baseEnd_840356] using wordTrace_append hprefix tailTrace_840356
  have hstable : (prefixWord ++ tailWord_840356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840356).length < 2 ^ (prefixWord ++ tailWord_840356).sum := by decide
  have hdescent : baseEnd_840356 < baseStart_840356 := by decide
  rcases family_descends (prefixWord ++ tailWord_840356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840373 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_840373 : Nat := 118140960795 + 840373 * 2 ^ 59
def prefixEnd_840373 : Nat := 4983230072969 + 3 ^ 40 * 840373 * 2
def baseEnd_840373 : Nat := 431515278060945770472701

theorem tailTrace_840373 : CollatzResearch.WordTrace tailWord_840373 prefixEnd_840373 431515278060945770472701 := by
  unfold tailWord_840373
  simp only [CollatzResearch.WordTrace]
  refine ⟨30650921384479620126957773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20433947589653080084638515 30650921384479620126957773)
  ·
    refine ⟨11494095519179857547609165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30650921384479620126957773 11494095519179857547609165)
    ·
      refine ⟨4310285819692446580353437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11494095519179857547609165 4310285819692446580353437)
      ·
        refine ⟨1616357182384667467632539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4310285819692446580353437 1616357182384667467632539)
        ·
          refine ⟨2424535773577001201448809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616357182384667467632539 2424535773577001201448809)
          ·
            refine ⟨1818401830182750901086607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424535773577001201448809 1818401830182750901086607)
            ·
              refine ⟨2727602745274126351629911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818401830182750901086607 2727602745274126351629911)
              ·
                refine ⟨4091404117911189527444867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727602745274126351629911 4091404117911189527444867)
                ·
                  refine ⟨6137106176866784291167301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091404117911189527444867 6137106176866784291167301)
                  ·
                    refine ⟨1150707408162522054593869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6137106176866784291167301 1150707408162522054593869)
                    ·
                      refine ⟨431515278060945770472701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150707408162522054593869 431515278060945770472701)
                      ·
                        rfl

theorem cell23_840373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_840373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840373 prefixEnd_840373 := by exact prefixLift 840373
  have htrace : WordTrace (prefixWord ++ tailWord_840373) baseStart_840373 baseEnd_840373 := by
    simpa [prefixWord, tailWord_840373, baseEnd_840373] using wordTrace_append hprefix tailTrace_840373
  have hstable : (prefixWord ++ tailWord_840373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840373).length < 2 ^ (prefixWord ++ tailWord_840373).sum := by decide
  have hdescent : baseEnd_840373 < baseStart_840373 := by decide
  rcases family_descends (prefixWord ++ tailWord_840373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840380 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_840380 : Nat := 118140960795 + 840380 * 2 ^ 59
def prefixEnd_840380 : Nat := 4983230072969 + 3 ^ 40 * 840380 * 2
def baseEnd_840380 : Nat := 143839624141842414361723

theorem tailTrace_840380 : CollatzResearch.WordTrace tailWord_840380 prefixEnd_840380 143839624141842414361723 := by
  unfold tailWord_840380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325588347727130161231297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20434117796969506881641729 15325588347727130161231297)
  ·
    refine ⟨11494191260795347620923473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15325588347727130161231297 11494191260795347620923473)
    ·
      refine ⟨8620643445596510715692605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11494191260795347620923473 8620643445596510715692605)
      ·
        refine ⟨3232741292098691518384727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8620643445596510715692605 3232741292098691518384727)
        ·
          refine ⟨4849111938148037277577091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232741292098691518384727 4849111938148037277577091)
          ·
            refine ⟨7273667907222055916365637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849111938148037277577091 7273667907222055916365637)
            ·
              refine ⟨1363812732604135484318557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7273667907222055916365637 1363812732604135484318557)
              ·
                refine ⟨511429774726550806619459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363812732604135484318557 511429774726550806619459)
                ·
                  refine ⟨767144662089826209929189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511429774726550806619459 767144662089826209929189)
                  ·
                    refine ⟨143839624141842414361723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767144662089826209929189 143839624141842414361723)
                    ·
                      rfl

theorem cell23_840380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_840380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840380 prefixEnd_840380 := by exact prefixLift 840380
  have htrace : WordTrace (prefixWord ++ tailWord_840380) baseStart_840380 baseEnd_840380 := by
    simpa [prefixWord, tailWord_840380, baseEnd_840380] using wordTrace_append hprefix tailTrace_840380
  have hstable : (prefixWord ++ tailWord_840380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840380).length < 2 ^ (prefixWord ++ tailWord_840380).sum := by decide
  have hdescent : baseEnd_840380 < baseStart_840380 := by decide
  rcases family_descends (prefixWord ++ tailWord_840380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840396 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_840396 : Nat := 118140960795 + 840396 * 2 ^ 59
def prefixEnd_840396 : Nat := 4983230072969 + 3 ^ 40 * 840396 * 2
def baseEnd_840396 : Nat := 431527088115999180485095

theorem tailTrace_840396 : CollatzResearch.WordTrace tailWord_840396 prefixEnd_840396 431527088115999180485095 := by
  unfold tailWord_840396
  simp only [CollatzResearch.WordTrace]
  refine ⟨15325880131698147527522521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20434506842264196703363361 15325880131698147527522521)
  ·
    refine ⟨11494410098773610645641891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15325880131698147527522521 11494410098773610645641891)
    ·
      refine ⟨17241615148160415968462837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494410098773610645641891 17241615148160415968462837)
      ·
        refine ⟨1616401420140038997043391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17241615148160415968462837 1616401420140038997043391)
        ·
          refine ⟨2424602130210058495565087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616401420140038997043391 2424602130210058495565087)
          ·
            refine ⟨3636903195315087743347631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424602130210058495565087 3636903195315087743347631)
            ·
              refine ⟨5455354792972631615021447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636903195315087743347631 5455354792972631615021447)
              ·
                refine ⟨8183032189458947422532171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455354792972631615021447 8183032189458947422532171)
                ·
                  refine ⟨12274548284188421133798257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8183032189458947422532171 12274548284188421133798257)
                  ·
                    refine ⟨9205911213141315850348693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12274548284188421133798257 9205911213141315850348693)
                    ·
                      refine ⟨431527088115999180485095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9205911213141315850348693 431527088115999180485095)
                      ·
                        rfl

theorem cell23_840396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_840396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840396 prefixEnd_840396 := by exact prefixLift 840396
  have htrace : WordTrace (prefixWord ++ tailWord_840396) baseStart_840396 baseEnd_840396 := by
    simpa [prefixWord, tailWord_840396, baseEnd_840396] using wordTrace_append hprefix tailTrace_840396
  have hstable : (prefixWord ++ tailWord_840396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840396).length < 2 ^ (prefixWord ++ tailWord_840396).sum := by decide
  have hdescent : baseEnd_840396 < baseStart_840396 := by decide
  rcases family_descends (prefixWord ++ tailWord_840396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840397 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_840397 : Nat := 118140960795 + 840397 * 2 ^ 59
def prefixEnd_840397 : Nat := 4983230072969 + 3 ^ 40 * 840397 * 2
def baseEnd_840397 : Nat := 143842533865551225524197

theorem tailTrace_840397 : CollatzResearch.WordTrace tailWord_840397 prefixEnd_840397 143842533865551225524197 := by
  unfold tailWord_840397
  simp only [CollatzResearch.WordTrace]
  refine ⟨30651796736392672225831445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20434531157595114817220963 30651796736392672225831445)
  ·
    refine ⟨1436802972018406510585849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30651796736392672225831445 1436802972018406510585849)
    ·
      refine ⟨1077602229013804882939387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436802972018406510585849 1077602229013804882939387)
      ·
        refine ⟨1616403343520707324409081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077602229013804882939387 1616403343520707324409081)
        ·
          refine ⟨1212302507640530493306811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616403343520707324409081 1212302507640530493306811)
          ·
            refine ⟨1818453761460795739960217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212302507640530493306811 1818453761460795739960217)
            ·
              refine ⟨1363840321095596804970163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818453761460795739960217 1363840321095596804970163)
              ·
                refine ⟨2045760481643395207455245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363840321095596804970163 2045760481643395207455245)
                ·
                  refine ⟨767160180616273202795717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2045760481643395207455245 767160180616273202795717)
                  ·
                    refine ⟨143842533865551225524197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767160180616273202795717 143842533865551225524197)
                    ·
                      rfl

theorem cell23_840397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_840397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840397 prefixEnd_840397 := by exact prefixLift 840397
  have htrace : WordTrace (prefixWord ++ tailWord_840397) baseStart_840397 baseEnd_840397 := by
    simpa [prefixWord, tailWord_840397, baseEnd_840397] using wordTrace_append hprefix tailTrace_840397
  have hstable : (prefixWord ++ tailWord_840397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840397).length < 2 ^ (prefixWord ++ tailWord_840397).sum := by decide
  have hdescent : baseEnd_840397 < baseStart_840397 := by decide
  rcases family_descends (prefixWord ++ tailWord_840397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840456 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_840456 : Nat := 118140960795 + 840456 * 2 ^ 59
def prefixEnd_840456 : Nat := 4983230072969 + 3 ^ 40 * 840456 * 2
def baseEnd_840456 : Nat := 431557896955268945734819

theorem tailTrace_840456 : CollatzResearch.WordTrace tailWord_840456 prefixEnd_840456 431557896955268945734819 := by
  unfold tailWord_840456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15326974321589462651114611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20435965762119283534819481 15326974321589462651114611)
  ·
    refine ⟨22990461482384193976671917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15326974321589462651114611 22990461482384193976671917)
    ·
      refine ⟨8621423055894072741251969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22990461482384193976671917 8621423055894072741251969)
      ·
        refine ⟨6466067291920554555938977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8621423055894072741251969 6466067291920554555938977)
        ·
          refine ⟨4849550468940415916954233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466067291920554555938977 4849550468940415916954233)
          ·
            refine ⟨3637162851705311937715675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849550468940415916954233 3637162851705311937715675)
            ·
              refine ⟨5455744277557967906573513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637162851705311937715675 5455744277557967906573513)
              ·
                refine ⟨4091808208168475929930135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455744277557967906573513 4091808208168475929930135)
                ·
                  refine ⟨6137712312252713894895203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091808208168475929930135 6137712312252713894895203)
                  ·
                    refine ⟨9206568468379070842342805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6137712312252713894895203 9206568468379070842342805)
                    ·
                      refine ⟨431557896955268945734819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9206568468379070842342805 431557896955268945734819)
                      ·
                        rfl

theorem cell23_840456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_840456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840456 prefixEnd_840456 := by exact prefixLift 840456
  have htrace : WordTrace (prefixWord ++ tailWord_840456) baseStart_840456 baseEnd_840456 := by
    simpa [prefixWord, tailWord_840456, baseEnd_840456] using wordTrace_append hprefix tailTrace_840456
  have hstable : (prefixWord ++ tailWord_840456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840456).length < 2 ^ (prefixWord ++ tailWord_840456).sum := by decide
  have hdescent : baseEnd_840456 < baseStart_840456 := by decide
  rcases family_descends (prefixWord ++ tailWord_840456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840480 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_840480 : Nat := 118140960795 + 840480 * 2 ^ 59
def prefixEnd_840480 : Nat := 4983230072969 + 3 ^ 40 * 840480 * 2
def baseEnd_840480 : Nat := 431570220490976851834709

theorem tailTrace_840480 : CollatzResearch.WordTrace tailWord_840480 prefixEnd_840480 431570220490976851834709 := by
  unfold tailWord_840480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327411997545988700551447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20436549330061318267401929 15327411997545988700551447)
  ·
    refine ⟨22991117996318983050827171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327411997545988700551447 22991117996318983050827171)
    ·
      refine ⟨34486676994478474576240757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991117996318983050827171 34486676994478474576240757)
      ·
        refine ⟨3233125968232356991522571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34486676994478474576240757 3233125968232356991522571)
        ·
          refine ⟨4849688952348535487283857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233125968232356991522571 4849688952348535487283857)
          ·
            refine ⟨3637266714261401615462893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849688952348535487283857 3637266714261401615462893)
            ·
              refine ⟨1363975017848025605798585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3637266714261401615462893 1363975017848025605798585)
              ·
                refine ⟨1022981263386019204348939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363975017848025605798585 1022981263386019204348939)
                ·
                  refine ⟨1534471895079028806523409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022981263386019204348939 1534471895079028806523409)
                  ·
                    refine ⟨1150853921309271604892557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1534471895079028806523409 1150853921309271604892557)
                    ·
                      refine ⟨431570220490976851834709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150853921309271604892557 431570220490976851834709)
                      ·
                        rfl

theorem cell23_840480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_840480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840480 prefixEnd_840480 := by exact prefixLift 840480
  have htrace : WordTrace (prefixWord ++ tailWord_840480) baseStart_840480 baseEnd_840480 := by
    simpa [prefixWord, tailWord_840480, baseEnd_840480] using wordTrace_append hprefix tailTrace_840480
  have hstable : (prefixWord ++ tailWord_840480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840480).length < 2 ^ (prefixWord ++ tailWord_840480).sum := by decide
  have hdescent : baseEnd_840480 < baseStart_840480 := by decide
  rcases family_descends (prefixWord ++ tailWord_840480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840511 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 1, 2, 2]
def baseStart_840511 : Nat := 118140960795 + 840511 * 2 ^ 59
def prefixEnd_840511 : Nat := 4983230072969 + 3 ^ 40 * 840511 * 2
def baseEnd_840511 : Nat := 431586138391266230547067

theorem tailTrace_840511 : CollatzResearch.WordTrace tailWord_840511 prefixEnd_840511 431586138391266230547067 := by
  unfold tailWord_840511
  simp only [CollatzResearch.WordTrace]
  refine ⟨30655954657979669695481387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20437303105319779796987591 30655954657979669695481387)
  ·
    refine ⟨45983931986969504543222081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30655954657979669695481387 45983931986969504543222081)
    ·
      refine ⟨34487948990227128407416561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45983931986969504543222081 34487948990227128407416561)
      ·
        refine ⟨25865961742670346305562421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34487948990227128407416561 25865961742670346305562421)
        ·
          refine ⟨2424933913375344966146477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25865961742670346305562421 2424933913375344966146477)
          ·
            refine ⟨909350217515754362304929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2424933913375344966146477 909350217515754362304929)
            ·
              refine ⟨682012663136815771728697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909350217515754362304929 682012663136815771728697)
              ·
                refine ⟨511509497352611828796523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682012663136815771728697 511509497352611828796523)
                ·
                  refine ⟨767264246028917743194785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511509497352611828796523 767264246028917743194785)
                  ·
                    refine ⟨575448184521688307396089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767264246028917743194785 575448184521688307396089)
                    ·
                      refine ⟨431586138391266230547067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575448184521688307396089 431586138391266230547067)
                      ·
                        rfl

theorem cell23_840511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_840511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840511 prefixEnd_840511 := by exact prefixLift 840511
  have htrace : WordTrace (prefixWord ++ tailWord_840511) baseStart_840511 baseEnd_840511 := by
    simpa [prefixWord, tailWord_840511, baseEnd_840511] using wordTrace_append hprefix tailTrace_840511
  have hstable : (prefixWord ++ tailWord_840511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840511).length < 2 ^ (prefixWord ++ tailWord_840511).sum := by decide
  have hdescent : baseEnd_840511 < baseStart_840511 := by decide
  rcases family_descends (prefixWord ++ tailWord_840511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_840536 : Nat := 118140960795 + 840536 * 2 ^ 59
def prefixEnd_840536 : Nat := 4983230072969 + 3 ^ 40 * 840536 * 2
def baseEnd_840536 : Nat := 431598975407628632734451

theorem tailTrace_840536 : CollatzResearch.WordTrace tailWord_840536 prefixEnd_840536 431598975407628632734451 := by
  unfold tailWord_840536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328433241444549482570731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20437910988592732643427641 15328433241444549482570731)
  ·
    refine ⟨22992649862166824223856097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15328433241444549482570731 22992649862166824223856097)
    ·
      refine ⟨17244487396625118167892073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22992649862166824223856097 17244487396625118167892073)
      ·
        refine ⟨12933365547468838625919055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17244487396625118167892073 12933365547468838625919055)
        ·
          refine ⟨19400048321203257938878583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933365547468838625919055 19400048321203257938878583)
          ·
            refine ⟨29100072481804886908317875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400048321203257938878583 29100072481804886908317875)
            ·
              refine ⟨43650108722707330362476813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29100072481804886908317875 43650108722707330362476813)
              ·
                refine ⟨16368790771015248885928805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43650108722707330362476813 16368790771015248885928805)
                ·
                  refine ⟨3069148269565359166111651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16368790771015248885928805 3069148269565359166111651)
                  ·
                    refine ⟨4603722404348038749167477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3069148269565359166111651 4603722404348038749167477)
                    ·
                      refine ⟨431598975407628632734451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4603722404348038749167477 431598975407628632734451)
                      ·
                        rfl

theorem cell23_840536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_840536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840536 prefixEnd_840536 := by exact prefixLift 840536
  have htrace : WordTrace (prefixWord ++ tailWord_840536) baseStart_840536 baseEnd_840536 := by
    simpa [prefixWord, tailWord_840536, baseEnd_840536] using wordTrace_append hprefix tailTrace_840536
  have hstable : (prefixWord ++ tailWord_840536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840536).length < 2 ^ (prefixWord ++ tailWord_840536).sum := by decide
  have hdescent : baseEnd_840536 < baseStart_840536 := by decide
  rcases family_descends (prefixWord ++ tailWord_840536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840556 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 9]
def baseStart_840556 : Nat := 118140960795 + 840556 * 2 ^ 59
def prefixEnd_840556 : Nat := 4983230072969 + 3 ^ 40 * 840556 * 2
def baseEnd_840556 : Nat := 47956582780079839387151

theorem tailTrace_840556 : CollatzResearch.WordTrace tailWord_840556 prefixEnd_840556 47956582780079839387151 := by
  unfold tailWord_840556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328797971408321190434761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20438397295211094920579681 15328797971408321190434761)
  ·
    refine ⟨11496598478556240892826071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15328797971408321190434761 11496598478556240892826071)
    ·
      refine ⟨17244897717834361339239107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11496598478556240892826071 17244897717834361339239107)
      ·
        refine ⟨25867346576751542008858661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17244897717834361339239107 25867346576751542008858661)
        ·
          refine ⟨4850127483140914126660999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25867346576751542008858661 4850127483140914126660999)
          ·
            refine ⟨7275191224711371189991499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850127483140914126660999 7275191224711371189991499)
            ·
              refine ⟨10912786837067056784987249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275191224711371189991499 10912786837067056784987249)
              ·
                refine ⟨8184590127800292588740437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912786837067056784987249 8184590127800292588740437)
                ·
                  refine ⟨47956582780079839387151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8184590127800292588740437 47956582780079839387151)
                  ·
                    rfl

theorem cell23_840556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_840556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840556 prefixEnd_840556 := by exact prefixLift 840556
  have htrace : WordTrace (prefixWord ++ tailWord_840556) baseStart_840556 baseEnd_840556 := by
    simpa [prefixWord, tailWord_840556, baseEnd_840556] using wordTrace_append hprefix tailTrace_840556
  have hstable : (prefixWord ++ tailWord_840556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840556).length < 2 ^ (prefixWord ++ tailWord_840556).sum := by decide
  have hdescent : baseEnd_840556 < baseStart_840556 := by decide
  rcases family_descends (prefixWord ++ tailWord_840556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840578 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_840578 : Nat := 118140960795 + 840578 * 2 ^ 59
def prefixEnd_840578 : Nat := 4983230072969 + 3 ^ 40 * 840578 * 2
def baseEnd_840578 : Nat := 431620541595117468409259

theorem tailTrace_840578 : CollatzResearch.WordTrace tailWord_840578 prefixEnd_840578 431620541595117468409259 := by
  unfold tailWord_840578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664599587184235034542597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20438932232491293425446925 7664599587184235034542597)
  ·
    refine ⟨1437112422597044068976737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7664599587184235034542597 1437112422597044068976737)
    ·
      refine ⟨1077834316947783051732553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437112422597044068976737 1077834316947783051732553)
      ·
        refine ⟨808375737710837288799415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077834316947783051732553 808375737710837288799415)
        ·
          refine ⟨1212563606566255933199123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808375737710837288799415 1212563606566255933199123)
          ·
            refine ⟨1818845409849383899798685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212563606566255933199123 1818845409849383899798685)
            ·
              refine ⟨682067028693518962424507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818845409849383899798685 682067028693518962424507)
              ·
                refine ⟨1023100543040278443636761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682067028693518962424507 1023100543040278443636761)
                ·
                  refine ⟨767325407280208832727571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1023100543040278443636761 767325407280208832727571)
                  ·
                    refine ⟨1150988110920313249091357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 767325407280208832727571 1150988110920313249091357)
                    ·
                      refine ⟨431620541595117468409259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1150988110920313249091357 431620541595117468409259)
                      ·
                        rfl

theorem cell23_840578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_840578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840578 prefixEnd_840578 := by exact prefixLift 840578
  have htrace : WordTrace (prefixWord ++ tailWord_840578) baseStart_840578 baseEnd_840578 := by
    simpa [prefixWord, tailWord_840578, baseEnd_840578] using wordTrace_append hprefix tailTrace_840578
  have hstable : (prefixWord ++ tailWord_840578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840578).length < 2 ^ (prefixWord ++ tailWord_840578).sum := by decide
  have hdescent : baseEnd_840578 < baseStart_840578 := by decide
  rcases family_descends (prefixWord ++ tailWord_840578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840607 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 5]
def baseStart_840607 : Nat := 118140960795 + 840607 * 2 ^ 59
def prefixEnd_840607 : Nat := 4983230072969 + 3 ^ 40 * 840607 * 2
def baseEnd_840607 : Nat := 47959492503788650549625

theorem tailTrace_840607 : CollatzResearch.WordTrace tailWord_840607 prefixEnd_840607 47959492503788650549625 := by
  unfold tailWord_840607
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659456065631878090976075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20439637377087918727317383 30659456065631878090976075)
  ·
    refine ⟨45989184098447817136464113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30659456065631878090976075 45989184098447817136464113)
    ·
      refine ⟨34491888073835862852348085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45989184098447817136464113 34491888073835862852348085)
      ·
        refine ⟨3233614506922112142407633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34491888073835862852348085 3233614506922112142407633)
        ·
          refine ⟨2425210880191584106805725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233614506922112142407633 2425210880191584106805725)
          ·
            refine ⟨909454080071844040052147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2425210880191584106805725 909454080071844040052147)
            ·
              refine ⟨1364181120107766060078221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909454080071844040052147 1364181120107766060078221)
              ·
                refine ⟨511567920040412272529333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1364181120107766060078221 511567920040412272529333)
                ·
                  refine ⟨47959492503788650549625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 511567920040412272529333 47959492503788650549625)
                  ·
                    rfl

theorem cell23_840607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 5].length) (baseStart_840607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840607 prefixEnd_840607 := by exact prefixLift 840607
  have htrace : WordTrace (prefixWord ++ tailWord_840607) baseStart_840607 baseEnd_840607 := by
    simpa [prefixWord, tailWord_840607, baseEnd_840607] using wordTrace_append hprefix tailTrace_840607
  have hstable : (prefixWord ++ tailWord_840607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840607).length < 2 ^ (prefixWord ++ tailWord_840607).sum := by decide
  have hdescent : baseEnd_840607 < baseStart_840607 := by decide
  rcases family_descends (prefixWord ++ tailWord_840607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840727 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 1, 5]
def baseStart_840727 : Nat := 118140960795 + 840727 * 2 ^ 59
def prefixEnd_840727 : Nat := 4983230072969 + 3 ^ 40 * 840727 * 2
def baseEnd_840727 : Nat := 143899016737545795148691

theorem tailTrace_840727 : CollatzResearch.WordTrace tailWord_840727 prefixEnd_840727 143899016737545795148691 := by
  unfold tailWord_840727
  simp only [CollatzResearch.WordTrace]
  refine ⟨30663832825197138585344435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20442555216798092390229623 30663832825197138585344435)
  ·
    refine ⟨45995749237795707878016653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30663832825197138585344435 45995749237795707878016653)
    ·
      refine ⟨17248405964173390454256245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45995749237795707878016653 17248405964173390454256245)
      ·
        refine ⟨1617038059141255355086523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17248405964173390454256245 1617038059141255355086523)
        ·
          refine ⟨2425557088711883032629785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617038059141255355086523 2425557088711883032629785)
          ·
            refine ⟨1819167816533912274472339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425557088711883032629785 1819167816533912274472339)
            ·
              refine ⟨2728751724800868411708509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819167816533912274472339 2728751724800868411708509)
              ·
                refine ⟨1023281896800325654390691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2728751724800868411708509 1023281896800325654390691)
                ·
                  refine ⟨1534922845200488481586037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023281896800325654390691 1534922845200488481586037)
                  ·
                    refine ⟨143899016737545795148691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1534922845200488481586037 143899016737545795148691)
                    ·
                      rfl

theorem cell23_840727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_840727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840727 prefixEnd_840727 := by exact prefixLift 840727
  have htrace : WordTrace (prefixWord ++ tailWord_840727) baseStart_840727 baseEnd_840727 := by
    simpa [prefixWord, tailWord_840727, baseEnd_840727] using wordTrace_append hprefix tailTrace_840727
  have hstable : (prefixWord ++ tailWord_840727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840727).length < 2 ^ (prefixWord ++ tailWord_840727).sum := by decide
  have hdescent : baseEnd_840727 < baseStart_840727 := by decide
  rcases family_descends (prefixWord ++ tailWord_840727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840753 : List Nat := [1, 2, 2, 3, 1, 2, 2, 10]
def baseStart_840753 : Nat := 118140960795 + 840753 * 2 ^ 59
def prefixEnd_840753 : Nat := 4983230072969 + 3 ^ 40 * 840753 * 2
def baseEnd_840753 : Nat := 15989274100357566063739

theorem tailTrace_840753 : CollatzResearch.WordTrace tailWord_840753 prefixEnd_840753 15989274100357566063739 := by
  unfold tailWord_840753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664781123102945025790913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20443187415401963350527275 30664781123102945025790913)
  ·
    refine ⟨22998585842327208769343185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30664781123102945025790913 22998585842327208769343185)
    ·
      refine ⟨17248939381745406577007389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22998585842327208769343185 17248939381745406577007389)
      ·
        refine ⟨6468352268154527466377771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17248939381745406577007389 6468352268154527466377771)
        ·
          refine ⟨9702528402231791199566657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468352268154527466377771 9702528402231791199566657)
          ·
            refine ⟨7276896301673843399674993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9702528402231791199566657 7276896301673843399674993)
            ·
              refine ⟨5457672226255382549756245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276896301673843399674993 5457672226255382549756245)
              ·
                refine ⟨15989274100357566063739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5457672226255382549756245 15989274100357566063739)
                ·
                  rfl

theorem cell23_840753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 10].length) (baseStart_840753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840753 prefixEnd_840753 := by exact prefixLift 840753
  have htrace : WordTrace (prefixWord ++ tailWord_840753) baseStart_840753 baseEnd_840753 := by
    simpa [prefixWord, tailWord_840753, baseEnd_840753] using wordTrace_append hprefix tailTrace_840753
  have hstable : (prefixWord ++ tailWord_840753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840753).length < 2 ^ (prefixWord ++ tailWord_840753).sum := by decide
  have hdescent : baseEnd_840753 < baseStart_840753 := by decide
  rcases family_descends (prefixWord ++ tailWord_840753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840760 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_840760 : Nat := 118140960795 + 840760 * 2 ^ 59
def prefixEnd_840760 : Nat := 4983230072969 + 3 ^ 40 * 840760 * 2
def baseEnd_840760 : Nat := 431713995074235756333421

theorem tailTrace_840760 : CollatzResearch.WordTrace tailWord_840760 prefixEnd_840760 431713995074235756333421 := by
  unfold tailWord_840760
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332518217038792610647867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20443357622718390147530489 15332518217038792610647867)
  ·
    refine ⟨22998777325558188915971801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332518217038792610647867 22998777325558188915971801)
    ·
      refine ⟨17249082994168641686978851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22998777325558188915971801 17249082994168641686978851)
      ·
        refine ⟨25873624491252962530468277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17249082994168641686978851 25873624491252962530468277)
        ·
          refine ⟨2425652296054965237231401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25873624491252962530468277 2425652296054965237231401)
          ·
            refine ⟨1819239222041223927923551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425652296054965237231401 1819239222041223927923551)
            ·
              refine ⟨2728858833061835891885327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819239222041223927923551 2728858833061835891885327)
              ·
                refine ⟨4093288249592753837827991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728858833061835891885327 4093288249592753837827991)
                ·
                  refine ⟨6139932374389130756741987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093288249592753837827991 6139932374389130756741987)
                  ·
                    refine ⟨9209898561583696135112981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139932374389130756741987 9209898561583696135112981)
                    ·
                      refine ⟨431713995074235756333421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9209898561583696135112981 431713995074235756333421)
                      ·
                        rfl

theorem cell23_840760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_840760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840760 prefixEnd_840760 := by exact prefixLift 840760
  have htrace : WordTrace (prefixWord ++ tailWord_840760) baseStart_840760 baseEnd_840760 := by
    simpa [prefixWord, tailWord_840760, baseEnd_840760] using wordTrace_append hprefix tailTrace_840760
  have hstable : (prefixWord ++ tailWord_840760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840760).length < 2 ^ (prefixWord ++ tailWord_840760).sum := by decide
  have hdescent : baseEnd_840760 < baseStart_840760 := by decide
  rcases family_descends (prefixWord ++ tailWord_840760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840764 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_840764 : Nat := 118140960795 + 840764 * 2 ^ 59
def prefixEnd_840764 : Nat := 4983230072969 + 3 ^ 40 * 840764 * 2
def baseEnd_840764 : Nat := 431716048996853740683403

theorem tailTrace_840764 : CollatzResearch.WordTrace tailWord_840764 prefixEnd_840764 431716048996853740683403 := by
  unfold tailWord_840764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332591163031546952220673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20443454884042062602960897 15332591163031546952220673)
  ·
    refine ⟨11499443372273660214165505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15332591163031546952220673 11499443372273660214165505)
    ·
      refine ⟨8624582529205245160624129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11499443372273660214165505 8624582529205245160624129)
      ·
        refine ⟨6468436896903933870468097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8624582529205245160624129 6468436896903933870468097)
        ·
          refine ⟨4851327672677950402851073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468436896903933870468097 4851327672677950402851073)
          ·
            refine ⟨3638495754508462802138305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851327672677950402851073 3638495754508462802138305)
            ·
              refine ⟨2728871815881347101603729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638495754508462802138305 2728871815881347101603729)
              ·
                refine ⟨2046653861911010326202797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728871815881347101603729 2046653861911010326202797)
                ·
                  refine ⟨767495198216628872326049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2046653861911010326202797 767495198216628872326049)
                  ·
                    refine ⟨575621398662471654244537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767495198216628872326049 575621398662471654244537)
                    ·
                      refine ⟨431716048996853740683403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575621398662471654244537 431716048996853740683403)
                      ·
                        rfl

theorem cell23_840764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_840764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840764 prefixEnd_840764 := by exact prefixLift 840764
  have htrace : WordTrace (prefixWord ++ tailWord_840764) baseStart_840764 baseEnd_840764 := by
    simpa [prefixWord, tailWord_840764, baseEnd_840764] using wordTrace_append hprefix tailTrace_840764
  have hstable : (prefixWord ++ tailWord_840764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840764).length < 2 ^ (prefixWord ++ tailWord_840764).sum := by decide
  have hdescent : baseEnd_840764 < baseStart_840764 := by decide
  rcases family_descends (prefixWord ++ tailWord_840764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840774 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_840774 : Nat := 118140960795 + 840774 * 2 ^ 59
def prefixEnd_840774 : Nat := 4983230072969 + 3 ^ 40 * 840774 * 2
def baseEnd_840774 : Nat := 143907061267799567186119

theorem tailTrace_840774 : CollatzResearch.WordTrace tailWord_840774 prefixEnd_840774 143907061267799567186119 := by
  unfold tailWord_840774
  simp only [CollatzResearch.WordTrace]
  refine ⟨958298345500839550384543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20443698037351243741536917 958298345500839550384543)
  ·
    refine ⟨1437447518251259325576815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958298345500839550384543 1437447518251259325576815)
    ·
      refine ⟨2156171277376888988365223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437447518251259325576815 2156171277376888988365223)
      ·
        refine ⟨3234256916065333482547835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156171277376888988365223 3234256916065333482547835)
        ·
          refine ⟨4851385374098000223821753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234256916065333482547835 4851385374098000223821753)
          ·
            refine ⟨3638539030573500167866315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851385374098000223821753 3638539030573500167866315)
            ·
              refine ⟨5457808545860250251799473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638539030573500167866315 5457808545860250251799473)
              ·
                refine ⟨4093356409395187688849605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457808545860250251799473 4093356409395187688849605)
                ·
                  refine ⟨767504326761597691659301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4093356409395187688849605 767504326761597691659301)
                  ·
                    refine ⟨143907061267799567186119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767504326761597691659301 143907061267799567186119)
                    ·
                      rfl

theorem cell23_840774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_840774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840774 prefixEnd_840774 := by exact prefixLift 840774
  have htrace : WordTrace (prefixWord ++ tailWord_840774) baseStart_840774 baseEnd_840774 := by
    simpa [prefixWord, tailWord_840774, baseEnd_840774] using wordTrace_append hprefix tailTrace_840774
  have hstable : (prefixWord ++ tailWord_840774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840774).length < 2 ^ (prefixWord ++ tailWord_840774).sum := by decide
  have hdescent : baseEnd_840774 < baseStart_840774 := by decide
  rcases family_descends (prefixWord ++ tailWord_840774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840780 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_840780 : Nat := 118140960795 + 840780 * 2 ^ 59
def prefixEnd_840780 : Nat := 4983230072969 + 3 ^ 40 * 840780 * 2
def baseEnd_840780 : Nat := 431724264687325678083329

theorem tailTrace_840780 : CollatzResearch.WordTrace tailWord_840780 prefixEnd_840780 431724264687325678083329 := by
  unfold tailWord_840780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332882947002564318511897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20443843929336752424682529 15332882947002564318511897)
  ·
    refine ⟨11499662210251923238883923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15332882947002564318511897 11499662210251923238883923)
    ·
      refine ⟨17249493315377884858325885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11499662210251923238883923 17249493315377884858325885)
      ·
        refine ⟨6468559993266706821872207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17249493315377884858325885 6468559993266706821872207)
        ·
          refine ⟨9702839989900060232808311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468559993266706821872207 9702839989900060232808311)
          ·
            refine ⟨14554259984850090349212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702839989900060232808311 14554259984850090349212467)
            ·
              refine ⟨21831389977275135523818701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14554259984850090349212467 21831389977275135523818701)
              ·
                refine ⟨8186771241478175821432013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21831389977275135523818701 8186771241478175821432013)
                ·
                  refine ⟨3070039215554315933037005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8186771241478175821432013 3070039215554315933037005)
                  ·
                    refine ⟨1151264705832868474888877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070039215554315933037005 1151264705832868474888877)
                    ·
                      refine ⟨431724264687325678083329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1151264705832868474888877 431724264687325678083329)
                      ·
                        rfl

theorem cell23_840780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_840780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840780 prefixEnd_840780 := by exact prefixLift 840780
  have htrace : WordTrace (prefixWord ++ tailWord_840780) baseStart_840780 baseEnd_840780 := by
    simpa [prefixWord, tailWord_840780, baseEnd_840780] using wordTrace_append hprefix tailTrace_840780
  have hstable : (prefixWord ++ tailWord_840780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840780).length < 2 ^ (prefixWord ++ tailWord_840780).sum := by decide
  have hdescent : baseEnd_840780 < baseStart_840780 := by decide
  rcases family_descends (prefixWord ++ tailWord_840780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840808 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 2, 4]
def baseStart_840808 : Nat := 118140960795 + 840808 * 2 ^ 59
def prefixEnd_840808 : Nat := 4983230072969 + 3 ^ 40 * 840808 * 2
def baseEnd_840808 : Nat := 143912880715217189511067

theorem tailTrace_840808 : CollatzResearch.WordTrace tailWord_840808 prefixEnd_840808 143912880715217189511067 := by
  unfold tailWord_840808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333393568951844709521539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20444524758602459612695385 15333393568951844709521539)
  ·
    refine ⟨23000090353427767064282309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333393568951844709521539 23000090353427767064282309)
    ·
      refine ⟨4312516941267706324552933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23000090353427767064282309 4312516941267706324552933)
      ·
        refine ⟨808596926487694935853675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4312516941267706324552933 808596926487694935853675)
        ·
          refine ⟨1212895389731542403780513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808596926487694935853675 1212895389731542403780513)
          ·
            refine ⟨909671542298656802835385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212895389731542403780513 909671542298656802835385)
            ·
              refine ⟨682253656723992602126539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909671542298656802835385 682253656723992602126539)
              ·
                refine ⟨1023380485085988903189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682253656723992602126539 1023380485085988903189809)
                ·
                  refine ⟨767535363814491677392357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1023380485085988903189809 767535363814491677392357)
                  ·
                    refine ⟨143912880715217189511067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767535363814491677392357 143912880715217189511067)
                    ·
                      rfl

theorem cell23_840808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_840808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840808 prefixEnd_840808 := by exact prefixLift 840808
  have htrace : WordTrace (prefixWord ++ tailWord_840808) baseStart_840808 baseEnd_840808 := by
    simpa [prefixWord, tailWord_840808, baseEnd_840808] using wordTrace_append hprefix tailTrace_840808
  have hstable : (prefixWord ++ tailWord_840808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840808).length < 2 ^ (prefixWord ++ tailWord_840808).sum := by decide
  have hdescent : baseEnd_840808 < baseStart_840808 := by decide
  rcases family_descends (prefixWord ++ tailWord_840808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840824 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_840824 : Nat := 118140960795 + 840824 * 2 ^ 59
def prefixEnd_840824 : Nat := 4983230072969 + 3 ^ 40 * 840824 * 2
def baseEnd_840824 : Nat := 431746857836123505933127

theorem tailTrace_840824 : CollatzResearch.WordTrace tailWord_840824 prefixEnd_840824 431746857836123505933127 := by
  unfold tailWord_840824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333685352922862075812763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20444913803897149434417017 15333685352922862075812763)
  ·
    refine ⟨23000528029384293113719145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333685352922862075812763 23000528029384293113719145)
    ·
      refine ⟨17250396022038219835289359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23000528029384293113719145 17250396022038219835289359)
      ·
        refine ⟨25875594033057329752934039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17250396022038219835289359 25875594033057329752934039)
        ·
          refine ⟨38813391049585994629401059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875594033057329752934039 38813391049585994629401059)
          ·
            refine ⟨58220086574378991944101589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38813391049585994629401059 58220086574378991944101589)
            ·
              refine ⟨1364533279087007623689881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58220086574378991944101589 1364533279087007623689881)
              ·
                refine ⟨1023399959315255717767411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364533279087007623689881 1023399959315255717767411)
                ·
                  refine ⟨1535099938972883576651117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023399959315255717767411 1535099938972883576651117)
                  ·
                    refine ⟨575662477114831341244169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535099938972883576651117 575662477114831341244169)
                    ·
                      refine ⟨431746857836123505933127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575662477114831341244169 431746857836123505933127)
                      ·
                        rfl

theorem cell23_840824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_840824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840824 prefixEnd_840824 := by exact prefixLift 840824
  have htrace : WordTrace (prefixWord ++ tailWord_840824) baseStart_840824 baseEnd_840824 := by
    simpa [prefixWord, tailWord_840824, baseEnd_840824] using wordTrace_append hprefix tailTrace_840824
  have hstable : (prefixWord ++ tailWord_840824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840824).length < 2 ^ (prefixWord ++ tailWord_840824).sum := by decide
  have hdescent : baseEnd_840824 < baseStart_840824 := by decide
  rcases family_descends (prefixWord ++ tailWord_840824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840841 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 1, 3, 2]
def baseStart_840841 : Nat := 118140960795 + 840841 * 2 ^ 59
def prefixEnd_840841 : Nat := 4983230072969 + 3 ^ 40 * 840841 * 2
def baseEnd_840841 : Nat := 431755587007249939420549

theorem tailTrace_840841 : CollatzResearch.WordTrace tailWord_840841 prefixEnd_840841 431755587007249939420549 := by
  unfold tailWord_840841
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667990746784136054994377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20445327164522757369996251 30667990746784136054994377)
  ·
    refine ⟨23000993060088102041245783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30667990746784136054994377 23000993060088102041245783)
    ·
      refine ⟨34501489590132153061868675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000993060088102041245783 34501489590132153061868675)
      ·
        refine ⟨51752234385198229592803013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34501489590132153061868675 51752234385198229592803013)
        ·
          refine ⟨9703543947224668048650565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51752234385198229592803013 9703543947224668048650565)
          ·
            refine ⟨1819414490104625259121981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9703543947224668048650565 1819414490104625259121981)
            ·
              refine ⟨682280433789234472170743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1819414490104625259121981 682280433789234472170743)
              ·
                refine ⟨1023420650683851708256115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682280433789234472170743 1023420650683851708256115)
                ·
                  refine ⟨1535130976025777562384173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023420650683851708256115 1535130976025777562384173)
                  ·
                    refine ⟨575674116009666585894065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535130976025777562384173 575674116009666585894065)
                    ·
                      refine ⟨431755587007249939420549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575674116009666585894065 431755587007249939420549)
                      ·
                        rfl

theorem cell23_840841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 3, 2].length) (baseStart_840841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840841 prefixEnd_840841 := by exact prefixLift 840841
  have htrace : WordTrace (prefixWord ++ tailWord_840841) baseStart_840841 baseEnd_840841 := by
    simpa [prefixWord, tailWord_840841, baseEnd_840841] using wordTrace_append hprefix tailTrace_840841
  have hstable : (prefixWord ++ tailWord_840841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840841).length < 2 ^ (prefixWord ++ tailWord_840841).sum := by decide
  have hdescent : baseEnd_840841 < baseStart_840841 := by decide
  rcases family_descends (prefixWord ++ tailWord_840841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840871 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_840871 : Nat := 118140960795 + 840871 * 2 ^ 59
def prefixEnd_840871 : Nat := 4983230072969 + 3 ^ 40 * 840871 * 2
def baseEnd_840871 : Nat := 431770991426884822045411

theorem tailTrace_840871 : CollatzResearch.WordTrace tailWord_840871 prefixEnd_840871 431770991426884822045411 := by
  unfold tailWord_840871
  simp only [CollatzResearch.WordTrace]
  refine ⟨30669084936675451178586467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20446056624450300785724311 30669084936675451178586467)
  ·
    refine ⟨46003627405013176767879701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30669084936675451178586467 46003627405013176767879701)
    ·
      refine ⟨2156420034609992660994361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46003627405013176767879701 2156420034609992660994361)
      ·
        refine ⟨1617315025957494495745771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156420034609992660994361 1617315025957494495745771)
        ·
          refine ⟨2425972538936241743618657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617315025957494495745771 2425972538936241743618657)
          ·
            refine ⟨1819479404202181307713993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425972538936241743618657 1819479404202181307713993)
            ·
              refine ⟨1364609553151635980785495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819479404202181307713993 1364609553151635980785495)
              ·
                refine ⟨2046914329727453971178243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364609553151635980785495 2046914329727453971178243)
                ·
                  refine ⟨3070371494591180956767365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046914329727453971178243 3070371494591180956767365)
                  ·
                    refine ⟨575694655235846429393881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070371494591180956767365 575694655235846429393881)
                    ·
                      refine ⟨431770991426884822045411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575694655235846429393881 431770991426884822045411)
                      ·
                        rfl

theorem cell23_840871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_840871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840871 prefixEnd_840871 := by exact prefixLift 840871
  have htrace : WordTrace (prefixWord ++ tailWord_840871) baseStart_840871 baseEnd_840871 := by
    simpa [prefixWord, tailWord_840871, baseEnd_840871] using wordTrace_append hprefix tailTrace_840871
  have hstable : (prefixWord ++ tailWord_840871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840871).length < 2 ^ (prefixWord ++ tailWord_840871).sum := by decide
  have hdescent : baseEnd_840871 < baseStart_840871 := by decide
  rcases family_descends (prefixWord ++ tailWord_840871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840894 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_840894 : Nat := 118140960795 + 840894 * 2 ^ 59
def prefixEnd_840894 : Nat := 4983230072969 + 3 ^ 40 * 840894 * 2
def baseEnd_840894 : Nat := 47975866831326470228645

theorem tailTrace_840894 : CollatzResearch.WordTrace tailWord_840894 prefixEnd_840894 47975866831326470228645 := by
  unfold tailWord_840894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833740476949015763334217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20446615877061417404449157 3833740476949015763334217)
  ·
    refine ⟨2875305357711761822500663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3833740476949015763334217 2875305357711761822500663)
    ·
      refine ⟨4312958036567642733750995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875305357711761822500663 4312958036567642733750995)
      ·
        refine ⟨6469437054851464100626493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312958036567642733750995 6469437054851464100626493)
        ·
          refine ⟨2426038895569299037734935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6469437054851464100626493 2426038895569299037734935)
          ·
            refine ⟨3639058343353948556602403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426038895569299037734935 3639058343353948556602403)
            ·
              refine ⟨5458587515030922834903605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639058343353948556602403 5458587515030922834903605)
              ·
                refine ⟨511742579534149015772213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5458587515030922834903605 511742579534149015772213)
                ·
                  refine ⟨47975866831326470228645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 511742579534149015772213 47975866831326470228645)
                  ·
                    rfl

theorem cell23_840894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_840894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840894 prefixEnd_840894 := by exact prefixLift 840894
  have htrace : WordTrace (prefixWord ++ tailWord_840894) baseStart_840894 baseEnd_840894 := by
    simpa [prefixWord, tailWord_840894, baseEnd_840894] using wordTrace_append hprefix tailTrace_840894
  have hstable : (prefixWord ++ tailWord_840894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840894).length < 2 ^ (prefixWord ++ tailWord_840894).sum := by decide
  have hdescent : baseEnd_840894 < baseStart_840894 := by decide
  rcases family_descends (prefixWord ++ tailWord_840894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840947 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3]
def baseStart_840947 : Nat := 118140960795 + 840947 * 2 ^ 59
def prefixEnd_840947 : Nat := 4983230072969 + 3 ^ 40 * 840947 * 2
def baseEnd_840947 : Nat := 431810015956626524695061

theorem tailTrace_840947 : CollatzResearch.WordTrace tailWord_840947 prefixEnd_840947 431810015956626524695061 := by
  unfold tailWord_840947
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671856884400116158353095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20447904589600077438902063 30671856884400116158353095)
  ·
    refine ⟨46007785326600174237529643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30671856884400116158353095 46007785326600174237529643)
    ·
      refine ⟨69011677989900261356294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46007785326600174237529643 69011677989900261356294465)
      ·
        refine ⟨51758758492425196017220849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69011677989900261356294465 51758758492425196017220849)
        ·
          refine ⟨38819068869318897012915637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51758758492425196017220849 38819068869318897012915637)
          ·
            refine ⟨3639287706498646594960841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38819068869318897012915637 3639287706498646594960841)
            ·
              refine ⟨2729465779873984946220631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639287706498646594960841 2729465779873984946220631)
              ·
                refine ⟨4094198669810977419330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729465779873984946220631 4094198669810977419330947)
                ·
                  refine ⟨6141298004716466128996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094198669810977419330947 6141298004716466128996421)
                  ·
                    refine ⟨1151493375884337399186829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141298004716466128996421 1151493375884337399186829)
                    ·
                      refine ⟨431810015956626524695061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1151493375884337399186829 431810015956626524695061)
                      ·
                        rfl

theorem cell23_840947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_840947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840947 prefixEnd_840947 := by exact prefixLift 840947
  have htrace : WordTrace (prefixWord ++ tailWord_840947) baseStart_840947 baseEnd_840947 := by
    simpa [prefixWord, tailWord_840947, baseEnd_840947] using wordTrace_append hprefix tailTrace_840947
  have hstable : (prefixWord ++ tailWord_840947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840947).length < 2 ^ (prefixWord ++ tailWord_840947).sum := by decide
  have hdescent : baseEnd_840947 < baseStart_840947 := by decide
  rcases family_descends (prefixWord ++ tailWord_840947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840964 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_840964 : Nat := 118140960795 + 840964 * 2 ^ 59
def prefixEnd_840964 : Nat := 4983230072969 + 3 ^ 40 * 840964 * 2
def baseEnd_840964 : Nat := 431818745127752958182483

theorem tailTrace_840964 : CollatzResearch.WordTrace tailWord_840964 prefixEnd_840964 431818745127752958182483 := by
  unfold tailWord_840964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336238462669264030860973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20448317950225685374481297 15336238462669264030860973)
  ·
    refine ⟨5751089423500974011572865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15336238462669264030860973 5751089423500974011572865)
    ·
      refine ⟨4313317067625730508679649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5751089423500974011572865 4313317067625730508679649)
      ·
        refine ⟨3234987800719297881509737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313317067625730508679649 3234987800719297881509737)
        ·
          refine ⟨2426240850539473411132303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234987800719297881509737 2426240850539473411132303)
          ·
            refine ⟨3639361275809210116698455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426240850539473411132303 3639361275809210116698455)
            ·
              refine ⟨5459041913713815175047683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639361275809210116698455 5459041913713815175047683)
              ·
                refine ⟨8188562870570722762571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459041913713815175047683 8188562870570722762571525)
                ·
                  refine ⟨1535355538232010517982161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8188562870570722762571525 1535355538232010517982161)
                  ·
                    refine ⟨1151516653674007888486621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1535355538232010517982161 1151516653674007888486621)
                    ·
                      refine ⟨431818745127752958182483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1151516653674007888486621 431818745127752958182483)
                      ·
                        rfl

theorem cell23_840964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_840964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840964 prefixEnd_840964 := by exact prefixLift 840964
  have htrace : WordTrace (prefixWord ++ tailWord_840964) baseStart_840964 baseEnd_840964 := by
    simpa [prefixWord, tailWord_840964, baseEnd_840964] using wordTrace_append hprefix tailTrace_840964
  have hstable : (prefixWord ++ tailWord_840964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840964).length < 2 ^ (prefixWord ++ tailWord_840964).sum := by decide
  have hdescent : baseEnd_840964 < baseStart_840964 := by decide
  rcases family_descends (prefixWord ++ tailWord_840964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840984 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 6]
def baseStart_840984 : Nat := 118140960795 + 840984 * 2 ^ 59
def prefixEnd_840984 : Nat := 4983230072969 + 3 ^ 40 * 840984 * 2
def baseEnd_840984 : Nat := 47981001637871431103599

theorem tailTrace_840984 : CollatzResearch.WordTrace tailWord_840984 prefixEnd_840984 47981001637871431103599 := by
  unfold tailWord_840984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336603192633035738725003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20448804256844047651633337 15336603192633035738725003)
  ·
    refine ⟨23004904788949553608087505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15336603192633035738725003 23004904788949553608087505)
    ·
      refine ⟨17253678591712165206065629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23004904788949553608087505 17253678591712165206065629)
      ·
        refine ⟨6470129471892061952274611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17253678591712165206065629 6470129471892061952274611)
        ·
          refine ⟨9705194207838092928411917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6470129471892061952274611 9705194207838092928411917)
          ·
            refine ⟨3639447827939284848154469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9705194207838092928411917 3639447827939284848154469)
            ·
              refine ⟨682396467738615909028963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3639447827939284848154469 682396467738615909028963)
              ·
                refine ⟨1023594701607923863543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682396467738615909028963 1023594701607923863543445)
                ·
                  refine ⟨47981001637871431103599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1023594701607923863543445 47981001637871431103599)
                  ·
                    rfl

theorem cell23_840984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_840984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_840984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_840984 prefixEnd_840984 := by exact prefixLift 840984
  have htrace : WordTrace (prefixWord ++ tailWord_840984) baseStart_840984 baseEnd_840984 := by
    simpa [prefixWord, tailWord_840984, baseEnd_840984] using wordTrace_append hprefix tailTrace_840984
  have hstable : (prefixWord ++ tailWord_840984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840984).length < 2 ^ (prefixWord ++ tailWord_840984).sum := by decide
  have hdescent : baseEnd_840984 < baseStart_840984 := by decide
  rcases family_descends (prefixWord ++ tailWord_840984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841044 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_841044 : Nat := 118140960795 + 841044 * 2 ^ 59
def prefixEnd_841044 : Nat := 4983230072969 + 3 ^ 40 * 841044 * 2
def baseEnd_841044 : Nat := 143953274526704215060705

theorem tailTrace_841044 : CollatzResearch.WordTrace tailWord_841044 prefixEnd_841044 143953274526704215060705 := by
  unfold tailWord_841044
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337697382524350862317093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20450263176699134483089457 15337697382524350862317093)
  ·
    refine ⟨2875818259223315786684455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15337697382524350862317093 2875818259223315786684455)
    ·
      refine ⟨4313727388834973680026683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875818259223315786684455 4313727388834973680026683)
      ·
        refine ⟨6470591083252460520040025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313727388834973680026683 6470591083252460520040025)
        ·
          refine ⟨4852943312439345390030019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6470591083252460520040025 4852943312439345390030019)
          ·
            refine ⟨7279414968659018085045029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852943312439345390030019 7279414968659018085045029)
            ·
              refine ⟨1364890306623565890945943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7279414968659018085045029 1364890306623565890945943)
              ·
                refine ⟨2047335459935348836418915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364890306623565890945943 2047335459935348836418915)
                ·
                  refine ⟨3071003189903023254628373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047335459935348836418915 3071003189903023254628373)
                  ·
                    refine ⟨143953274526704215060705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3071003189903023254628373 143953274526704215060705)
                    ·
                      rfl

theorem cell23_841044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_841044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841044 prefixEnd_841044 := by exact prefixLift 841044
  have htrace : WordTrace (prefixWord ++ tailWord_841044) baseStart_841044 baseEnd_841044 := by
    simpa [prefixWord, tailWord_841044, baseEnd_841044] using wordTrace_append hprefix tailTrace_841044
  have hstable : (prefixWord ++ tailWord_841044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841044).length < 2 ^ (prefixWord ++ tailWord_841044).sum := by decide
  have hdescent : baseEnd_841044 < baseStart_841044 := by decide
  rcases family_descends (prefixWord ++ tailWord_841044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841068 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_841068 : Nat := 118140960795 + 841068 * 2 ^ 59
def prefixEnd_841068 : Nat := 4983230072969 + 3 ^ 40 * 841068 * 2
def baseEnd_841068 : Nat := 431872147115820551282005

theorem tailTrace_841068 : CollatzResearch.WordTrace tailWord_841068 prefixEnd_841068 431872147115820551282005 := by
  unfold tailWord_841068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338135058480876911753929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20450846744641169215671905 15338135058480876911753929)
  ·
    refine ⟨11503601293860657683815447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15338135058480876911753929 11503601293860657683815447)
    ·
      refine ⟨17255401940790986525723171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11503601293860657683815447 17255401940790986525723171)
      ·
        refine ⟨25883102911186479788584757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17255401940790986525723171 25883102911186479788584757)
        ·
          refine ⟨2426540897923732480179821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25883102911186479788584757 2426540897923732480179821)
          ·
            refine ⟨909952836721399680067433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2426540897923732480179821 909952836721399680067433)
            ·
              refine ⟨682464627541049760050575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909952836721399680067433 682464627541049760050575)
              ·
                refine ⟨1023696941311574640075863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682464627541049760050575 1023696941311574640075863)
                ·
                  refine ⟨1535545411967361960113795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023696941311574640075863 1535545411967361960113795)
                  ·
                    refine ⟨2303318117951042940170693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535545411967361960113795 2303318117951042940170693)
                    ·
                      refine ⟨431872147115820551282005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2303318117951042940170693 431872147115820551282005)
                      ·
                        rfl

theorem cell23_841068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_841068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841068 prefixEnd_841068 := by exact prefixLift 841068
  have htrace : WordTrace (prefixWord ++ tailWord_841068) baseStart_841068 baseEnd_841068 := by
    simpa [prefixWord, tailWord_841068, baseEnd_841068] using wordTrace_append hprefix tailTrace_841068
  have hstable : (prefixWord ++ tailWord_841068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841068).length < 2 ^ (prefixWord ++ tailWord_841068).sum := by decide
  have hdescent : baseEnd_841068 < baseStart_841068 := by decide
  rcases family_descends (prefixWord ++ tailWord_841068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841201 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_841201 : Nat := 118140960795 + 841201 * 2 ^ 59
def prefixEnd_841201 : Nat := 4983230072969 + 3 ^ 40 * 841201 * 2
def baseEnd_841201 : Nat := 431940440042868530918893

theorem tailTrace_841201 : CollatzResearch.WordTrace tailWord_841201 prefixEnd_841201 431940440042868530918893 := by
  unfold tailWord_841201
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681121025479917538099457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20454080683653278358732971 30681121025479917538099457)
  ·
    refine ⟨23010840769109938153574593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30681121025479917538099457 23010840769109938153574593)
    ·
      refine ⟨17258130576832453615180945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23010840769109938153574593 17258130576832453615180945)
      ·
        refine ⟨12943597932624340211385709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17258130576832453615180945 12943597932624340211385709)
        ·
          refine ⟨4853849224734127579269641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12943597932624340211385709 4853849224734127579269641)
          ·
            refine ⟨3640386918550595684452231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853849224734127579269641 3640386918550595684452231)
            ·
              refine ⟨5460580377825893526678347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640386918550595684452231 5460580377825893526678347)
              ·
                refine ⟨8190870566738840290017521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460580377825893526678347 8190870566738840290017521)
                ·
                  refine ⟨6143152925054130217513141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8190870566738840290017521 6143152925054130217513141)
                  ·
                    refine ⟨575920586723824707891857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6143152925054130217513141 575920586723824707891857)
                    ·
                      refine ⟨431940440042868530918893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575920586723824707891857 431940440042868530918893)
                      ·
                        rfl

theorem cell23_841201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_841201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841201 prefixEnd_841201 := by exact prefixLift 841201
  have htrace : WordTrace (prefixWord ++ tailWord_841201) baseStart_841201 baseEnd_841201 := by
    simpa [prefixWord, tailWord_841201, baseEnd_841201] using wordTrace_append hprefix tailTrace_841201
  have hstable : (prefixWord ++ tailWord_841201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841201).length < 2 ^ (prefixWord ++ tailWord_841201).sum := by decide
  have hdescent : baseEnd_841201 < baseStart_841201 := by decide
  rcases family_descends (prefixWord ++ tailWord_841201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841228 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_841228 : Nat := 118140960795 + 841228 * 2 ^ 59
def prefixEnd_841228 : Nat := 4983230072969 + 3 ^ 40 * 841228 * 2
def baseEnd_841228 : Nat := 143984768006846641760423

theorem tailTrace_841228 : CollatzResearch.WordTrace tailWord_841228 prefixEnd_841228 143984768006846641760423 := by
  unfold tailWord_841228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341052898191050574666169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20454737197588067432888225 15341052898191050574666169)
  ·
    refine ⟨11505789673643287930999627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15341052898191050574666169 11505789673643287930999627)
    ·
      refine ⟨17258684510464931896499441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505789673643287930999627 17258684510464931896499441)
      ·
        refine ⟨12944013382848698922374581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17258684510464931896499441 12944013382848698922374581)
        ·
          refine ⟨1213501254642065523972617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12944013382848698922374581 1213501254642065523972617)
          ·
            refine ⟨910125940981549142979463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213501254642065523972617 910125940981549142979463)
            ·
              refine ⟨1365188911472323714469195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910125940981549142979463 1365188911472323714469195)
              ·
                refine ⟨2047783367208485571703793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365188911472323714469195 2047783367208485571703793)
                ·
                  refine ⟨1535837525406364178777845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047783367208485571703793 1535837525406364178777845)
                  ·
                    refine ⟨143984768006846641760423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1535837525406364178777845 143984768006846641760423)
                    ·
                      rfl

theorem cell23_841228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_841228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841228 prefixEnd_841228 := by exact prefixLift 841228
  have htrace : WordTrace (prefixWord ++ tailWord_841228) baseStart_841228 baseEnd_841228 := by
    simpa [prefixWord, tailWord_841228, baseEnd_841228] using wordTrace_append hprefix tailTrace_841228
  have hstable : (prefixWord ++ tailWord_841228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841228).length < 2 ^ (prefixWord ++ tailWord_841228).sum := by decide
  have hdescent : baseEnd_841228 < baseStart_841228 := by decide
  rcases family_descends (prefixWord ++ tailWord_841228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841244 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_841244 : Nat := 118140960795 + 841244 * 2 ^ 59
def prefixEnd_841244 : Nat := 4983230072969 + 3 ^ 40 * 841244 * 2
def baseEnd_841244 : Nat := 431962519711011862681195

theorem tailTrace_841244 : CollatzResearch.WordTrace tailWord_841244 prefixEnd_841244 431962519711011862681195 := by
  unfold tailWord_841244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341344682162067940957393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20455126242882757254609857 15341344682162067940957393)
  ·
    refine ⟨11506008511621550955718045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15341344682162067940957393 11506008511621550955718045)
    ·
      refine ⟨4314753191858081608394267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11506008511621550955718045 4314753191858081608394267)
      ·
        refine ⟨6472129787787122412591401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314753191858081608394267 6472129787787122412591401)
        ·
          refine ⟨4854097340840341809443551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6472129787787122412591401 4854097340840341809443551)
          ·
            refine ⟨7281146011260512714165327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854097340840341809443551 7281146011260512714165327)
            ·
              refine ⟨10921719016890769071247991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281146011260512714165327 10921719016890769071247991)
              ·
                refine ⟨16382578525336153606871987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10921719016890769071247991 16382578525336153606871987)
                ·
                  refine ⟨24573867788004230410307981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16382578525336153606871987 24573867788004230410307981)
                  ·
                    refine ⟨9215200420501586403865493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24573867788004230410307981 9215200420501586403865493)
                    ·
                      refine ⟨431962519711011862681195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9215200420501586403865493 431962519711011862681195)
                      ·
                        rfl

theorem cell23_841244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_841244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841244 prefixEnd_841244 := by exact prefixLift 841244
  have htrace : WordTrace (prefixWord ++ tailWord_841244) baseStart_841244 baseEnd_841244 := by
    simpa [prefixWord, tailWord_841244, baseEnd_841244] using wordTrace_append hprefix tailTrace_841244
  have hstable : (prefixWord ++ tailWord_841244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841244).length < 2 ^ (prefixWord ++ tailWord_841244).sum := by decide
  have hdescent : baseEnd_841244 < baseStart_841244 := by decide
  rcases family_descends (prefixWord ++ tailWord_841244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841248 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2]
def baseStart_841248 : Nat := 118140960795 + 841248 * 2 ^ 59
def prefixEnd_841248 : Nat := 4983230072969 + 3 ^ 40 * 841248 * 2
def baseEnd_841248 : Nat := 431964573633629847031177

theorem tailTrace_841248 : CollatzResearch.WordTrace tailWord_841248 prefixEnd_841248 431964573633629847031177 := by
  unfold tailWord_841248
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341417628154822282530199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20455223504206429710040265 15341417628154822282530199)
  ·
    refine ⟨23012126442232233423795299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341417628154822282530199 23012126442232233423795299)
    ·
      refine ⟨34518189663348350135692949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23012126442232233423795299 34518189663348350135692949)
      ·
        refine ⟨1618040140469453912610607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34518189663348350135692949 1618040140469453912610607)
        ·
          refine ⟨2427060210704180868915911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618040140469453912610607 2427060210704180868915911)
          ·
            refine ⟨3640590316056271303373867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427060210704180868915911 3640590316056271303373867)
            ·
              refine ⟨5460885474084406955060801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640590316056271303373867 5460885474084406955060801)
              ·
                refine ⟨4095664105563305216295601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460885474084406955060801 4095664105563305216295601)
                ·
                  refine ⟨3071748079172478912221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095664105563305216295601 3071748079172478912221701)
                  ·
                    refine ⟨575952764844839796041569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071748079172478912221701 575952764844839796041569)
                    ·
                      refine ⟨431964573633629847031177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 575952764844839796041569 431964573633629847031177)
                      ·
                        rfl

theorem cell23_841248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_841248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841248 prefixEnd_841248 := by exact prefixLift 841248
  have htrace : WordTrace (prefixWord ++ tailWord_841248) baseStart_841248 baseEnd_841248 := by
    simpa [prefixWord, tailWord_841248, baseEnd_841248] using wordTrace_append hprefix tailTrace_841248
  have hstable : (prefixWord ++ tailWord_841248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841248).length < 2 ^ (prefixWord ++ tailWord_841248).sum := by decide
  have hdescent : baseEnd_841248 < baseStart_841248 := by decide
  rcases family_descends (prefixWord ++ tailWord_841248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841258 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_841258 : Nat := 118140960795 + 841258 * 2 ^ 59
def prefixEnd_841258 : Nat := 4983230072969 + 3 ^ 40 * 841258 * 2
def baseEnd_841258 : Nat := 143989902813391602635377

theorem tailTrace_841258 : CollatzResearch.WordTrace tailWord_841258 prefixEnd_841258 143989902813391602635377 := by
  unfold tailWord_841258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670799996568354068231107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20455466657515610848616285 7670799996568354068231107)
  ·
    refine ⟨11506199994852531102346661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670799996568354068231107 11506199994852531102346661)
    ·
      refine ⟨2157412499034849581689999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11506199994852531102346661 2157412499034849581689999)
      ·
        refine ⟨3236118748552274372534999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157412499034849581689999 3236118748552274372534999)
        ·
          refine ⟨4854178122828411558802499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236118748552274372534999 4854178122828411558802499)
          ·
            refine ⟨7281267184242617338203749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854178122828411558802499 7281267184242617338203749)
            ·
              refine ⟨1365237597045490750913203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7281267184242617338203749 1365237597045490750913203)
              ·
                refine ⟨2047856395568236126369805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365237597045490750913203 2047856395568236126369805)
                ·
                  refine ⟨767946148338088547388677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2047856395568236126369805 767946148338088547388677)
                  ·
                    refine ⟨143989902813391602635377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767946148338088547388677 143989902813391602635377)
                    ·
                      rfl

theorem cell23_841258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_841258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841258 prefixEnd_841258 := by exact prefixLift 841258
  have htrace : WordTrace (prefixWord ++ tailWord_841258) baseStart_841258 baseEnd_841258 := by
    simpa [prefixWord, tailWord_841258, baseEnd_841258] using wordTrace_append hprefix tailTrace_841258
  have hstable : (prefixWord ++ tailWord_841258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841258).length < 2 ^ (prefixWord ++ tailWord_841258).sum := by decide
  have hdescent : baseEnd_841258 < baseStart_841258 := by decide
  rcases family_descends (prefixWord ++ tailWord_841258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841274 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_841274 : Nat := 118140960795 + 841274 * 2 ^ 59
def prefixEnd_841274 : Nat := 4983230072969 + 3 ^ 40 * 841274 * 2
def baseEnd_841274 : Nat := 431977924130646745306057

theorem tailTrace_841274 : CollatzResearch.WordTrace tailWord_841274 prefixEnd_841274 431977924130646745306057 := by
  unfold tailWord_841274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670945888553862751376719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20455855702810300670337917 7670945888553862751376719)
  ·
    refine ⟨11506418832830794127065079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670945888553862751376719 11506418832830794127065079)
    ·
      refine ⟨17259628249246191190597619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11506418832830794127065079 17259628249246191190597619)
      ·
        refine ⟨25889442373869286785896429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17259628249246191190597619 25889442373869286785896429)
        ·
          refine ⟨9708540890200982544711161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25889442373869286785896429 9708540890200982544711161)
          ·
            refine ⟨7281405667650736908533371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708540890200982544711161 7281405667650736908533371)
            ·
              refine ⟨10922108501476105362800057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281405667650736908533371 10922108501476105362800057)
              ·
                refine ⟨8191581376107079022100043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10922108501476105362800057 8191581376107079022100043)
                ·
                  refine ⟨12287372064160618533150065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191581376107079022100043 12287372064160618533150065)
                  ·
                    refine ⟨9215529048120463899862549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287372064160618533150065 9215529048120463899862549)
                    ·
                      refine ⟨431977924130646745306057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9215529048120463899862549 431977924130646745306057)
                      ·
                        rfl

theorem cell23_841274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_841274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841274 prefixEnd_841274 := by exact prefixLift 841274
  have htrace : WordTrace (prefixWord ++ tailWord_841274) baseStart_841274 baseEnd_841274 := by
    simpa [prefixWord, tailWord_841274, baseEnd_841274] using wordTrace_append hprefix tailTrace_841274
  have hstable : (prefixWord ++ tailWord_841274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841274).length < 2 ^ (prefixWord ++ tailWord_841274).sum := by decide
  have hdescent : baseEnd_841274 < baseStart_841274 := by decide
  rcases family_descends (prefixWord ++ tailWord_841274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841281 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_841281 : Nat := 118140960795 + 841281 * 2 ^ 59
def prefixEnd_841281 : Nat := 4983230072969 + 3 ^ 40 * 841281 * 2
def baseEnd_841281 : Nat := 431981518495228217918525

theorem tailTrace_841281 : CollatzResearch.WordTrace tailWord_841281 prefixEnd_841281 431981518495228217918525 := by
  unfold tailWord_841281
  simp only [CollatzResearch.WordTrace]
  refine ⟨30684038865190091201011697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20456025910126727467341131 30684038865190091201011697)
  ·
    refine ⟨23013029148892568400758773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30684038865190091201011697 23013029148892568400758773)
    ·
      refine ⟨2157471482708678287571135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23013029148892568400758773 2157471482708678287571135)
      ·
        refine ⟨3236207224063017431356703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157471482708678287571135 3236207224063017431356703)
        ·
          refine ⟨4854310836094526147035055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236207224063017431356703 4854310836094526147035055)
          ·
            refine ⟨7281466254141789220552583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854310836094526147035055 7281466254141789220552583)
            ·
              refine ⟨10922199381212683830828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281466254141789220552583 10922199381212683830828875)
              ·
                refine ⟨16383299071819025746243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922199381212683830828875 16383299071819025746243313)
                ·
                  refine ⟨12287474303864269309682485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383299071819025746243313 12287474303864269309682485)
                  ·
                    refine ⟨1151950715987275247782733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12287474303864269309682485 1151950715987275247782733)
                    ·
                      refine ⟨431981518495228217918525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1151950715987275247782733 431981518495228217918525)
                      ·
                        rfl

theorem cell23_841281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_841281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841281 prefixEnd_841281 := by exact prefixLift 841281
  have htrace : WordTrace (prefixWord ++ tailWord_841281) baseStart_841281 baseEnd_841281 := by
    simpa [prefixWord, tailWord_841281, baseEnd_841281] using wordTrace_append hprefix tailTrace_841281
  have hstable : (prefixWord ++ tailWord_841281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841281).length < 2 ^ (prefixWord ++ tailWord_841281).sum := by decide
  have hdescent : baseEnd_841281 < baseStart_841281 := by decide
  rcases family_descends (prefixWord ++ tailWord_841281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841309 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_841309 : Nat := 118140960795 + 841309 * 2 ^ 59
def prefixEnd_841309 : Nat := 4983230072969 + 3 ^ 40 * 841309 * 2
def baseEnd_841309 : Nat := 143998631984518036122799

theorem tailTrace_841309 : CollatzResearch.WordTrace tailWord_841309 prefixEnd_841309 143998631984518036122799 := by
  unfold tailWord_841309
  simp only [CollatzResearch.WordTrace]
  refine ⟨30685060109088651983030981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20456706739392434655353987 30685060109088651983030981)
  ·
    refine ⟨5753448770454122246818309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30685060109088651983030981 5753448770454122246818309)
    ·
      refine ⟨1078771644460147921278433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5753448770454122246818309 1078771644460147921278433)
      ·
        refine ⟨809078733345110940958825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078771644460147921278433 809078733345110940958825)
        ·
          refine ⟨606809050008833205719119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809078733345110940958825 606809050008833205719119)
          ·
            refine ⟨910213575013249808578679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606809050008833205719119 910213575013249808578679)
            ·
              refine ⟨1365320362519874712868019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910213575013249808578679 1365320362519874712868019)
              ·
                refine ⟨2047980543779812069302029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365320362519874712868019 2047980543779812069302029)
                ·
                  refine ⟨767992703917429525988261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2047980543779812069302029 767992703917429525988261)
                  ·
                    refine ⟨143998631984518036122799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767992703917429525988261 143998631984518036122799)
                    ·
                      rfl

theorem cell23_841309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_841309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841309 prefixEnd_841309 := by exact prefixLift 841309
  have htrace : WordTrace (prefixWord ++ tailWord_841309) baseStart_841309 baseEnd_841309 := by
    simpa [prefixWord, tailWord_841309, baseEnd_841309] using wordTrace_append hprefix tailTrace_841309
  have hstable : (prefixWord ++ tailWord_841309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841309).length < 2 ^ (prefixWord ++ tailWord_841309).sum := by decide
  have hdescent : baseEnd_841309 < baseStart_841309 := by decide
  rcases family_descends (prefixWord ++ tailWord_841309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841315 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 3]
def baseStart_841315 : Nat := 118140960795 + 841315 * 2 ^ 59
def prefixEnd_841315 : Nat := 4983230072969 + 3 ^ 40 * 841315 * 2
def baseEnd_841315 : Nat := 431998976837481084893369

theorem tailTrace_841315 : CollatzResearch.WordTrace tailWord_841315 prefixEnd_841315 431998976837481084893369 := by
  unfold tailWord_841315
  simp only [CollatzResearch.WordTrace]
  refine ⟨30685278947066915007749399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20456852631377943338499599 30685278947066915007749399)
  ·
    refine ⟨46027918420600372511624099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30685278947066915007749399 46027918420600372511624099)
    ·
      refine ⟨69041877630900558767436149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46027918420600372511624099 69041877630900558767436149)
      ·
        refine ⟨6472676027896927384447139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69041877630900558767436149 6472676027896927384447139)
        ·
          refine ⟨9709014041845391076670709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472676027896927384447139 9709014041845391076670709)
          ·
            refine ⟨910220066423005413437879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9709014041845391076670709 910220066423005413437879)
            ·
              refine ⟨1365330099634508120156819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910220066423005413437879 1365330099634508120156819)
              ·
                refine ⟨2047995149451762180235229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365330099634508120156819 2047995149451762180235229)
                ·
                  refine ⟨767998181044410817588211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2047995149451762180235229 767998181044410817588211)
                  ·
                    refine ⟨1151997271566616226382317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 767998181044410817588211 1151997271566616226382317)
                    ·
                      refine ⟨431998976837481084893369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1151997271566616226382317 431998976837481084893369)
                      ·
                        rfl

theorem cell23_841315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_841315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841315 prefixEnd_841315 := by exact prefixLift 841315
  have htrace : WordTrace (prefixWord ++ tailWord_841315) baseStart_841315 baseEnd_841315 := by
    simpa [prefixWord, tailWord_841315, baseEnd_841315] using wordTrace_append hprefix tailTrace_841315
  have hstable : (prefixWord ++ tailWord_841315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841315).length < 2 ^ (prefixWord ++ tailWord_841315).sum := by decide
  have hdescent : baseEnd_841315 < baseStart_841315 := by decide
  rcases family_descends (prefixWord ++ tailWord_841315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841344 : List Nat := [2, 1, 1, 2, 1, 4, 1, 11]
def baseStart_841344 : Nat := 118140960795 + 841344 * 2 ^ 59
def prefixEnd_841344 : Nat := 4983230072969 + 3 ^ 40 * 841344 * 2
def baseEnd_841344 : Nat := 16000513621350424867805

theorem tailTrace_841344 : CollatzResearch.WordTrace tailWord_841344 prefixEnd_841344 16000513621350424867805 := by
  unfold tailWord_841344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343168331980926480277543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20457557775974568640370057 15343168331980926480277543)
  ·
    refine ⟨23014752497971389720416315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343168331980926480277543 23014752497971389720416315)
    ·
      refine ⟨34522128746957084580624473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014752497971389720416315 34522128746957084580624473)
      ·
        refine ⟨25891596560217813435468355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34522128746957084580624473 25891596560217813435468355)
        ·
          refine ⟨38837394840326720153202533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25891596560217813435468355 38837394840326720153202533)
          ·
            refine ⟨7282011532561260028725475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38837394840326720153202533 7282011532561260028725475)
            ·
              refine ⟨10923017298841890043088213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282011532561260028725475 10923017298841890043088213)
              ·
                refine ⟨16000513621350424867805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 10923017298841890043088213 16000513621350424867805)
                ·
                  rfl

theorem cell23_841344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_841344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841344 prefixEnd_841344 := by exact prefixLift 841344
  have htrace : WordTrace (prefixWord ++ tailWord_841344) baseStart_841344 baseEnd_841344 := by
    simpa [prefixWord, tailWord_841344, baseEnd_841344] using wordTrace_append hprefix tailTrace_841344
  have hstable : (prefixWord ++ tailWord_841344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841344).length < 2 ^ (prefixWord ++ tailWord_841344).sum := by decide
  have hdescent : baseEnd_841344 < baseStart_841344 := by decide
  rcases family_descends (prefixWord ++ tailWord_841344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841348 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_841348 : Nat := 118140960795 + 841348 * 2 ^ 59
def prefixEnd_841348 : Nat := 4983230072969 + 3 ^ 40 * 841348 * 2
def baseEnd_841348 : Nat := 144005307233026485260239

theorem tailTrace_841348 : CollatzResearch.WordTrace tailWord_841348 prefixEnd_841348 144005307233026485260239 := by
  unfold tailWord_841348
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343241277973680821850349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20457655037298241095800465 15343241277973680821850349)
  ·
    refine ⟨5753715479240130308193881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15343241277973680821850349 5753715479240130308193881)
    ·
      refine ⟨4315286609430097731145411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5753715479240130308193881 4315286609430097731145411)
      ·
        refine ⟨6472929914145146596718117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315286609430097731145411 6472929914145146596718117)
        ·
          refine ⟨1213674358902214986884647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6472929914145146596718117 1213674358902214986884647)
          ·
            refine ⟨1820511538353322480326971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213674358902214986884647 1820511538353322480326971)
            ·
              refine ⟨2730767307529983720490457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820511538353322480326971 2730767307529983720490457)
              ·
                refine ⟨2048075480647487790367843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730767307529983720490457 2048075480647487790367843)
                ·
                  refine ⟨3072113220971231685551765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048075480647487790367843 3072113220971231685551765)
                  ·
                    refine ⟨144005307233026485260239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3072113220971231685551765 144005307233026485260239)
                    ·
                      rfl

theorem cell23_841348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_841348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841348 prefixEnd_841348 := by exact prefixLift 841348
  have htrace : WordTrace (prefixWord ++ tailWord_841348) baseStart_841348 baseEnd_841348 := by
    simpa [prefixWord, tailWord_841348, baseEnd_841348] using wordTrace_append hprefix tailTrace_841348
  have hstable : (prefixWord ++ tailWord_841348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841348).length < 2 ^ (prefixWord ++ tailWord_841348).sum := by decide
  have hdescent : baseEnd_841348 < baseStart_841348 := by decide
  rcases family_descends (prefixWord ++ tailWord_841348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841351 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_841351 : Nat := 118140960795 + 841351 * 2 ^ 59
def prefixEnd_841351 : Nat := 4983230072969 + 3 ^ 40 * 841351 * 2
def baseEnd_841351 : Nat := 432017462141042944043203

theorem tailTrace_841351 : CollatzResearch.WordTrace tailWord_841351 prefixEnd_841351 432017462141042944043203 := by
  unfold tailWord_841351
  simp only [CollatzResearch.WordTrace]
  refine ⟨30686591974936493156059907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20457727983290995437373271 30686591974936493156059907)
  ·
    refine ⟨46029887962404739734089861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30686591974936493156059907 46029887962404739734089861)
    ·
      refine ⟨8630603992950888700141849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46029887962404739734089861 8630603992950888700141849)
      ·
        refine ⟨6472952994713166525106387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8630603992950888700141849 6472952994713166525106387)
        ·
          refine ⟨9709429492069749787659581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472952994713166525106387 9709429492069749787659581)
          ·
            refine ⟨3641036059526156170372343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9709429492069749787659581 3641036059526156170372343)
            ·
              refine ⟨5461554089289234255558515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641036059526156170372343 5461554089289234255558515)
              ·
                refine ⟨8192331133933851383337773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461554089289234255558515 8192331133933851383337773)
                ·
                  refine ⟨3072124175225194268751665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8192331133933851383337773 3072124175225194268751665)
                  ·
                    refine ⟨2304093131418895701563749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072124175225194268751665 2304093131418895701563749)
                    ·
                      refine ⟨432017462141042944043203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2304093131418895701563749 432017462141042944043203)
                      ·
                        rfl

theorem cell23_841351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_841351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841351 prefixEnd_841351 := by exact prefixLift 841351
  have htrace : WordTrace (prefixWord ++ tailWord_841351) baseStart_841351 baseEnd_841351 := by
    simpa [prefixWord, tailWord_841351, baseEnd_841351] using wordTrace_append hprefix tailTrace_841351
  have hstable : (prefixWord ++ tailWord_841351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841351).length < 2 ^ (prefixWord ++ tailWord_841351).sum := by decide
  have hdescent : baseEnd_841351 < baseStart_841351 := by decide
  rcases family_descends (prefixWord ++ tailWord_841351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841352 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 1, 5]
def baseStart_841352 : Nat := 118140960795 + 841352 * 2 ^ 59
def prefixEnd_841352 : Nat := 4983230072969 + 3 ^ 40 * 841352 * 2
def baseEnd_841352 : Nat := 144005991873899146710233

theorem tailTrace_841352 : CollatzResearch.WordTrace tailWord_841352 prefixEnd_841352 144005991873899146710233 := by
  unfold tailWord_841352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343314223966435163423155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20457752298621913551230873 15343314223966435163423155)
  ·
    refine ⟨23014971335949652745134733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343314223966435163423155 23014971335949652745134733)
    ·
      refine ⟨8630614250981119779425525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23014971335949652745134733 8630614250981119779425525)
      ·
        refine ⟨809120086029479979321143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8630614250981119779425525 809120086029479979321143)
        ·
          refine ⟨1213680129044219968981715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809120086029479979321143 1213680129044219968981715)
          ·
            refine ⟨1820520193566329953472573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213680129044219968981715 1820520193566329953472573)
            ·
              refine ⟨682695072587373732552215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1820520193566329953472573 682695072587373732552215)
              ·
                refine ⟨1024042608881060598828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682695072587373732552215 1024042608881060598828323)
                ·
                  refine ⟨1536063913321590898242485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024042608881060598828323 1536063913321590898242485)
                  ·
                    refine ⟨144005991873899146710233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1536063913321590898242485 144005991873899146710233)
                    ·
                      rfl

theorem cell23_841352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_841352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841352 prefixEnd_841352 := by exact prefixLift 841352
  have htrace : WordTrace (prefixWord ++ tailWord_841352) baseStart_841352 baseEnd_841352 := by
    simpa [prefixWord, tailWord_841352, baseEnd_841352] using wordTrace_append hprefix tailTrace_841352
  have hstable : (prefixWord ++ tailWord_841352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841352).length < 2 ^ (prefixWord ++ tailWord_841352).sum := by decide
  have hdescent : baseEnd_841352 < baseStart_841352 := by decide
  rcases family_descends (prefixWord ++ tailWord_841352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841358 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_841358 : Nat := 118140960795 + 841358 * 2 ^ 59
def prefixEnd_841358 : Nat := 4983230072969 + 3 ^ 40 * 841358 * 2
def baseEnd_841358 : Nat := 432021056505624416655671

theorem tailTrace_841358 : CollatzResearch.WordTrace tailWord_841358 prefixEnd_841358 432021056505624416655671 := by
  unfold tailWord_841358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835855910738891668945591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20457898190607422234376485 3835855910738891668945591)
  ·
    refine ⟨5753783866108337503418387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3835855910738891668945591 5753783866108337503418387)
    ·
      refine ⟨8630675799162506255127581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753783866108337503418387 8630675799162506255127581)
      ·
        refine ⟨3236503424685939845672843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8630675799162506255127581 3236503424685939845672843)
        ·
          refine ⟨4854755137028909768509265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236503424685939845672843 4854755137028909768509265)
          ·
            refine ⟨3641066352771682326381949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854755137028909768509265 3641066352771682326381949)
            ·
              refine ⟨1365399882289380872393231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3641066352771682326381949 1365399882289380872393231)
              ·
                refine ⟨2048099823434071308589847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365399882289380872393231 2048099823434071308589847)
                ·
                  refine ⟨3072149735151106962884771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048099823434071308589847 3072149735151106962884771)
                  ·
                    refine ⟨4608224602726660444327157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3072149735151106962884771 4608224602726660444327157)
                    ·
                      refine ⟨432021056505624416655671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4608224602726660444327157 432021056505624416655671)
                      ·
                        rfl

theorem cell23_841358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_841358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841358 prefixEnd_841358 := by exact prefixLift 841358
  have htrace : WordTrace (prefixWord ++ tailWord_841358) baseStart_841358 baseEnd_841358 := by
    simpa [prefixWord, tailWord_841358, baseEnd_841358] using wordTrace_append hprefix tailTrace_841358
  have hstable : (prefixWord ++ tailWord_841358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841358).length < 2 ^ (prefixWord ++ tailWord_841358).sum := by decide
  have hdescent : baseEnd_841358 < baseStart_841358 := by decide
  rcases family_descends (prefixWord ++ tailWord_841358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841415 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_841415 : Nat := 118140960795 + 841415 * 2 ^ 59
def prefixEnd_841415 : Nat := 4983230072969 + 3 ^ 40 * 841415 * 2
def baseEnd_841415 : Nat := 432050324902930693642909

theorem tailTrace_841415 : CollatzResearch.WordTrace tailWord_841415 prefixEnd_841415 432050324902930693642909 := by
  unfold tailWord_841415
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688926246704632086389699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459284164469754724259799 30688926246704632086389699)
  ·
    refine ⟨46033389370056948129584549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688926246704632086389699 46033389370056948129584549)
    ·
      refine ⟨8631260506885677774297103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46033389370056948129584549 8631260506885677774297103)
      ·
        refine ⟨12946890760328516661445655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631260506885677774297103 12946890760328516661445655)
        ·
          refine ⟨19420336140492774992168483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946890760328516661445655 19420336140492774992168483)
          ·
            refine ⟨29130504210739162488252725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19420336140492774992168483 29130504210739162488252725)
            ·
              refine ⟨2730984769756796483273693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29130504210739162488252725 2730984769756796483273693)
              ·
                refine ⟨1024119288658798681227635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730984769756796483273693 1024119288658798681227635)
                ·
                  refine ⟨1536178932988198021841453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024119288658798681227635 1536178932988198021841453)
                  ·
                    refine ⟨576067099870574258190545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536178932988198021841453 576067099870574258190545)
                    ·
                      refine ⟨432050324902930693642909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576067099870574258190545 432050324902930693642909)
                      ·
                        rfl

theorem cell23_841415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_841415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841415 prefixEnd_841415 := by exact prefixLift 841415
  have htrace : WordTrace (prefixWord ++ tailWord_841415) baseStart_841415 baseEnd_841415 := by
    simpa [prefixWord, tailWord_841415, baseEnd_841415] using wordTrace_append hprefix tailTrace_841415
  have hstable : (prefixWord ++ tailWord_841415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841415).length < 2 ^ (prefixWord ++ tailWord_841415).sum := by decide
  have hdescent : baseEnd_841415 < baseStart_841415 := by decide
  rcases family_descends (prefixWord ++ tailWord_841415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841451 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 7]
def baseStart_841451 : Nat := 118140960795 + 841451 * 2 ^ 59
def prefixEnd_841451 : Nat := 4983230072969 + 3 ^ 40 * 841451 * 2
def baseEnd_841451 : Nat := 48007645578499172532527

theorem tailTrace_841451 : CollatzResearch.WordTrace tailWord_841451 prefixEnd_841451 48007645578499172532527 := by
  unfold tailWord_841451
  simp only [CollatzResearch.WordTrace]
  refine ⟨30690239274574210234700207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20460159516382806823133471 30690239274574210234700207)
  ·
    refine ⟨46035358911861315352050311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30690239274574210234700207 46035358911861315352050311)
    ·
      refine ⟨69053038367791973028075467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46035358911861315352050311 69053038367791973028075467)
      ·
        refine ⟨103579557551687959542113201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69053038367791973028075467 103579557551687959542113201)
        ·
          refine ⟨77684668163765969656584901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103579557551687959542113201 77684668163765969656584901)
          ·
            refine ⟨14565875280706119310609669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77684668163765969656584901 14565875280706119310609669)
            ·
              refine ⟨2731101615132397370739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14565875280706119310609669 2731101615132397370739313)
              ·
                refine ⟨2048326211349298028054485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731101615132397370739313 2048326211349298028054485)
                ·
                  refine ⟨48007645578499172532527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2048326211349298028054485 48007645578499172532527)
                  ·
                    rfl

theorem cell23_841451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 7].length) (baseStart_841451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841451 prefixEnd_841451 := by exact prefixLift 841451
  have htrace : WordTrace (prefixWord ++ tailWord_841451) baseStart_841451 baseEnd_841451 := by
    simpa [prefixWord, tailWord_841451, baseEnd_841451] using wordTrace_append hprefix tailTrace_841451
  have hstable : (prefixWord ++ tailWord_841451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841451).length < 2 ^ (prefixWord ++ tailWord_841451).sum := by decide
  have hdescent : baseEnd_841451 < baseStart_841451 := by decide
  rcases family_descends (prefixWord ++ tailWord_841451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841462 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_841462 : Nat := 118140960795 + 841462 * 2 ^ 59
def prefixEnd_841462 : Nat := 4983230072969 + 3 ^ 40 * 841462 * 2
def baseEnd_841462 : Nat := 432074458493692009755193

theorem tailTrace_841462 : CollatzResearch.WordTrace tailWord_841462 prefixEnd_841462 432074458493692009755193 := by
  unfold tailWord_841462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918165029845897444584415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20460426985022906075567093 1918165029845897444584415)
  ·
    refine ⟨2877247544768846166876623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918165029845897444584415 2877247544768846166876623)
    ·
      refine ⟨4315871317153269250314935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877247544768846166876623 4315871317153269250314935)
      ·
        refine ⟨6473806975729903875472403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315871317153269250314935 6473806975729903875472403)
        ·
          refine ⟨9710710463594855813208605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473806975729903875472403 9710710463594855813208605)
          ·
            refine ⟨3641516423848070929953227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9710710463594855813208605 3641516423848070929953227)
            ·
              refine ⟨5462274635772106394929841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641516423848070929953227 5462274635772106394929841)
              ·
                refine ⟨4096705976829079796197381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462274635772106394929841 4096705976829079796197381)
                ·
                  refine ⟨768132370655452461787009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4096705976829079796197381 768132370655452461787009)
                  ·
                    refine ⟨576099277991589346340257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768132370655452461787009 576099277991589346340257)
                    ·
                      refine ⟨432074458493692009755193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576099277991589346340257 432074458493692009755193)
                      ·
                        rfl

theorem cell23_841462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_841462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841462 prefixEnd_841462 := by exact prefixLift 841462
  have htrace : WordTrace (prefixWord ++ tailWord_841462) baseStart_841462 baseEnd_841462 := by
    simpa [prefixWord, tailWord_841462, baseEnd_841462] using wordTrace_append hprefix tailTrace_841462
  have hstable : (prefixWord ++ tailWord_841462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841462).length < 2 ^ (prefixWord ++ tailWord_841462).sum := by decide
  have hdescent : baseEnd_841462 < baseStart_841462 := by decide
  rcases family_descends (prefixWord ++ tailWord_841462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841542 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_841542 : Nat := 118140960795 + 841542 * 2 ^ 59
def prefixEnd_841542 : Nat := 4983230072969 + 3 ^ 40 * 841542 * 2
def baseEnd_841542 : Nat := 432115536946051696754825

theorem tailTrace_841542 : CollatzResearch.WordTrace tailWord_841542 prefixEnd_841542 432115536946051696754825 := by
  unfold tailWord_841542
  simp only [CollatzResearch.WordTrace]
  refine ⟨959173697413891649258215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20462372211496355184175253 959173697413891649258215)
  ·
    refine ⟨1438760546120837473887323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959173697413891649258215 1438760546120837473887323)
    ·
      refine ⟨2158140819181256210830985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438760546120837473887323 2158140819181256210830985)
      ·
        refine ⟨1618605614385942158123239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158140819181256210830985 1618605614385942158123239)
        ·
          refine ⟨2427908421578913237184859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618605614385942158123239 2427908421578913237184859)
          ·
            refine ⟨3641862632368369855777289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427908421578913237184859 3641862632368369855777289)
            ·
              refine ⟨2731396974276277391832967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641862632368369855777289 2731396974276277391832967)
              ·
                refine ⟨4097095461414416087749451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731396974276277391832967 4097095461414416087749451)
                ·
                  refine ⟨6145643192121624131624177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097095461414416087749451 6145643192121624131624177)
                  ·
                    refine ⟨4609232394091218098718133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145643192121624131624177 4609232394091218098718133)
                    ·
                      refine ⟨432115536946051696754825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4609232394091218098718133 432115536946051696754825)
                      ·
                        rfl

theorem cell23_841542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_841542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841542 prefixEnd_841542 := by exact prefixLift 841542
  have htrace : WordTrace (prefixWord ++ tailWord_841542) baseStart_841542 baseEnd_841542 := by
    simpa [prefixWord, tailWord_841542, baseEnd_841542] using wordTrace_append hprefix tailTrace_841542
  have hstable : (prefixWord ++ tailWord_841542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841542).length < 2 ^ (prefixWord ++ tailWord_841542).sum := by decide
  have hdescent : baseEnd_841542 < baseStart_841542 := by decide
  rcases family_descends (prefixWord ++ tailWord_841542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841585 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_841585 : Nat := 118140960795 + 841585 * 2 ^ 59
def prefixEnd_841585 : Nat := 4983230072969 + 3 ^ 40 * 841585 * 2
def baseEnd_841585 : Nat := 432137616614195028517127

theorem tailTrace_841585 : CollatzResearch.WordTrace tailWord_841585 prefixEnd_841585 432137616614195028517127 := by
  unfold tailWord_841585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695126656088751120078209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20463417770725834080052139 30695126656088751120078209)
  ·
    refine ⟨23021344992066563340058657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30695126656088751120078209 23021344992066563340058657)
    ·
      refine ⟨17266008744049922505043993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23021344992066563340058657 17266008744049922505043993)
      ·
        refine ⟨12949506558037441878782995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17266008744049922505043993 12949506558037441878782995)
        ·
          refine ⟨19424259837056162818174493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949506558037441878782995 19424259837056162818174493)
          ·
            refine ⟨7284097438896061056815435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19424259837056162818174493 7284097438896061056815435)
            ·
              refine ⟨10926146158344091585223153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284097438896061056815435 10926146158344091585223153)
              ·
                refine ⟨8194609618758068688917365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10926146158344091585223153 8194609618758068688917365)
                ·
                  refine ⟨768244651758568939586003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8194609618758068688917365 768244651758568939586003)
                  ·
                    refine ⟨1152366977637853409379005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768244651758568939586003 1152366977637853409379005)
                    ·
                      refine ⟨432137616614195028517127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152366977637853409379005 432137616614195028517127)
                      ·
                        rfl

theorem cell23_841585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_841585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841585 prefixEnd_841585 := by exact prefixLift 841585
  have htrace : WordTrace (prefixWord ++ tailWord_841585) baseStart_841585 baseEnd_841585 := by
    simpa [prefixWord, tailWord_841585, baseEnd_841585] using wordTrace_append hprefix tailTrace_841585
  have hstable : (prefixWord ++ tailWord_841585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841585).length < 2 ^ (prefixWord ++ tailWord_841585).sum := by decide
  have hdescent : baseEnd_841585 < baseStart_841585 := by decide
  rcases family_descends (prefixWord ++ tailWord_841585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841595 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 4, 3, 2]
def baseStart_841595 : Nat := 118140960795 + 841595 * 2 ^ 59
def prefixEnd_841595 : Nat := 4983230072969 + 3 ^ 40 * 841595 * 2
def baseEnd_841595 : Nat := 432142751420739989392081

theorem tailTrace_841595 : CollatzResearch.WordTrace tailWord_841595 prefixEnd_841595 432142751420739989392081 := by
  unfold tailWord_841595
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695491386052522827942239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20463660924035015218628159 30695491386052522827942239)
  ·
    refine ⟨46043237079078784241913359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30695491386052522827942239 46043237079078784241913359)
    ·
      refine ⟨69064855618618176362870039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46043237079078784241913359 69064855618618176362870039)
      ·
        refine ⟨103597283427927264544305059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69064855618618176362870039 103597283427927264544305059)
        ·
          refine ⟨155395925141890896816457589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103597283427927264544305059 155395925141890896816457589)
          ·
            refine ⟨14568367982052271576542899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155395925141890896816457589 14568367982052271576542899)
            ·
              refine ⟨21852551973078407364814349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568367982052271576542899 21852551973078407364814349)
              ·
                refine ⟨8194706989904402761805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21852551973078407364814349 8194706989904402761805381)
                ·
                  refine ⟨1536507560607075517838509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8194706989904402761805381 1536507560607075517838509)
                  ·
                    refine ⟨576190335227653319189441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1536507560607075517838509 576190335227653319189441)
                    ·
                      refine ⟨432142751420739989392081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576190335227653319189441 432142751420739989392081)
                      ·
                        rfl

theorem cell23_841595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 3, 2].length) (baseStart_841595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841595 prefixEnd_841595 := by exact prefixLift 841595
  have htrace : WordTrace (prefixWord ++ tailWord_841595) baseStart_841595 baseEnd_841595 := by
    simpa [prefixWord, tailWord_841595, baseEnd_841595] using wordTrace_append hprefix tailTrace_841595
  have hstable : (prefixWord ++ tailWord_841595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841595).length < 2 ^ (prefixWord ++ tailWord_841595).sum := by decide
  have hdescent : baseEnd_841595 < baseStart_841595 := by decide
  rcases family_descends (prefixWord ++ tailWord_841595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841625 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_841625 : Nat := 118140960795 + 841625 * 2 ^ 59
def prefixEnd_841625 : Nat := 4983230072969 + 3 ^ 40 * 841625 * 2
def baseEnd_841625 : Nat := 432158155840374872016943

theorem tailTrace_841625 : CollatzResearch.WordTrace tailWord_841625 prefixEnd_841625 432158155840374872016943 := by
  unfold tailWord_841625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30696585575943837951534329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20464390383962558634356219 30696585575943837951534329)
  ·
    refine ⟨23022439181957878463650747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30696585575943837951534329 23022439181957878463650747)
    ·
      refine ⟨34533658772936817695476121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23022439181957878463650747 34533658772936817695476121)
      ·
        refine ⟨25900244079702613271607091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34533658772936817695476121 25900244079702613271607091)
        ·
          refine ⟨38850366119553919907410637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25900244079702613271607091 38850366119553919907410637)
          ·
            refine ⟨14568887294832719965278989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38850366119553919907410637 14568887294832719965278989)
            ·
              refine ⟨5463332735562269986979621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14568887294832719965278989 5463332735562269986979621)
              ·
                refine ⟨1024374887917925622558679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5463332735562269986979621 1024374887917925622558679)
                ·
                  refine ⟨1536562331876888433838019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024374887917925622558679 1536562331876888433838019)
                  ·
                    refine ⟨2304843497815332650757029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1536562331876888433838019 2304843497815332650757029)
                    ·
                      refine ⟨432158155840374872016943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2304843497815332650757029 432158155840374872016943)
                      ·
                        rfl

theorem cell23_841625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_841625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841625 prefixEnd_841625 := by exact prefixLift 841625
  have htrace : WordTrace (prefixWord ++ tailWord_841625) baseStart_841625 baseEnd_841625 := by
    simpa [prefixWord, tailWord_841625, baseEnd_841625] using wordTrace_append hprefix tailTrace_841625
  have hstable : (prefixWord ++ tailWord_841625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841625).length < 2 ^ (prefixWord ++ tailWord_841625).sum := by decide
  have hdescent : baseEnd_841625 < baseStart_841625 := by decide
  rcases family_descends (prefixWord ++ tailWord_841625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841630 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_841630 : Nat := 118140960795 + 841630 * 2 ^ 59
def prefixEnd_841630 : Nat := 4983230072969 + 3 ^ 40 * 841630 * 2
def baseEnd_841630 : Nat := 144053574414549117484807

theorem tailTrace_841630 : CollatzResearch.WordTrace tailWord_841630 prefixEnd_841630 144053574414549117484807 := by
  unfold tailWord_841630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837095992615715475683293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20464511960617149203644229 3837095992615715475683293)
  ·
    refine ⟨1438910997230893303381235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3837095992615715475683293 1438910997230893303381235)
    ·
      refine ⟨2158366495846339955071853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438910997230893303381235 2158366495846339955071853)
      ·
        refine ⟨809387435942377483151945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2158366495846339955071853 809387435942377483151945)
        ·
          refine ⟨607040576956783112363959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809387435942377483151945 607040576956783112363959)
          ·
            refine ⟨910560865435174668545939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607040576956783112363959 910560865435174668545939)
            ·
              refine ⟨1365841298152762002818909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910560865435174668545939 1365841298152762002818909)
              ·
                refine ⟨512190486807285751057091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365841298152762002818909 512190486807285751057091)
                ·
                  refine ⟨768285730210928626585637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512190486807285751057091 768285730210928626585637)
                  ·
                    refine ⟨144053574414549117484807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 768285730210928626585637 144053574414549117484807)
                    ·
                      rfl

theorem cell23_841630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_841630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841630 prefixEnd_841630 := by exact prefixLift 841630
  have htrace : WordTrace (prefixWord ++ tailWord_841630) baseStart_841630 baseEnd_841630 := by
    simpa [prefixWord, tailWord_841630, baseEnd_841630] using wordTrace_append hprefix tailTrace_841630
  have hstable : (prefixWord ++ tailWord_841630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841630).length < 2 ^ (prefixWord ++ tailWord_841630).sum := by decide
  have hdescent : baseEnd_841630 < baseStart_841630 := by decide
  rcases family_descends (prefixWord ++ tailWord_841630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841636 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_841636 : Nat := 118140960795 + 841636 * 2 ^ 59
def prefixEnd_841636 : Nat := 4983230072969 + 3 ^ 40 * 841636 * 2
def baseEnd_841636 : Nat := 432163804127574328979393

theorem tailTrace_841636 : CollatzResearch.WordTrace tailWord_841636 prefixEnd_841636 432163804127574328979393 := by
  unfold tailWord_841636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348493389451993415092381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20464657852602657886789841 15348493389451993415092381)
  ·
    refine ⟨5755685021044497530659643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15348493389451993415092381 5755685021044497530659643)
    ·
      refine ⟨8633527531566746295989465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5755685021044497530659643 8633527531566746295989465)
      ·
        refine ⟨6475145648675059721992099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8633527531566746295989465 6475145648675059721992099)
        ·
          refine ⟨9712718473012589582988149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475145648675059721992099 9712718473012589582988149)
          ·
            refine ⟨910567356844930273405139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9712718473012589582988149 910567356844930273405139)
            ·
              refine ⟨1365851035267395410107709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910567356844930273405139 1365851035267395410107709)
              ·
                refine ⟨512194138225273278790391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365851035267395410107709 512194138225273278790391)
                ·
                  refine ⟨768291207337909918185587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512194138225273278790391 768291207337909918185587)
                  ·
                    refine ⟨1152436811006864877278381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768291207337909918185587 1152436811006864877278381)
                    ·
                      refine ⟨432163804127574328979393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152436811006864877278381 432163804127574328979393)
                      ·
                        rfl

theorem cell23_841636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_841636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841636 prefixEnd_841636 := by exact prefixLift 841636
  have htrace : WordTrace (prefixWord ++ tailWord_841636) baseStart_841636 baseEnd_841636 := by
    simpa [prefixWord, tailWord_841636, baseEnd_841636] using wordTrace_append hprefix tailTrace_841636
  have hstable : (prefixWord ++ tailWord_841636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841636).length < 2 ^ (prefixWord ++ tailWord_841636).sum := by decide
  have hdescent : baseEnd_841636 < baseStart_841636 := by decide
  rcases family_descends (prefixWord ++ tailWord_841636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841675 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3]
def baseStart_841675 : Nat := 118140960795 + 841675 * 2 ^ 59
def prefixEnd_841675 : Nat := 4983230072969 + 3 ^ 40 * 841675 * 2
def baseEnd_841675 : Nat := 432183829873099676391713

theorem tailTrace_841675 : CollatzResearch.WordTrace tailWord_841675 prefixEnd_841675 432183829873099676391713 := by
  unfold tailWord_841675
  simp only [CollatzResearch.WordTrace]
  refine ⟨30698409225762696490854479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20465606150508464327236319 30698409225762696490854479)
  ·
    refine ⟨46047613838644044736281719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30698409225762696490854479 46047613838644044736281719)
    ·
      refine ⟨69071420757966067104422579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46047613838644044736281719 69071420757966067104422579)
      ·
        refine ⟨103607131136949100656633869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69071420757966067104422579 103607131136949100656633869)
        ·
          refine ⟨38852674176355912746237701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103607131136949100656633869 38852674176355912746237701)
          ·
            refine ⟨7284876408066733639919569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38852674176355912746237701 7284876408066733639919569)
            ·
              refine ⟨5463657306050050229939677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284876408066733639919569 5463657306050050229939677)
              ·
                refine ⟨2048871489768768836227379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463657306050050229939677 2048871489768768836227379)
                ·
                  refine ⟨3073307234653153254341069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048871489768768836227379 3073307234653153254341069)
                  ·
                    refine ⟨1152490212994932470377901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073307234653153254341069 1152490212994932470377901)
                    ·
                      refine ⟨432183829873099676391713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152490212994932470377901 432183829873099676391713)
                      ·
                        rfl

theorem cell23_841675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].length) (baseStart_841675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841675 prefixEnd_841675 := by exact prefixLift 841675
  have htrace : WordTrace (prefixWord ++ tailWord_841675) baseStart_841675 baseEnd_841675 := by
    simpa [prefixWord, tailWord_841675, baseEnd_841675] using wordTrace_append hprefix tailTrace_841675
  have hstable : (prefixWord ++ tailWord_841675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841675).length < 2 ^ (prefixWord ++ tailWord_841675).sum := by decide
  have hdescent : baseEnd_841675 < baseStart_841675 := by decide
  rcases family_descends (prefixWord ++ tailWord_841675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841708 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_841708 : Nat := 118140960795 + 841708 * 2 ^ 59
def prefixEnd_841708 : Nat := 4983230072969 + 3 ^ 40 * 841708 * 2
def baseEnd_841708 : Nat := 144066924911566015759687

theorem tailTrace_841708 : CollatzResearch.WordTrace tailWord_841708 prefixEnd_841708 144066924911566015759687 := by
  unfold tailWord_841708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349806417321571563402889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20466408556428762084537185 15349806417321571563402889)
  ·
    refine ⟨11512354812991178672552167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15349806417321571563402889 11512354812991178672552167)
    ·
      refine ⟨17268532219486768008828251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11512354812991178672552167 17268532219486768008828251)
      ·
        refine ⟨25902798329230152013242377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268532219486768008828251 25902798329230152013242377)
        ·
          refine ⟨19427098746922614009931783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25902798329230152013242377 19427098746922614009931783)
          ·
            refine ⟨29140648120383921014897675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19427098746922614009931783 29140648120383921014897675)
            ·
              refine ⟨43710972180575881522346513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29140648120383921014897675 43710972180575881522346513)
              ·
                refine ⟨32783229135431911141759885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43710972180575881522346513 32783229135431911141759885)
                ·
                  refine ⟨12293710925786966678159957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32783229135431911141759885 12293710925786966678159957)
                  ·
                    refine ⟨144066924911566015759687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12293710925786966678159957 144066924911566015759687)
                    ·
                      rfl

theorem cell23_841708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_841708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841708 prefixEnd_841708 := by exact prefixLift 841708
  have htrace : WordTrace (prefixWord ++ tailWord_841708) baseStart_841708 baseEnd_841708 := by
    simpa [prefixWord, tailWord_841708, baseEnd_841708] using wordTrace_append hprefix tailTrace_841708
  have hstable : (prefixWord ++ tailWord_841708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841708).length < 2 ^ (prefixWord ++ tailWord_841708).sum := by decide
  have hdescent : baseEnd_841708 < baseStart_841708 := by decide
  rcases family_descends (prefixWord ++ tailWord_841708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841710 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_841710 : Nat := 118140960795 + 841710 * 2 ^ 59
def prefixEnd_841710 : Nat := 4983230072969 + 3 ^ 40 * 841710 * 2
def baseEnd_841710 : Nat := 432201801696007039454053

theorem tailTrace_841710 : CollatzResearch.WordTrace tailWord_841710 prefixEnd_841710 432201801696007039454053 := by
  unfold tailWord_841710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837460722579487183547323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20466457187090598312252389 3837460722579487183547323)
  ·
    refine ⟨5756191083869230775320985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3837460722579487183547323 5756191083869230775320985)
    ·
      refine ⟨4317143312901923081490739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5756191083869230775320985 4317143312901923081490739)
      ·
        refine ⟨6475714969352884622236109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317143312901923081490739 6475714969352884622236109)
        ·
          refine ⟨2428393113507331733338541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6475714969352884622236109 2428393113507331733338541)
          ·
            refine ⟨910647417565249400001953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2428393113507331733338541 910647417565249400001953)
            ·
              refine ⟨682985563173937050001465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910647417565249400001953 682985563173937050001465)
              ·
                refine ⟨512239172380452787501099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682985563173937050001465 512239172380452787501099)
                ·
                  refine ⟨768358758570679181251649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512239172380452787501099 768358758570679181251649)
                  ·
                    refine ⟨576269068928009385938737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768358758570679181251649 576269068928009385938737)
                    ·
                      refine ⟨432201801696007039454053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576269068928009385938737 432201801696007039454053)
                      ·
                        rfl

theorem cell23_841710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_841710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841710 prefixEnd_841710 := by exact prefixLift 841710
  have htrace : WordTrace (prefixWord ++ tailWord_841710) baseStart_841710 baseEnd_841710 := by
    simpa [prefixWord, tailWord_841710, baseEnd_841710] using wordTrace_append hprefix tailTrace_841710
  have hstable : (prefixWord ++ tailWord_841710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841710).length < 2 ^ (prefixWord ++ tailWord_841710).sum := by decide
  have hdescent : baseEnd_841710 < baseStart_841710 := by decide
  rcases family_descends (prefixWord ++ tailWord_841710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841726 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_841726 : Nat := 118140960795 + 841726 * 2 ^ 59
def prefixEnd_841726 : Nat := 4983230072969 + 3 ^ 40 * 841726 * 2
def baseEnd_841726 : Nat := 432210017386478976853979

theorem tailTrace_841726 : CollatzResearch.WordTrace tailWord_841726 prefixEnd_841726 432210017386478976853979 := by
  unfold tailWord_841726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837533668572241525120129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20466846232385288133974021 3837533668572241525120129)
  ·
    refine ⟨2878150251429181143840097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3837533668572241525120129 2878150251429181143840097)
    ·
      refine ⟨2158612688571885857880073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878150251429181143840097 2158612688571885857880073)
      ·
        refine ⟨1618959516428914393410055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158612688571885857880073 1618959516428914393410055)
        ·
          refine ⟨2428439274643371590115083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618959516428914393410055 2428439274643371590115083)
          ·
            refine ⟨3642658911965057385172625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428439274643371590115083 3642658911965057385172625)
            ·
              refine ⟨2731994183973793038879469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642658911965057385172625 2731994183973793038879469)
              ·
                refine ⟨1024497818990172389579801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2731994183973793038879469 1024497818990172389579801)
                ·
                  refine ⟨768373364242629292184851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024497818990172389579801 768373364242629292184851)
                  ·
                    refine ⟨1152560046363943938277277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768373364242629292184851 1152560046363943938277277)
                    ·
                      refine ⟨432210017386478976853979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152560046363943938277277 432210017386478976853979)
                      ·
                        rfl

theorem cell23_841726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_841726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841726 prefixEnd_841726 := by exact prefixLift 841726
  have htrace : WordTrace (prefixWord ++ tailWord_841726) baseStart_841726 baseEnd_841726 := by
    simpa [prefixWord, tailWord_841726, baseEnd_841726] using wordTrace_append hprefix tailTrace_841726
  have hstable : (prefixWord ++ tailWord_841726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841726).length < 2 ^ (prefixWord ++ tailWord_841726).sum := by decide
  have hdescent : baseEnd_841726 < baseStart_841726 := by decide
  rcases family_descends (prefixWord ++ tailWord_841726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841859 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3]
def baseStart_841859 : Nat := 118140960795 + 841859 * 2 ^ 59
def prefixEnd_841859 : Nat := 4983230072969 + 3 ^ 40 * 841859 * 2
def baseEnd_841859 : Nat := 432278310313526956490867

theorem tailTrace_841859 : CollatzResearch.WordTrace tailWord_841859 prefixEnd_841859 432278310313526956490867 := by
  unfold tailWord_841859
  simp only [CollatzResearch.WordTrace]
  refine ⟨30705120257096095915552631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20470080171397397277035087 30705120257096095915552631)
  ·
    refine ⟨46057680385644143873328947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30705120257096095915552631 46057680385644143873328947)
    ·
      refine ⟨69086520578466215809993421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46057680385644143873328947 69086520578466215809993421)
      ·
        refine ⟨25907445216924830928747533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69086520578466215809993421 25907445216924830928747533)
        ·
          refine ⟨9715291956346811598280325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25907445216924830928747533 9715291956346811598280325)
          ·
            refine ⟨1821617241815027174677561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9715291956346811598280325 1821617241815027174677561)
            ·
              refine ⟨1366212931361270381008171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821617241815027174677561 1366212931361270381008171)
              ·
                refine ⟨2049319397041905571512257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366212931361270381008171 2049319397041905571512257)
                ·
                  refine ⟨1536989547781429178634193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2049319397041905571512257 1536989547781429178634193)
                  ·
                    refine ⟨1152742160836071883975645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536989547781429178634193 1152742160836071883975645)
                    ·
                      refine ⟨432278310313526956490867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152742160836071883975645 432278310313526956490867)
                      ·
                        rfl

theorem cell23_841859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_841859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841859 prefixEnd_841859 := by exact prefixLift 841859
  have htrace : WordTrace (prefixWord ++ tailWord_841859) baseStart_841859 baseEnd_841859 := by
    simpa [prefixWord, tailWord_841859, baseEnd_841859] using wordTrace_append hprefix tailTrace_841859
  have hstable : (prefixWord ++ tailWord_841859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841859).length < 2 ^ (prefixWord ++ tailWord_841859).sum := by decide
  have hdescent : baseEnd_841859 < baseStart_841859 := by decide
  rcases family_descends (prefixWord ++ tailWord_841859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841879 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 6]
def baseStart_841879 : Nat := 118140960795 + 841879 * 2 ^ 59
def prefixEnd_841879 : Nat := 4983230072969 + 3 ^ 40 * 841879 * 2
def baseEnd_841879 : Nat := 48032064436290764248975

theorem tailTrace_841879 : CollatzResearch.WordTrace tailWord_841879 prefixEnd_841879 48032064436290764248975 := by
  unfold tailWord_841879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30705849717023639331280691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20470566478015759554187127 30705849717023639331280691)
  ·
    refine ⟨46058774575535458996921037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30705849717023639331280691 46058774575535458996921037)
    ·
      refine ⟨17272040465825797123845389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46058774575535458996921037 17272040465825797123845389)
      ·
        refine ⟨6477015174684673921442021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17272040465825797123845389 6477015174684673921442021)
        ·
          refine ⟨1214440345253376360270379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6477015174684673921442021 1214440345253376360270379)
          ·
            refine ⟨1821660517880064540405569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214440345253376360270379 1821660517880064540405569)
            ·
              refine ⟨1366245388410048405304177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821660517880064540405569 1366245388410048405304177)
              ·
                refine ⟨1024684041307536303978133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366245388410048405304177 1024684041307536303978133)
                ·
                  refine ⟨48032064436290764248975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1024684041307536303978133 48032064436290764248975)
                  ·
                    rfl

theorem cell23_841879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 6].length) (baseStart_841879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841879 prefixEnd_841879 := by exact prefixLift 841879
  have htrace : WordTrace (prefixWord ++ tailWord_841879) baseStart_841879 baseEnd_841879 := by
    simpa [prefixWord, tailWord_841879, baseEnd_841879] using wordTrace_append hprefix tailTrace_841879
  have hstable : (prefixWord ++ tailWord_841879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841879).length < 2 ^ (prefixWord ++ tailWord_841879).sum := by decide
  have hdescent : baseEnd_841879 < baseStart_841879 := by decide
  rcases family_descends (prefixWord ++ tailWord_841879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841912 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_841912 : Nat := 118140960795 + 841912 * 2 ^ 59
def prefixEnd_841912 : Nat := 4983230072969 + 3 ^ 40 * 841912 * 2
def baseEnd_841912 : Nat := 432305524788215249128123

theorem tailTrace_841912 : CollatzResearch.WordTrace tailWord_841912 prefixEnd_841912 432305524788215249128123 := by
  unfold tailWord_841912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353526662952042983615995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20471368883936057311487993 15353526662952042983615995)
  ·
    refine ⟨23030289994428064475423993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15353526662952042983615995 23030289994428064475423993)
    ·
      refine ⟨17272717495821048356567995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23030289994428064475423993 17272717495821048356567995)
      ·
        refine ⟨25909076243731572534851993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17272717495821048356567995 25909076243731572534851993)
        ·
          refine ⟨19431807182798679401138995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25909076243731572534851993 19431807182798679401138995)
          ·
            refine ⟨29147710774198019101708493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19431807182798679401138995 29147710774198019101708493)
            ·
              refine ⟨10930391540324257163140685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29147710774198019101708493 10930391540324257163140685)
              ·
                refine ⟨4098896827621596436177757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10930391540324257163140685 4098896827621596436177757)
                ·
                  refine ⟨1537086310358098663566659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4098896827621596436177757 1537086310358098663566659)
                  ·
                    refine ⟨2305629465537147995349989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1537086310358098663566659 2305629465537147995349989)
                    ·
                      refine ⟨432305524788215249128123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2305629465537147995349989 432305524788215249128123)
                      ·
                        rfl

theorem cell23_841912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_841912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841912 prefixEnd_841912 := by exact prefixLift 841912
  have htrace : WordTrace (prefixWord ++ tailWord_841912) baseStart_841912 baseEnd_841912 := by
    simpa [prefixWord, tailWord_841912, baseEnd_841912] using wordTrace_append hprefix tailTrace_841912
  have hstable : (prefixWord ++ tailWord_841912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841912).length < 2 ^ (prefixWord ++ tailWord_841912).sum := by decide
  have hdescent : baseEnd_841912 < baseStart_841912 := by decide
  rcases family_descends (prefixWord ++ tailWord_841912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841916 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_841916 : Nat := 118140960795 + 841916 * 2 ^ 59
def prefixEnd_841916 : Nat := 4983230072969 + 3 ^ 40 * 841916 * 2
def baseEnd_841916 : Nat := 432307578710833233478105

theorem tailTrace_841916 : CollatzResearch.WordTrace tailWord_841916 prefixEnd_841916 432307578710833233478105 := by
  unfold tailWord_841916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353599608944797325188801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20471466145259729766918401 15353599608944797325188801)
  ·
    refine ⟨11515199706708597993891601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15353599608944797325188801 11515199706708597993891601)
    ·
      refine ⟨8636399780031448495418701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11515199706708597993891601 8636399780031448495418701)
      ·
        refine ⟨3238649917511793185782013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8636399780031448495418701 3238649917511793185782013)
        ·
          refine ⟨1214493719066922444668255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3238649917511793185782013 1214493719066922444668255)
          ·
            refine ⟨1821740578600383667002383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214493719066922444668255 1821740578600383667002383)
            ·
              refine ⟨2732610867900575500503575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821740578600383667002383 2732610867900575500503575)
              ·
                refine ⟨4098916301850863250755363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732610867900575500503575 4098916301850863250755363)
                ·
                  refine ⟨6148374452776294876133045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098916301850863250755363 6148374452776294876133045)
                  ·
                    refine ⟨576410104947777644637473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6148374452776294876133045 576410104947777644637473)
                    ·
                      refine ⟨432307578710833233478105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576410104947777644637473 432307578710833233478105)
                      ·
                        rfl

theorem cell23_841916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_841916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841916 prefixEnd_841916 := by exact prefixLift 841916
  have htrace : WordTrace (prefixWord ++ tailWord_841916) baseStart_841916 baseEnd_841916 := by
    simpa [prefixWord, tailWord_841916, baseEnd_841916] using wordTrace_append hprefix tailTrace_841916
  have hstable : (prefixWord ++ tailWord_841916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841916).length < 2 ^ (prefixWord ++ tailWord_841916).sum := by decide
  have hdescent : baseEnd_841916 < baseStart_841916 := by decide
  rcases family_descends (prefixWord ++ tailWord_841916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841935 : List Nat := [1, 1, 2, 1, 1, 3, 14]
def baseStart_841935 : Nat := 118140960795 + 841935 * 2 ^ 59
def prefixEnd_841935 : Nat := 4983230072969 + 3 ^ 40 * 841935 * 2
def baseEnd_841935 : Nat := 5337251047447761223957

theorem tailTrace_841935 : CollatzResearch.WordTrace tailWord_841935 prefixEnd_841935 5337251047447761223957 := by
  unfold tailWord_841935
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707892204820760895319259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20471928136547173930212839 30707892204820760895319259)
  ·
    refine ⟨46061838307231141342978889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30707892204820760895319259 46061838307231141342978889)
    ·
      refine ⟨34546378730423356007234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46061838307231141342978889 34546378730423356007234167)
      ·
        refine ⟨51819568095635034010851251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34546378730423356007234167 51819568095635034010851251)
        ·
          refine ⟨77729352143452551016276877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51819568095635034010851251 77729352143452551016276877)
          ·
            refine ⟨29148507053794706631103829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77729352143452551016276877 29148507053794706631103829)
            ·
              refine ⟨5337251047447761223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 29148507053794706631103829 5337251047447761223957)
              ·
                rfl

theorem cell23_841935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 14].length) (baseStart_841935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841935 prefixEnd_841935 := by exact prefixLift 841935
  have htrace : WordTrace (prefixWord ++ tailWord_841935) baseStart_841935 baseEnd_841935 := by
    simpa [prefixWord, tailWord_841935, baseEnd_841935] using wordTrace_append hprefix tailTrace_841935
  have hstable : (prefixWord ++ tailWord_841935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841935).length < 2 ^ (prefixWord ++ tailWord_841935).sum := by decide
  have hdescent : baseEnd_841935 < baseStart_841935 := by decide
  rcases family_descends (prefixWord ++ tailWord_841935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841946 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_841946 : Nat := 118140960795 + 841946 * 2 ^ 59
def prefixEnd_841946 : Nat := 4983230072969 + 3 ^ 40 * 841946 * 2
def baseEnd_841946 : Nat := 432322983130468116102967

theorem tailTrace_841946 : CollatzResearch.WordTrace tailWord_841946 prefixEnd_841946 432322983130468116102967 := by
  unfold tailWord_841946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677073351945227443492423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20472195605187273182646461 7677073351945227443492423)
  ·
    refine ⟨11515610027917841165238635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677073351945227443492423 11515610027917841165238635)
    ·
      refine ⟨17273415041876761747857953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515610027917841165238635 17273415041876761747857953)
      ·
        refine ⟨12955061281407571310893465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17273415041876761747857953 12955061281407571310893465)
        ·
          refine ⟨9716295961055678483170099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12955061281407571310893465 9716295961055678483170099)
          ·
            refine ⟨14574443941583517724755149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716295961055678483170099 14574443941583517724755149)
            ·
              refine ⟨5465416478093819146783181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14574443941583517724755149 5465416478093819146783181)
              ·
                refine ⟨2049531179285182180043693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5465416478093819146783181 2049531179285182180043693)
                ·
                  refine ⟨768574192231943317516385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2049531179285182180043693 768574192231943317516385)
                  ·
                    refine ⟨576430644173957488137289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768574192231943317516385 576430644173957488137289)
                    ·
                      refine ⟨432322983130468116102967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576430644173957488137289 432322983130468116102967)
                      ·
                        rfl

theorem cell23_841946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_841946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841946 prefixEnd_841946 := by exact prefixLift 841946
  have htrace : WordTrace (prefixWord ++ tailWord_841946) baseStart_841946 baseEnd_841946 := by
    simpa [prefixWord, tailWord_841946, baseEnd_841946] using wordTrace_append hprefix tailTrace_841946
  have hstable : (prefixWord ++ tailWord_841946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841946).length < 2 ^ (prefixWord ++ tailWord_841946).sum := by decide
  have hdescent : baseEnd_841946 < baseStart_841946 := by decide
  rcases family_descends (prefixWord ++ tailWord_841946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841949 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_841949 : Nat := 118140960795 + 841949 * 2 ^ 59
def prefixEnd_841949 : Nat := 4983230072969 + 3 ^ 40 * 841949 * 2
def baseEnd_841949 : Nat := 432324523572431604365453

theorem tailTrace_841949 : CollatzResearch.WordTrace tailWord_841949 prefixEnd_841949 432324523572431604365453 := by
  unfold tailWord_841949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708402826770041286328901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20472268551180027524219267 30708402826770041286328901)
  ·
    refine ⟨5757825530019382741186669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30708402826770041286328901 5757825530019382741186669)
    ·
      refine ⟨2159184573757268527945001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5757825530019382741186669 2159184573757268527945001)
      ·
        refine ⟨1619388430317951395958751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159184573757268527945001 1619388430317951395958751)
        ·
          refine ⟨2429082645476927093938127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619388430317951395958751 2429082645476927093938127)
          ·
            refine ⟨3643623968215390640907191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429082645476927093938127 3643623968215390640907191)
            ·
              refine ⟨5465435952323085961360787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643623968215390640907191 5465435952323085961360787)
              ·
                refine ⟨8198153928484628942041181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465435952323085961360787 8198153928484628942041181)
                ·
                  refine ⟨3074307723181735853265443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8198153928484628942041181 3074307723181735853265443)
                  ·
                    refine ⟨4611461584772603779898165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074307723181735853265443 4611461584772603779898165)
                    ·
                      refine ⟨432324523572431604365453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4611461584772603779898165 432324523572431604365453)
                      ·
                        rfl

theorem cell23_841949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_841949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841949 prefixEnd_841949 := by exact prefixLift 841949
  have htrace : WordTrace (prefixWord ++ tailWord_841949) baseStart_841949 baseEnd_841949 := by
    simpa [prefixWord, tailWord_841949, baseEnd_841949] using wordTrace_append hprefix tailTrace_841949
  have hstable : (prefixWord ++ tailWord_841949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841949).length < 2 ^ (prefixWord ++ tailWord_841949).sum := by decide
  have hdescent : baseEnd_841949 < baseStart_841949 := by decide
  rcases family_descends (prefixWord ++ tailWord_841949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841959 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_841959 : Nat := 118140960795 + 841959 * 2 ^ 59
def prefixEnd_841959 : Nat := 4983230072969 + 3 ^ 40 * 841959 * 2
def baseEnd_841959 : Nat := 432329658378976565240407

theorem tailTrace_841959 : CollatzResearch.WordTrace tailWord_841959 prefixEnd_841959 432329658378976565240407 := by
  unfold tailWord_841959
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708767556733812994192931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20472511704489208662795287 30708767556733812994192931)
  ·
    refine ⟨46063151335100719491289397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30708767556733812994192931 46063151335100719491289397)
    ·
      refine ⟨4318420437665692452308381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46063151335100719491289397 4318420437665692452308381)
      ·
        refine ⟨1619407664124634669615643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4318420437665692452308381 1619407664124634669615643)
        ·
          refine ⟨2429111496186952004423465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619407664124634669615643 2429111496186952004423465)
          ·
            refine ⟨1821833622140214003317599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429111496186952004423465 1821833622140214003317599)
            ·
              refine ⟨2732750433210321004976399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821833622140214003317599 2732750433210321004976399)
              ·
                refine ⟨4099125649815481507464599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732750433210321004976399 4099125649815481507464599)
                ·
                  refine ⟨6148688474723222261196899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099125649815481507464599 6148688474723222261196899)
                  ·
                    refine ⟨9223032712084833391795349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6148688474723222261196899 9223032712084833391795349)
                    ·
                      refine ⟨432329658378976565240407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9223032712084833391795349 432329658378976565240407)
                      ·
                        rfl

theorem cell23_841959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_841959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841959 prefixEnd_841959 := by exact prefixLift 841959
  have htrace : WordTrace (prefixWord ++ tailWord_841959) baseStart_841959 baseEnd_841959 := by
    simpa [prefixWord, tailWord_841959, baseEnd_841959] using wordTrace_append hprefix tailTrace_841959
  have hstable : (prefixWord ++ tailWord_841959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841959).length < 2 ^ (prefixWord ++ tailWord_841959).sum := by decide
  have hdescent : baseEnd_841959 < baseStart_841959 := by decide
  rcases family_descends (prefixWord ++ tailWord_841959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841980 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_841980 : Nat := 118140960795 + 841980 * 2 ^ 59
def prefixEnd_841980 : Nat := 4983230072969 + 3 ^ 40 * 841980 * 2
def baseEnd_841980 : Nat := 432340441472720983077811

theorem tailTrace_841980 : CollatzResearch.WordTrace tailWord_841980 prefixEnd_841980 432340441472720983077811 := by
  unfold tailWord_841980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15354766744828866790353697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20473022326438489053804929 15354766744828866790353697)
  ·
    refine ⟨11516075058621650092765273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15354766744828866790353697 11516075058621650092765273)
    ·
      refine ⟨8637056293966237569573955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11516075058621650092765273 8637056293966237569573955)
      ·
        refine ⟨12955584440949356354360933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8637056293966237569573955 12955584440949356354360933)
        ·
          refine ⟨2429172082678004316442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12955584440949356354360933 2429172082678004316442675)
          ·
            refine ⟨3643758124017006474664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429172082678004316442675 3643758124017006474664013)
            ·
              refine ⟨1366409296506377427999005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3643758124017006474664013 1366409296506377427999005)
              ·
                refine ⟨512403486189891535499627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1366409296506377427999005 512403486189891535499627)
                ·
                  refine ⟨768605229284837303249441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512403486189891535499627 768605229284837303249441)
                  ·
                    refine ⟨576453921963627977437081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768605229284837303249441 576453921963627977437081)
                    ·
                      refine ⟨432340441472720983077811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576453921963627977437081 432340441472720983077811)
                      ·
                        rfl

theorem cell23_841980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_841980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841980 prefixEnd_841980 := by exact prefixLift 841980
  have htrace : WordTrace (prefixWord ++ tailWord_841980) baseStart_841980 baseEnd_841980 := by
    simpa [prefixWord, tailWord_841980, baseEnd_841980] using wordTrace_append hprefix tailTrace_841980
  have hstable : (prefixWord ++ tailWord_841980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841980).length < 2 ^ (prefixWord ++ tailWord_841980).sum := by decide
  have hdescent : baseEnd_841980 < baseStart_841980 := by decide
  rcases family_descends (prefixWord ++ tailWord_841980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841996 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_841996 : Nat := 118140960795 + 841996 * 2 ^ 59
def prefixEnd_841996 : Nat := 4983230072969 + 3 ^ 40 * 841996 * 2
def baseEnd_841996 : Nat := 432348657163192920477737

theorem tailTrace_841996 : CollatzResearch.WordTrace tailWord_841996 prefixEnd_841996 432348657163192920477737 := by
  unfold tailWord_841996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355058528799884156644921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20473411371733178875526561 15355058528799884156644921)
  ·
    refine ⟨11516293896599913117483691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15355058528799884156644921 11516293896599913117483691)
    ·
      refine ⟨17274440844899869676225537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11516293896599913117483691 17274440844899869676225537)
      ·
        refine ⟨12955830633674902257169153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17274440844899869676225537 12955830633674902257169153)
        ·
          refine ⟨9716872975256176692876865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12955830633674902257169153 9716872975256176692876865)
          ·
            refine ⟨7287654731442132519657649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9716872975256176692876865 7287654731442132519657649)
            ·
              refine ⟨5465741048581599389743237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7287654731442132519657649 5465741048581599389743237)
              ·
                refine ⟨1024826446609049885576857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5465741048581599389743237 1024826446609049885576857)
                ·
                  refine ⟨768619834956787414182643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024826446609049885576857 768619834956787414182643)
                  ·
                    refine ⟨1152929752435181121273965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768619834956787414182643 1152929752435181121273965)
                    ·
                      refine ⟨432348657163192920477737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1152929752435181121273965 432348657163192920477737)
                      ·
                        rfl

theorem cell23_841996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_841996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_841996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_841996 prefixEnd_841996 := by exact prefixLift 841996
  have htrace : WordTrace (prefixWord ++ tailWord_841996) baseStart_841996 baseEnd_841996 := by
    simpa [prefixWord, tailWord_841996, baseEnd_841996] using wordTrace_append hprefix tailTrace_841996
  have hstable : (prefixWord ++ tailWord_841996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841996).length < 2 ^ (prefixWord ++ tailWord_841996).sum := by decide
  have hdescent : baseEnd_841996 < baseStart_841996 := by decide
  rcases family_descends (prefixWord ++ tailWord_841996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842012 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_842012 : Nat := 118140960795 + 842012 * 2 ^ 59
def prefixEnd_842012 : Nat := 4983230072969 + 3 ^ 40 * 842012 * 2
def baseEnd_842012 : Nat := 144118957617888285959221

theorem tailTrace_842012 : CollatzResearch.WordTrace tailWord_842012 prefixEnd_842012 144118957617888285959221 := by
  unfold tailWord_842012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355350312770901522936145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20473800417027868697248193 15355350312770901522936145)
  ·
    refine ⟨11516512734578176142202109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15355350312770901522936145 11516512734578176142202109)
    ·
      refine ⟨4318692275466816053325791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11516512734578176142202109 4318692275466816053325791)
      ·
        refine ⟨6478038413200224079988687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318692275466816053325791 6478038413200224079988687)
        ·
          refine ⟨9717057619800336119983031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478038413200224079988687 9717057619800336119983031)
          ·
            refine ⟨14575586429700504179974547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717057619800336119983031 14575586429700504179974547)
            ·
              refine ⟨21863379644550756269961821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575586429700504179974547 21863379644550756269961821)
              ·
                refine ⟨8198767366706533601235683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21863379644550756269961821 8198767366706533601235683)
                ·
                  refine ⟨12298151050059800401853525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8198767366706533601235683 12298151050059800401853525)
                  ·
                    refine ⟨144118957617888285959221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12298151050059800401853525 144118957617888285959221)
                    ·
                      rfl

theorem cell23_842012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_842012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842012 prefixEnd_842012 := by exact prefixLift 842012
  have htrace : WordTrace (prefixWord ++ tailWord_842012) baseStart_842012 baseEnd_842012 := by
    simpa [prefixWord, tailWord_842012, baseEnd_842012] using wordTrace_append hprefix tailTrace_842012
  have hstable : (prefixWord ++ tailWord_842012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842012).length < 2 ^ (prefixWord ++ tailWord_842012).sum := by decide
  have hdescent : baseEnd_842012 < baseStart_842012 := by decide
  rcases family_descends (prefixWord ++ tailWord_842012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842032 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_842032 : Nat := 118140960795 + 842032 * 2 ^ 59
def prefixEnd_842032 : Nat := 4983230072969 + 3 ^ 40 * 842032 * 2
def baseEnd_842032 : Nat := 432367142466754779627571

theorem tailTrace_842032 : CollatzResearch.WordTrace tailWord_842032 prefixEnd_842032 432367142466754779627571 := by
  unfold tailWord_842032
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355715042734673230800175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20474286723646230974400233 15355715042734673230800175)
  ·
    refine ⟨23033572564102009846200263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15355715042734673230800175 23033572564102009846200263)
    ·
      refine ⟨34550358846153014769300395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23033572564102009846200263 34550358846153014769300395)
      ·
        refine ⟨51825538269229522153950593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34550358846153014769300395 51825538269229522153950593)
        ·
          refine ⟨38869153701922141615462945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51825538269229522153950593 38869153701922141615462945)
          ·
            refine ⟨29151865276441606211597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38869153701922141615462945 29151865276441606211597209)
            ·
              refine ⟨21863898957331204658697907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29151865276441606211597209 21863898957331204658697907)
              ·
                refine ⟨32795848435996806988046861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863898957331204658697907 32795848435996806988046861)
                ·
                  refine ⟨12298443163498802620517573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32795848435996806988046861 12298443163498802620517573)
                  ·
                    refine ⟨2305958093156025491347045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12298443163498802620517573 2305958093156025491347045)
                    ·
                      refine ⟨432367142466754779627571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2305958093156025491347045 432367142466754779627571)
                      ·
                        rfl

theorem cell23_842032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_842032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842032 prefixEnd_842032 := by exact prefixLift 842032
  have htrace : WordTrace (prefixWord ++ tailWord_842032) baseStart_842032 baseEnd_842032 := by
    simpa [prefixWord, tailWord_842032, baseEnd_842032] using wordTrace_append hprefix tailTrace_842032
  have hstable : (prefixWord ++ tailWord_842032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842032).length < 2 ^ (prefixWord ++ tailWord_842032).sum := by decide
  have hdescent : baseEnd_842032 < baseStart_842032 := by decide
  rcases family_descends (prefixWord ++ tailWord_842032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842126 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_842126 : Nat := 118140960795 + 842126 * 2 ^ 59
def prefixEnd_842126 : Nat := 4983230072969 + 3 ^ 40 * 842126 * 2
def baseEnd_842126 : Nat := 432415409648277411852139

theorem tailTrace_842126 : CollatzResearch.WordTrace tailWord_842126 prefixEnd_842126 432415409648277411852139 := by
  unfold tailWord_842126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839357318391100064440279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20476572364752533677014821 3839357318391100064440279)
  ·
    refine ⟨5759035977586650096660419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839357318391100064440279 5759035977586650096660419)
    ·
      refine ⟨8638553966379975144990629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759035977586650096660419 8638553966379975144990629)
      ·
        refine ⟨1619728868696245339685743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8638553966379975144990629 1619728868696245339685743)
        ·
          refine ⟨2429593303044368009528615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619728868696245339685743 2429593303044368009528615)
          ·
            refine ⟨3644389954566552014292923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429593303044368009528615 3644389954566552014292923)
            ·
              refine ⟨5466584931849828021439385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644389954566552014292923 5466584931849828021439385)
              ·
                refine ⟨4099938698887371016079539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466584931849828021439385 4099938698887371016079539)
                ·
                  refine ⟨6149908048331056524119309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099938698887371016079539 6149908048331056524119309)
                  ·
                    refine ⟨2306215518124146196544741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6149908048331056524119309 2306215518124146196544741)
                    ·
                      refine ⟨432415409648277411852139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2306215518124146196544741 432415409648277411852139)
                      ·
                        rfl

theorem cell23_842126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_842126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842126 prefixEnd_842126 := by exact prefixLift 842126
  have htrace : WordTrace (prefixWord ++ tailWord_842126) baseStart_842126 baseEnd_842126 := by
    simpa [prefixWord, tailWord_842126, baseEnd_842126] using wordTrace_append hprefix tailTrace_842126
  have hstable : (prefixWord ++ tailWord_842126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842126).length < 2 ^ (prefixWord ++ tailWord_842126).sum := by decide
  have hdescent : baseEnd_842126 < baseStart_842126 := by decide
  rcases family_descends (prefixWord ++ tailWord_842126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842146 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_842146 : Nat := 118140960795 + 842146 * 2 ^ 59
def prefixEnd_842146 : Nat := 4983230072969 + 3 ^ 40 * 842146 * 2
def baseEnd_842146 : Nat := 432425679261367333602047

theorem tailTrace_842146 : CollatzResearch.WordTrace tailWord_842146 prefixEnd_842146 432425679261367333602047 := by
  unfold tailWord_842146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7678897001764085982812573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20477058671370895954166861 7678897001764085982812573)
  ·
    refine ⟨2879586375661532243554715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7678897001764085982812573 2879586375661532243554715)
    ·
      refine ⟨4319379563492298365332073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879586375661532243554715 4319379563492298365332073)
      ·
        refine ⟨3239534672619223773999055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4319379563492298365332073 3239534672619223773999055)
        ·
          refine ⟨4859302008928835660998583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239534672619223773999055 4859302008928835660998583)
          ·
            refine ⟨7288953013393253491497875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859302008928835660998583 7288953013393253491497875)
            ·
              refine ⟨10933429520089880237246813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288953013393253491497875 10933429520089880237246813)
              ·
                refine ⟨4100036070033705088967555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10933429520089880237246813 4100036070033705088967555)
                ·
                  refine ⟨6150054105050557633451333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100036070033705088967555 6150054105050557633451333)
                  ·
                    refine ⟨1153135144696979556272125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150054105050557633451333 1153135144696979556272125)
                    ·
                      refine ⟨432425679261367333602047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1153135144696979556272125 432425679261367333602047)
                      ·
                        rfl

theorem cell23_842146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_842146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842146 prefixEnd_842146 := by exact prefixLift 842146
  have htrace : WordTrace (prefixWord ++ tailWord_842146) baseStart_842146 baseEnd_842146 := by
    simpa [prefixWord, tailWord_842146, baseEnd_842146] using wordTrace_append hprefix tailTrace_842146
  have hstable : (prefixWord ++ tailWord_842146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842146).length < 2 ^ (prefixWord ++ tailWord_842146).sum := by decide
  have hdescent : baseEnd_842146 < baseStart_842146 := by decide
  rcases family_descends (prefixWord ++ tailWord_842146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842179 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 3, 5]
def baseStart_842179 : Nat := 118140960795 + 842179 * 2 ^ 59
def prefixEnd_842179 : Nat := 4983230072969 + 3 ^ 40 * 842179 * 2
def baseEnd_842179 : Nat := 144147541374321901496465

theorem tailTrace_842179 : CollatzResearch.WordTrace tailWord_842179 prefixEnd_842179 144147541374321901496465 := by
  unfold tailWord_842179
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716791615936790567201591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477861077291193711467727 30716791615936790567201591)
  ·
    refine ⟨46075187423905185850802387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30716791615936790567201591 46075187423905185850802387)
    ·
      refine ⟨69112781135857778776203581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46075187423905185850802387 69112781135857778776203581)
      ·
        refine ⟨25917292925946667041076343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69112781135857778776203581 25917292925946667041076343)
        ·
          refine ⟨38875939388920000561614515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25917292925946667041076343 38875939388920000561614515)
          ·
            refine ⟨58313909083380000842421773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38875939388920000561614515 58313909083380000842421773)
            ·
              refine ⟨21867715906267500315908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58313909083380000842421773 21867715906267500315908165)
              ·
                refine ⟨4100196732425156309232781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21867715906267500315908165 4100196732425156309232781)
                ·
                  refine ⟨1537573774659433615962293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100196732425156309232781 1537573774659433615962293)
                  ·
                    refine ⟨144147541374321901496465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1537573774659433615962293 144147541374321901496465)
                    ·
                      rfl

theorem cell23_842179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].length) (baseStart_842179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842179 prefixEnd_842179 := by exact prefixLift 842179
  have htrace : WordTrace (prefixWord ++ tailWord_842179) baseStart_842179 baseEnd_842179 := by
    simpa [prefixWord, tailWord_842179, baseEnd_842179] using wordTrace_append hprefix tailTrace_842179
  have hstable : (prefixWord ++ tailWord_842179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842179).length < 2 ^ (prefixWord ++ tailWord_842179).sum := by decide
  have hdescent : baseEnd_842179 < baseStart_842179 := by decide
  rcases family_descends (prefixWord ++ tailWord_842179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842183 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 6]
def baseStart_842183 : Nat := 118140960795 + 842183 * 2 ^ 59
def prefixEnd_842183 : Nat := 4983230072969 + 3 ^ 40 * 842183 * 2
def baseEnd_842183 : Nat := 48049408671731520982153

theorem tailTrace_842183 : CollatzResearch.WordTrace tailWord_842183 prefixEnd_842183 48049408671731520982153 := by
  unfold tailWord_842183
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716937507922299250347203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477958338614866166898135 30716937507922299250347203)
  ·
    refine ⟨46075406261883448875520805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30716937507922299250347203 46075406261883448875520805)
    ·
      refine ⟨8639138674103146664160151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46075406261883448875520805 8639138674103146664160151)
      ·
        refine ⟨12958708011154719996240227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639138674103146664160151 12958708011154719996240227)
        ·
          refine ⟨19438062016732079994360341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958708011154719996240227 19438062016732079994360341)
          ·
            refine ⟨911159157034316249735641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19438062016732079994360341 911159157034316249735641)
            ·
              refine ⟨683369367775737187301731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911159157034316249735641 683369367775737187301731)
              ·
                refine ⟨1025054051663605780952597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683369367775737187301731 1025054051663605780952597)
                ·
                  refine ⟨48049408671731520982153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1025054051663605780952597 48049408671731520982153)
                  ·
                    rfl

theorem cell23_842183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 6].length) (baseStart_842183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842183 prefixEnd_842183 := by exact prefixLift 842183
  have htrace : WordTrace (prefixWord ++ tailWord_842183) baseStart_842183 baseEnd_842183 := by
    simpa [prefixWord, tailWord_842183, baseEnd_842183] using wordTrace_append hprefix tailTrace_842183
  have hstable : (prefixWord ++ tailWord_842183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842183).length < 2 ^ (prefixWord ++ tailWord_842183).sum := by decide
  have hdescent : baseEnd_842183 < baseStart_842183 := by decide
  rcases family_descends (prefixWord ++ tailWord_842183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842250 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_842250 : Nat := 118140960795 + 842250 * 2 ^ 59
def prefixEnd_842250 : Nat := 4983230072969 + 3 ^ 40 * 842250 * 2
def baseEnd_842250 : Nat := 432479081249434926701569

theorem tailTrace_842250 : CollatzResearch.WordTrace tailWord_842250 prefixEnd_842250 432479081249434926701569 := by
  unfold tailWord_842250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679845299669892423259051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20479587465786379795357469 7679845299669892423259051)
  ·
    refine ⟨11519767949504838634888577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7679845299669892423259051 11519767949504838634888577)
    ·
      refine ⟨8639825962128628976166433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11519767949504838634888577 8639825962128628976166433)
      ·
        refine ⟨6479869471596471732124825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639825962128628976166433 6479869471596471732124825)
        ·
          refine ⟨4859902103697353799093619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479869471596471732124825 4859902103697353799093619)
          ·
            refine ⟨7289853155546030698640429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859902103697353799093619 7289853155546030698640429)
            ·
              refine ⟨2733694933329761511990161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7289853155546030698640429 2733694933329761511990161)
              ·
                refine ⟨2050271199997321133992621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733694933329761511990161 2050271199997321133992621)
                ·
                  refine ⟨768851699998995425247233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2050271199997321133992621 768851699998995425247233)
                  ·
                    refine ⟨576638774999246568935425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768851699998995425247233 576638774999246568935425)
                    ·
                      refine ⟨432479081249434926701569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576638774999246568935425 432479081249434926701569)
                      ·
                        rfl

theorem cell23_842250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_842250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842250 prefixEnd_842250 := by exact prefixLift 842250
  have htrace : WordTrace (prefixWord ++ tailWord_842250) baseStart_842250 baseEnd_842250 := by
    simpa [prefixWord, tailWord_842250, baseEnd_842250] using wordTrace_append hprefix tailTrace_842250
  have hstable : (prefixWord ++ tailWord_842250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842250).length < 2 ^ (prefixWord ++ tailWord_842250).sum := by decide
  have hdescent : baseEnd_842250 < baseStart_842250 := by decide
  rcases family_descends (prefixWord ++ tailWord_842250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 8]
def baseStart_842299 : Nat := 118140960795 + 842299 * 2 ^ 59
def prefixEnd_842299 : Nat := 4983230072969 + 3 ^ 40 * 842299 * 2
def baseEnd_842299 : Nat := 144168080600501744996281

theorem tailTrace_842299 : CollatzResearch.WordTrace tailWord_842299 prefixEnd_842299 144168080600501744996281 := by
  unfold tailWord_842299
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721168375502051061569951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20480778917001367374379967 30721168375502051061569951)
  ·
    refine ⟨46081752563253076592354927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721168375502051061569951 46081752563253076592354927)
    ·
      refine ⟨69122628844879614888532391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46081752563253076592354927 69122628844879614888532391)
      ·
        refine ⟨103683943267319422332798587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69122628844879614888532391 103683943267319422332798587)
        ·
          refine ⟨155525914900979133499197881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103683943267319422332798587 155525914900979133499197881)
          ·
            refine ⟨116644436175734350124398411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155525914900979133499197881 116644436175734350124398411)
            ·
              refine ⟨174966654263601525186597617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116644436175734350124398411 174966654263601525186597617)
              ·
                refine ⟨131224990697701143889948213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174966654263601525186597617 131224990697701143889948213)
                ·
                  refine ⟨12302342877909482239682645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131224990697701143889948213 12302342877909482239682645)
                  ·
                    refine ⟨144168080600501744996281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12302342877909482239682645 144168080600501744996281)
                    ·
                      rfl

theorem cell23_842299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_842299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842299 prefixEnd_842299 := by exact prefixLift 842299
  have htrace : WordTrace (prefixWord ++ tailWord_842299) baseStart_842299 baseEnd_842299 := by
    simpa [prefixWord, tailWord_842299, baseEnd_842299] using wordTrace_append hprefix tailTrace_842299
  have hstable : (prefixWord ++ tailWord_842299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842299).length < 2 ^ (prefixWord ++ tailWord_842299).sum := by decide
  have hdescent : baseEnd_842299 < baseStart_842299 := by decide
  rcases family_descends (prefixWord ++ tailWord_842299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842300 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_842300 : Nat := 118140960795 + 842300 * 2 ^ 59
def prefixEnd_842300 : Nat := 4983230072969 + 3 ^ 40 * 842300 * 2
def baseEnd_842300 : Nat := 432504755282159731076339

theorem tailTrace_842300 : CollatzResearch.WordTrace tailWord_842300 prefixEnd_842300 432504755282159731076339 := by
  unfold tailWord_842300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360602424249214116178177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20480803232332285488237569 15360602424249214116178177)
  ·
    refine ⟨11520451818186910587133633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15360602424249214116178177 11520451818186910587133633)
    ·
      refine ⟨8640338863640182940350225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520451818186910587133633 8640338863640182940350225)
      ·
        refine ⟨6480254147730137205262669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8640338863640182940350225 6480254147730137205262669)
        ·
          refine ⟨2430095305398801451973501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6480254147730137205262669 2430095305398801451973501)
          ·
            refine ⟨911285739524550544490063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430095305398801451973501 911285739524550544490063)
            ·
              refine ⟨1366928609286825816735095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911285739524550544490063 1366928609286825816735095)
              ·
                refine ⟨2050392913930238725102643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366928609286825816735095 2050392913930238725102643)
                ·
                  refine ⟨3075589370895358087653965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050392913930238725102643 3075589370895358087653965)
                  ·
                    refine ⟨1153346014085759282870237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075589370895358087653965 1153346014085759282870237)
                    ·
                      refine ⟨432504755282159731076339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1153346014085759282870237 432504755282159731076339)
                      ·
                        rfl

theorem cell23_842300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_842300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842300 prefixEnd_842300 := by exact prefixLift 842300
  have htrace : WordTrace (prefixWord ++ tailWord_842300) baseStart_842300 baseEnd_842300 := by
    simpa [prefixWord, tailWord_842300, baseEnd_842300] using wordTrace_append hprefix tailTrace_842300
  have hstable : (prefixWord ++ tailWord_842300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842300).length < 2 ^ (prefixWord ++ tailWord_842300).sum := by decide
  have hdescent : baseEnd_842300 < baseStart_842300 := by decide
  rcases family_descends (prefixWord ++ tailWord_842300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842336 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_842336 : Nat := 118140960795 + 842336 * 2 ^ 59
def prefixEnd_842336 : Nat := 4983230072969 + 3 ^ 40 * 842336 * 2
def baseEnd_842336 : Nat := 432523240585721590226173

theorem tailTrace_842336 : CollatzResearch.WordTrace tailWord_842336 prefixEnd_842336 432523240585721590226173 := by
  unfold tailWord_842336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361258938184003190333431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20481678584245337587111241 15361258938184003190333431)
  ·
    refine ⟨23041888407276004785500147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15361258938184003190333431 23041888407276004785500147)
    ·
      refine ⟨34562832610914007178250221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23041888407276004785500147 34562832610914007178250221)
      ·
        refine ⟨12961062229092752691843833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34562832610914007178250221 12961062229092752691843833)
        ·
          refine ⟨9720796671819564518882875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12961062229092752691843833 9720796671819564518882875)
          ·
            refine ⟨14581195007729346778324313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720796671819564518882875 14581195007729346778324313)
            ·
              refine ⟨10935896255797010083743235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14581195007729346778324313 10935896255797010083743235)
              ·
                refine ⟨16403844383695515125614853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935896255797010083743235 16403844383695515125614853)
                ·
                  refine ⟨3075720821942909086052785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16403844383695515125614853 3075720821942909086052785)
                  ·
                    refine ⟨2306790616457181814539589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075720821942909086052785 2306790616457181814539589)
                    ·
                      refine ⟨432523240585721590226173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2306790616457181814539589 432523240585721590226173)
                      ·
                        rfl

theorem cell23_842336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_842336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842336 prefixEnd_842336 := by exact prefixLift 842336
  have htrace : WordTrace (prefixWord ++ tailWord_842336) baseStart_842336 baseEnd_842336 := by
    simpa [prefixWord, tailWord_842336, baseEnd_842336] using wordTrace_append hprefix tailTrace_842336
  have hstable : (prefixWord ++ tailWord_842336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842336).length < 2 ^ (prefixWord ++ tailWord_842336).sum := by decide
  have hdescent : baseEnd_842336 < baseStart_842336 := by decide
  rcases family_descends (prefixWord ++ tailWord_842336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842340 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_842340 : Nat := 118140960795 + 842340 * 2 ^ 59
def prefixEnd_842340 : Nat := 4983230072969 + 3 ^ 40 * 842340 * 2
def baseEnd_842340 : Nat := 432525294508339574576155

theorem tailTrace_842340 : CollatzResearch.WordTrace tailWord_842340 prefixEnd_842340 432525294508339574576155 := by
  unfold tailWord_842340
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361331884176757531906237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20481775845569010042541649 15361331884176757531906237)
  ·
    refine ⟨5760499456566284074464839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15361331884176757531906237 5760499456566284074464839)
    ·
      refine ⟨8640749184849426111697259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760499456566284074464839 8640749184849426111697259)
      ·
        refine ⟨12961123777274139167545889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640749184849426111697259 12961123777274139167545889)
        ·
          refine ⟨9720842832955604375659417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12961123777274139167545889 9720842832955604375659417)
          ·
            refine ⟨7290632124716703281744563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9720842832955604375659417 7290632124716703281744563)
            ·
              refine ⟨10935948187075054922616845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290632124716703281744563 10935948187075054922616845)
              ·
                refine ⟨4100980570153145595981317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10935948187075054922616845 4100980570153145595981317)
                ·
                  refine ⟨768933856903714799246497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4100980570153145595981317 768933856903714799246497)
                  ·
                    refine ⟨576700392677786099434873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768933856903714799246497 576700392677786099434873)
                    ·
                      refine ⟨432525294508339574576155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576700392677786099434873 432525294508339574576155)
                      ·
                        rfl

theorem cell23_842340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_842340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842340 prefixEnd_842340 := by exact prefixLift 842340
  have htrace : WordTrace (prefixWord ++ tailWord_842340) baseStart_842340 baseEnd_842340 := by
    simpa [prefixWord, tailWord_842340, baseEnd_842340] using wordTrace_append hprefix tailTrace_842340
  have hstable : (prefixWord ++ tailWord_842340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842340).length < 2 ^ (prefixWord ++ tailWord_842340).sum := by decide
  have hdescent : baseEnd_842340 < baseStart_842340 := by decide
  rcases family_descends (prefixWord ++ tailWord_842340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842407 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_842407 : Nat := 118140960795 + 842407 * 2 ^ 59
def prefixEnd_842407 : Nat := 4983230072969 + 3 ^ 40 * 842407 * 2
def baseEnd_842407 : Nat := 432559697712190812438347

theorem tailTrace_842407 : CollatzResearch.WordTrace tailWord_842407 prefixEnd_842407 432559697712190812438347 := by
  unfold tailWord_842407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725107459110785506501475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20483404972740523671000983 30725107459110785506501475)
  ·
    refine ⟨46087661188666178259752213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30725107459110785506501475 46087661188666178259752213)
    ·
      refine ⟨2160359118218727105925885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46087661188666178259752213 2160359118218727105925885)
      ·
        refine ⟨810134669332022664722207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2160359118218727105925885 810134669332022664722207)
        ·
          refine ⟨1215202003998033997083311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810134669332022664722207 1215202003998033997083311)
          ·
            refine ⟨1822803005997050995624967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215202003998033997083311 1822803005997050995624967)
            ·
              refine ⟨2734204508995576493437451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822803005997050995624967 2734204508995576493437451)
              ·
                refine ⟨4101306763493364740156177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734204508995576493437451 4101306763493364740156177)
                ·
                  refine ⟨3075980072620023555117133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4101306763493364740156177 3075980072620023555117133)
                  ·
                    refine ⟨1153492527232508833168925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075980072620023555117133 1153492527232508833168925)
                    ·
                      refine ⟨432559697712190812438347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1153492527232508833168925 432559697712190812438347)
                      ·
                        rfl

theorem cell23_842407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_842407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842407 prefixEnd_842407 := by exact prefixLift 842407
  have htrace : WordTrace (prefixWord ++ tailWord_842407) baseStart_842407 baseEnd_842407 := by
    simpa [prefixWord, tailWord_842407, baseEnd_842407] using wordTrace_append hprefix tailTrace_842407
  have hstable : (prefixWord ++ tailWord_842407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842407).length < 2 ^ (prefixWord ++ tailWord_842407).sum := by decide
  have hdescent : baseEnd_842407 < baseStart_842407 := by decide
  rcases family_descends (prefixWord ++ tailWord_842407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842430 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_842430 : Nat := 118140960795 + 842430 * 2 ^ 59
def prefixEnd_842430 : Nat := 4983230072969 + 3 ^ 40 * 842430 * 2
def baseEnd_842430 : Nat := 432571507767244222450741

theorem tailTrace_842430 : CollatzResearch.WordTrace tailWord_842430 prefixEnd_842430 432571507767244222450741 := by
  unfold tailWord_842430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840743292253432554323593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20483964225351640289725829 3840743292253432554323593)
  ·
    refine ⟨2880557469190074415742695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840743292253432554323593 2880557469190074415742695)
    ·
      refine ⟨4320836203785111623614043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880557469190074415742695 4320836203785111623614043)
      ·
        refine ⟨6481254305677667435421065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320836203785111623614043 6481254305677667435421065)
        ·
          refine ⟨4860940729258250576565799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6481254305677667435421065 4860940729258250576565799)
          ·
            refine ⟨7291411093887375864848699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860940729258250576565799 7291411093887375864848699)
            ·
              refine ⟨10937116640831063797273049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291411093887375864848699 10937116640831063797273049)
              ·
                refine ⟨8202837480623297847954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10937116640831063797273049 8202837480623297847954787)
                ·
                  refine ⟨12304256220934946771932181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202837480623297847954787 12304256220934946771932181)
                  ·
                    refine ⟨576762010356325629934321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12304256220934946771932181 576762010356325629934321)
                    ·
                      refine ⟨432571507767244222450741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576762010356325629934321 432571507767244222450741)
                      ·
                        rfl

theorem cell23_842430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_842430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842430 prefixEnd_842430 := by exact prefixLift 842430
  have htrace : WordTrace (prefixWord ++ tailWord_842430) baseStart_842430 baseEnd_842430 := by
    simpa [prefixWord, tailWord_842430, baseEnd_842430] using wordTrace_append hprefix tailTrace_842430
  have hstable : (prefixWord ++ tailWord_842430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842430).length < 2 ^ (prefixWord ++ tailWord_842430).sum := by decide
  have hdescent : baseEnd_842430 < baseStart_842430 := by decide
  rcases family_descends (prefixWord ++ tailWord_842430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842480 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_842480 : Nat := 118140960795 + 842480 * 2 ^ 59
def prefixEnd_842480 : Nat := 4983230072969 + 3 ^ 40 * 842480 * 2
def baseEnd_842480 : Nat := 432597181799969026825511

theorem tailTrace_842480 : CollatzResearch.WordTrace tailWord_842480 prefixEnd_842480 432597181799969026825511 := by
  unfold tailWord_842480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363884993923159486954447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20485179991897545982605929 15363884993923159486954447)
  ·
    refine ⟨23045827490884739230431671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15363884993923159486954447 23045827490884739230431671)
    ·
      refine ⟨34568741236327108845647507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23045827490884739230431671 34568741236327108845647507)
      ·
        refine ⟨51853111854490663268471261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34568741236327108845647507 51853111854490663268471261)
        ·
          refine ⟨19444916945433998725676723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51853111854490663268471261 19444916945433998725676723)
          ·
            refine ⟨29167375418150998088515085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444916945433998725676723 29167375418150998088515085)
            ·
              refine ⟨10937765781806624283193157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29167375418150998088515085 10937765781806624283193157)
              ·
                refine ⟨2050831084088742053098717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10937765781806624283193157 2050831084088742053098717)
                ·
                  refine ⟨769061656533278269912019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2050831084088742053098717 769061656533278269912019)
                  ·
                    refine ⟨1153592484799917404868029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 769061656533278269912019 1153592484799917404868029)
                    ·
                      refine ⟨432597181799969026825511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1153592484799917404868029 432597181799969026825511)
                      ·
                        rfl

theorem cell23_842480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_842480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842480 prefixEnd_842480 := by exact prefixLift 842480
  have htrace : WordTrace (prefixWord ++ tailWord_842480) baseStart_842480 baseEnd_842480 := by
    simpa [prefixWord, tailWord_842480, baseEnd_842480] using wordTrace_append hprefix tailTrace_842480
  have hstable : (prefixWord ++ tailWord_842480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842480).length < 2 ^ (prefixWord ++ tailWord_842480).sum := by decide
  have hdescent : baseEnd_842480 < baseStart_842480 := by decide
  rcases family_descends (prefixWord ++ tailWord_842480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842490 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_842490 : Nat := 118140960795 + 842490 * 2 ^ 59
def prefixEnd_842490 : Nat := 4983230072969 + 3 ^ 40 * 842490 * 2
def baseEnd_842490 : Nat := 432602316606513987700465

theorem tailTrace_842490 : CollatzResearch.WordTrace tailWord_842490 prefixEnd_842490 432602316606513987700465 := by
  unfold tailWord_842490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682033679452522670443231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20485423145206727121181949 7682033679452522670443231)
  ·
    refine ⟨11523050519178784005664847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682033679452522670443231 11523050519178784005664847)
    ·
      refine ⟨17284575778768176008497271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523050519178784005664847 17284575778768176008497271)
      ·
        refine ⟨25926863668152264012745907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17284575778768176008497271 25926863668152264012745907)
        ·
          refine ⟨38890295502228396019118861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25926863668152264012745907 38890295502228396019118861)
          ·
            refine ⟨14583860813335648507169573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38890295502228396019118861 14583860813335648507169573)
            ·
              refine ⟨2734473902500434095094295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14583860813335648507169573 2734473902500434095094295)
              ·
                refine ⟨4101710853750651142641443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734473902500434095094295 4101710853750651142641443)
                ·
                  refine ⟨6152566280625976713962165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101710853750651142641443 6152566280625976713962165)
                  ·
                    refine ⟨576803088808685316933953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6152566280625976713962165 576803088808685316933953)
                    ·
                      refine ⟨432602316606513987700465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576803088808685316933953 432602316606513987700465)
                      ·
                        rfl

theorem cell23_842490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_842490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842490 prefixEnd_842490 := by exact prefixLift 842490
  have htrace : WordTrace (prefixWord ++ tailWord_842490) baseStart_842490 baseEnd_842490 := by
    simpa [prefixWord, tailWord_842490, baseEnd_842490] using wordTrace_append hprefix tailTrace_842490
  have hstable : (prefixWord ++ tailWord_842490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842490).length < 2 ^ (prefixWord ++ tailWord_842490).sum := by decide
  have hdescent : baseEnd_842490 < baseStart_842490 := by decide
  rcases family_descends (prefixWord ++ tailWord_842490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842500 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_842500 : Nat := 118140960795 + 842500 * 2 ^ 59
def prefixEnd_842500 : Nat := 4983230072969 + 3 ^ 40 * 842500 * 2
def baseEnd_842500 : Nat := 144202483804352982858473

theorem tailTrace_842500 : CollatzResearch.WordTrace tailWord_842500 prefixEnd_842500 144202483804352982858473 := by
  unfold tailWord_842500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364249723886931194818477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20485666298515908259757969 15364249723886931194818477)
  ·
    refine ⟨5761593646457599198056929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15364249723886931194818477 5761593646457599198056929)
    ·
      refine ⟨4321195234843199398542697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5761593646457599198056929 4321195234843199398542697)
      ·
        refine ⟨3240896426132399548907023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4321195234843199398542697 3240896426132399548907023)
        ·
          refine ⟨4861344639198599323360535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240896426132399548907023 4861344639198599323360535)
          ·
            refine ⟨7292016958797898985040803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861344639198599323360535 7292016958797898985040803)
            ·
              refine ⟨10938025438196848477561205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292016958797898985040803 10938025438196848477561205)
              ·
                refine ⟨1025439884830954544771363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10938025438196848477561205 1025439884830954544771363)
                ·
                  refine ⟨1538159827246431817157045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025439884830954544771363 1538159827246431817157045)
                  ·
                    refine ⟨144202483804352982858473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1538159827246431817157045 144202483804352982858473)
                    ·
                      rfl

theorem cell23_842500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_842500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842500 prefixEnd_842500 := by exact prefixLift 842500
  have htrace : WordTrace (prefixWord ++ tailWord_842500) baseStart_842500 baseEnd_842500 := by
    simpa [prefixWord, tailWord_842500, baseEnd_842500] using wordTrace_append hprefix tailTrace_842500
  have hstable : (prefixWord ++ tailWord_842500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842500).length < 2 ^ (prefixWord ++ tailWord_842500).sum := by decide
  have hdescent : baseEnd_842500 < baseStart_842500 := by decide
  rcases family_descends (prefixWord ++ tailWord_842500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842533 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_842533 : Nat := 118140960795 + 842533 * 2 ^ 59
def prefixEnd_842533 : Nat := 4983230072969 + 3 ^ 40 * 842533 * 2
def baseEnd_842533 : Nat := 432624396274657319462767

theorem tailTrace_842533 : CollatzResearch.WordTrace tailWord_842533 prefixEnd_842533 432624396274657319462767 := by
  unfold tailWord_842533
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729703056654309025588253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20486468704436206017058835 30729703056654309025588253)
  ·
    refine ⟨11523638646245365884595595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30729703056654309025588253 11523638646245365884595595)
    ·
      refine ⟨17285457969368048826893393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523638646245365884595595 17285457969368048826893393)
      ·
        refine ⟨12964093477026036620170045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17285457969368048826893393 12964093477026036620170045)
        ·
          refine ⟨4861535053884763732563767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12964093477026036620170045 4861535053884763732563767)
          ·
            refine ⟨7292302580827145598845651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861535053884763732563767 7292302580827145598845651)
            ·
              refine ⟨10938453871240718398268477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292302580827145598845651 10938453871240718398268477)
              ·
                refine ⟨4101920201715269399350679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938453871240718398268477 4101920201715269399350679)
                ·
                  refine ⟨6152880302572904099026019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101920201715269399350679 6152880302572904099026019)
                  ·
                    refine ⟨9229320453859356148539029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152880302572904099026019 9229320453859356148539029)
                    ·
                      refine ⟨432624396274657319462767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9229320453859356148539029 432624396274657319462767)
                      ·
                        rfl

theorem cell23_842533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_842533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842533 prefixEnd_842533 := by exact prefixLift 842533
  have htrace : WordTrace (prefixWord ++ tailWord_842533) baseStart_842533 baseEnd_842533 := by
    simpa [prefixWord, tailWord_842533, baseEnd_842533] using wordTrace_append hprefix tailTrace_842533
  have hstable : (prefixWord ++ tailWord_842533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842533).length < 2 ^ (prefixWord ++ tailWord_842533).sum := by decide
  have hdescent : baseEnd_842533 < baseStart_842533 := by decide
  rcases family_descends (prefixWord ++ tailWord_842533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842540 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_842540 : Nat := 118140960795 + 842540 * 2 ^ 59
def prefixEnd_842540 : Nat := 4983230072969 + 3 ^ 40 * 842540 * 2
def baseEnd_842540 : Nat := 432627990639238792075235

theorem tailTrace_842540 : CollatzResearch.WordTrace tailWord_842540 prefixEnd_842540 432627990639238792075235 := by
  unfold tailWord_842540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364979183814474610546537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20486638911752632814062049 15364979183814474610546537)
  ·
    refine ⟨11523734387860855957909903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15364979183814474610546537 11523734387860855957909903)
    ·
      refine ⟨17285601581791283936864855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523734387860855957909903 17285601581791283936864855)
      ·
        refine ⟨25928402372686925905297283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285601581791283936864855 25928402372686925905297283)
        ·
          refine ⟨38892603559030388857945925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25928402372686925905297283 38892603559030388857945925)
          ·
            refine ⟨7292363167318197910864861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38892603559030388857945925 7292363167318197910864861)
            ·
              refine ⟨2734636187744324216574323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292363167318197910864861 2734636187744324216574323)
              ·
                refine ⟨4101954281616486324861485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734636187744324216574323 4101954281616486324861485)
                ·
                  refine ⟨1538232855606182371823057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4101954281616486324861485 1538232855606182371823057)
                  ·
                    refine ⟨1153674641704636778867293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1538232855606182371823057 1153674641704636778867293)
                    ·
                      refine ⟨432627990639238792075235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1153674641704636778867293 432627990639238792075235)
                      ·
                        rfl

theorem cell23_842540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_842540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842540 prefixEnd_842540 := by exact prefixLift 842540
  have htrace : WordTrace (prefixWord ++ tailWord_842540) baseStart_842540 baseEnd_842540 := by
    simpa [prefixWord, tailWord_842540, baseEnd_842540] using wordTrace_append hprefix tailTrace_842540
  have hstable : (prefixWord ++ tailWord_842540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842540).length < 2 ^ (prefixWord ++ tailWord_842540).sum := by decide
  have hdescent : baseEnd_842540 < baseStart_842540 := by decide
  rcases family_descends (prefixWord ++ tailWord_842540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842554 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_842554 : Nat := 118140960795 + 842554 * 2 ^ 59
def prefixEnd_842554 : Nat := 4983230072969 + 3 ^ 40 * 842554 * 2
def baseEnd_842554 : Nat := 432635179368401737300171

theorem tailTrace_842554 : CollatzResearch.WordTrace tailWord_842554 prefixEnd_842554 432635179368401737300171 := by
  unfold tailWord_842554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682617247394557403025679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20486979326385486408068477 7682617247394557403025679)
  ·
    refine ⟨11523925871091836104538519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682617247394557403025679 11523925871091836104538519)
    ·
      refine ⟨17285888806637754156807779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523925871091836104538519 17285888806637754156807779)
      ·
        refine ⟨25928833209956631235211669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285888806637754156807779 25928833209956631235211669)
        ·
          refine ⟨1215414056716717089150547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25928833209956631235211669 1215414056716717089150547)
          ·
            refine ⟨1823121085075075633725821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215414056716717089150547 1823121085075075633725821)
            ·
              refine ⟨683670406903153362647183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1823121085075075633725821 683670406903153362647183)
              ·
                refine ⟨1025505610354730043970775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683670406903153362647183 1025505610354730043970775)
                ·
                  refine ⟨1538258415532095065956163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025505610354730043970775 1538258415532095065956163)
                  ·
                    refine ⟨2307387623298142598934245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1538258415532095065956163 2307387623298142598934245)
                    ·
                      refine ⟨432635179368401737300171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2307387623298142598934245 432635179368401737300171)
                      ·
                        rfl

theorem cell23_842554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_842554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842554 prefixEnd_842554 := by exact prefixLift 842554
  have htrace : WordTrace (prefixWord ++ tailWord_842554) baseStart_842554 baseEnd_842554 := by
    simpa [prefixWord, tailWord_842554, baseEnd_842554] using wordTrace_append hprefix tailTrace_842554
  have hstable : (prefixWord ++ tailWord_842554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842554).length < 2 ^ (prefixWord ++ tailWord_842554).sum := by decide
  have hdescent : baseEnd_842554 < baseStart_842554 := by decide
  rcases family_descends (prefixWord ++ tailWord_842554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842577 : List Nat := [1, 2, 2, 1, 7, 1, 1, 8]
def baseStart_842577 : Nat := 118140960795 + 842577 * 2 ^ 59
def prefixEnd_842577 : Nat := 4983230072969 + 3 ^ 40 * 842577 * 2
def baseEnd_842577 : Nat := 16023962571239079530095

theorem tailTrace_842577 : CollatzResearch.WordTrace tailWord_842577 prefixEnd_842577 16023962571239079530095 := by
  unfold tailWord_842577
  simp only [CollatzResearch.WordTrace]
  refine ⟨30731307868494904540189985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20487538578996603026793323 30731307868494904540189985)
  ·
    refine ⟨23048480901371178405142489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30731307868494904540189985 23048480901371178405142489)
    ·
      refine ⟨17286360676028383803856867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23048480901371178405142489 17286360676028383803856867)
      ·
        refine ⟨25929541014042575705785301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17286360676028383803856867 25929541014042575705785301)
        ·
          refine ⟨607723617516622868104343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25929541014042575705785301 607723617516622868104343)
          ·
            refine ⟨911585426274934302156515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607723617516622868104343 911585426274934302156515)
            ·
              refine ⟨1367378139412401453234773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911585426274934302156515 1367378139412401453234773)
              ·
                refine ⟨16023962571239079530095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1367378139412401453234773 16023962571239079530095)
                ·
                  rfl

theorem cell23_842577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 8].length) (baseStart_842577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842577 prefixEnd_842577 := by exact prefixLift 842577
  have htrace : WordTrace (prefixWord ++ tailWord_842577) baseStart_842577 baseEnd_842577 := by
    simpa [prefixWord, tailWord_842577, baseEnd_842577] using wordTrace_append hprefix tailTrace_842577
  have hstable : (prefixWord ++ tailWord_842577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842577).length < 2 ^ (prefixWord ++ tailWord_842577).sum := by decide
  have hdescent : baseEnd_842577 < baseStart_842577 := by decide
  rcases family_descends (prefixWord ++ tailWord_842577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842597 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_842597 : Nat := 118140960795 + 842597 * 2 ^ 59
def prefixEnd_842597 : Nat := 4983230072969 + 3 ^ 40 * 842597 * 2
def baseEnd_842597 : Nat := 432657259036545069062473

theorem tailTrace_842597 : CollatzResearch.WordTrace tailWord_842597 prefixEnd_842597 432657259036545069062473 := by
  unfold tailWord_842597
  simp only [CollatzResearch.WordTrace]
  refine ⟨30732037328422447955918045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20488024885614965303945363 30732037328422447955918045)
  ·
    refine ⟨11524513998158417983469267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30732037328422447955918045 11524513998158417983469267)
    ·
      refine ⟨17286770997237626975203901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524513998158417983469267 17286770997237626975203901)
      ·
        refine ⟨6482539123964110115701463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17286770997237626975203901 6482539123964110115701463)
        ·
          refine ⟨9723808685946165173552195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482539123964110115701463 9723808685946165173552195)
          ·
            refine ⟨14585713028919247760328293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723808685946165173552195 14585713028919247760328293)
            ·
              refine ⟨2734821192922358955061555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14585713028919247760328293 2734821192922358955061555)
              ·
                refine ⟨4102231789383538432592333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734821192922358955061555 4102231789383538432592333)
                ·
                  refine ⟨1538336921018826912222125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4102231789383538432592333 1538336921018826912222125)
                  ·
                    refine ⟨576876345382060092083297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538336921018826912222125 576876345382060092083297)
                    ·
                      refine ⟨432657259036545069062473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 576876345382060092083297 432657259036545069062473)
                      ·
                        rfl

theorem cell23_842597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_842597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842597 prefixEnd_842597 := by exact prefixLift 842597
  have htrace : WordTrace (prefixWord ++ tailWord_842597) baseStart_842597 baseEnd_842597 := by
    simpa [prefixWord, tailWord_842597, baseEnd_842597] using wordTrace_append hprefix tailTrace_842597
  have hstable : (prefixWord ++ tailWord_842597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842597).length < 2 ^ (prefixWord ++ tailWord_842597).sum := by decide
  have hdescent : baseEnd_842597 < baseStart_842597 := by decide
  rcases family_descends (prefixWord ++ tailWord_842597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842680 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 4, 5]
def baseStart_842680 : Nat := 118140960795 + 842680 * 2 ^ 59
def prefixEnd_842680 : Nat := 4983230072969 + 3 ^ 40 * 842680 * 2
def baseEnd_842680 : Nat := 144233292643622748108197

theorem tailTrace_842680 : CollatzResearch.WordTrace tailWord_842680 prefixEnd_842680 144233292643622748108197 := by
  unfold tailWord_842680
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367532293560876565594747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20490043058081168754126329 15367532293560876565594747)
  ·
    refine ⟨23051298440341314848392121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15367532293560876565594747 23051298440341314848392121)
    ·
      refine ⟨17288473830255986136294091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23051298440341314848392121 17288473830255986136294091)
      ·
        refine ⟨25932710745383979204441137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17288473830255986136294091 25932710745383979204441137)
        ·
          refine ⟨19449533059037984403330853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25932710745383979204441137 19449533059037984403330853)
          ·
            refine ⟨3646787448569622075624535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19449533059037984403330853 3646787448569622075624535)
            ·
              refine ⟨5470181172854433113436803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646787448569622075624535 5470181172854433113436803)
              ·
                refine ⟨8205271759281649670155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470181172854433113436803 8205271759281649670155205)
                ·
                  refine ⟨1538488454865309313154101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8205271759281649670155205 1538488454865309313154101)
                  ·
                    refine ⟨144233292643622748108197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1538488454865309313154101 144233292643622748108197)
                    ·
                      rfl

theorem cell23_842680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_842680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842680 prefixEnd_842680 := by exact prefixLift 842680
  have htrace : WordTrace (prefixWord ++ tailWord_842680) baseStart_842680 baseEnd_842680 := by
    simpa [prefixWord, tailWord_842680, baseEnd_842680] using wordTrace_append hprefix tailTrace_842680
  have hstable : (prefixWord ++ tailWord_842680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842680).length < 2 ^ (prefixWord ++ tailWord_842680).sum := by decide
  have hdescent : baseEnd_842680 < baseStart_842680 := by decide
  rcases family_descends (prefixWord ++ tailWord_842680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842791 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 6]
def baseStart_842791 : Nat := 118140960795 + 842791 * 2 ^ 59
def prefixEnd_842791 : Nat := 4983230072969 + 3 ^ 40 * 842791 * 2
def baseEnd_842791 : Nat := 48084097142613034448509

theorem tailTrace_842791 : CollatzResearch.WordTrace tailWord_842791 prefixEnd_842791 48084097142613034448509 := by
  unfold tailWord_842791
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739113089719619088480227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20492742059813079392320151 30739113089719619088480227)
  ·
    refine ⟨46108669634579428632720341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30739113089719619088480227 46108669634579428632720341)
    ·
      refine ⟨1080671944560455358579383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46108669634579428632720341 1080671944560455358579383)
      ·
        refine ⟨1621007916840683037869075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080671944560455358579383 1621007916840683037869075)
        ·
          refine ⟨2431511875261024556803613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621007916840683037869075 2431511875261024556803613)
          ·
            refine ⟨911816953222884208801355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431511875261024556803613 911816953222884208801355)
            ·
              refine ⟨1367725429834326313202033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911816953222884208801355 1367725429834326313202033)
              ·
                refine ⟨1025794072375744734901525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367725429834326313202033 1025794072375744734901525)
                ·
                  refine ⟨48084097142613034448509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1025794072375744734901525 48084097142613034448509)
                  ·
                    rfl

theorem cell23_842791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 6].length) (baseStart_842791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842791 prefixEnd_842791 := by exact prefixLift 842791
  have htrace : WordTrace (prefixWord ++ tailWord_842791) baseStart_842791 baseEnd_842791 := by
    simpa [prefixWord, tailWord_842791, baseEnd_842791] using wordTrace_append hprefix tailTrace_842791
  have hstable : (prefixWord ++ tailWord_842791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842791).length < 2 ^ (prefixWord ++ tailWord_842791).sum := by decide
  have hdescent : baseEnd_842791 < baseStart_842791 := by decide
  rcases family_descends (prefixWord ++ tailWord_842791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842801 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_842801 : Nat := 118140960795 + 842801 * 2 ^ 59
def prefixEnd_842801 : Nat := 4983230072969 + 3 ^ 40 * 842801 * 2
def baseEnd_842801 : Nat := 432762009090062270911535

theorem tailTrace_842801 : CollatzResearch.WordTrace tailWord_842801 prefixEnd_842801 432762009090062270911535 := by
  unfold tailWord_842801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739477819683390796344257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20492985213122260530896171 30739477819683390796344257)
  ·
    refine ⟨23054608364762543097258193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30739477819683390796344257 23054608364762543097258193)
    ·
      refine ⟨17290956273571907322943645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23054608364762543097258193 17290956273571907322943645)
      ·
        refine ⟨6484108602589465246103867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17290956273571907322943645 6484108602589465246103867)
        ·
          refine ⟨9726162903884197869155801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484108602589465246103867 9726162903884197869155801)
          ·
            refine ⟨7294622177913148401866851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9726162903884197869155801 7294622177913148401866851)
            ·
              refine ⟨10941933266869722602800277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294622177913148401866851 10941933266869722602800277)
              ·
                refine ⟨512903121884518247006263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10941933266869722602800277 512903121884518247006263)
                ·
                  refine ⟨769354682826777370509395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512903121884518247006263 769354682826777370509395)
                  ·
                    refine ⟨1154032024240166055764093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 769354682826777370509395 1154032024240166055764093)
                    ·
                      refine ⟨432762009090062270911535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154032024240166055764093 432762009090062270911535)
                      ·
                        rfl

theorem cell23_842801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_842801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842801 prefixEnd_842801 := by exact prefixLift 842801
  have htrace : WordTrace (prefixWord ++ tailWord_842801) baseStart_842801 baseEnd_842801 := by
    simpa [prefixWord, tailWord_842801, baseEnd_842801] using wordTrace_append hprefix tailTrace_842801
  have hstable : (prefixWord ++ tailWord_842801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842801).length < 2 ^ (prefixWord ++ tailWord_842801).sum := by decide
  have hdescent : baseEnd_842801 < baseStart_842801 := by decide
  rcases family_descends (prefixWord ++ tailWord_842801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842824 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_842824 : Nat := 118140960795 + 842824 * 2 ^ 59
def prefixEnd_842824 : Nat := 4983230072969 + 3 ^ 40 * 842824 * 2
def baseEnd_842824 : Nat := 432773819145115680923929

theorem tailTrace_842824 : CollatzResearch.WordTrace tailWord_842824 prefixEnd_842824 432773819145115680923929 := by
  unfold tailWord_842824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370158349300032862215763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20493544465733377149621017 15370158349300032862215763)
  ·
    refine ⟨23055237523950049293323645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15370158349300032862215763 23055237523950049293323645)
    ·
      refine ⟨8645714071481268484996367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23055237523950049293323645 8645714071481268484996367)
      ·
        refine ⟨12968571107221902727494551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645714071481268484996367 12968571107221902727494551)
        ·
          refine ⟨19452856660832854091241827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968571107221902727494551 19452856660832854091241827)
          ·
            refine ⟨29179284991249281136862741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19452856660832854091241827 29179284991249281136862741)
            ·
              refine ⟨1367778983964810053290441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29179284991249281136862741 1367778983964810053290441)
              ·
                refine ⟨1025834237973607539967831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367778983964810053290441 1025834237973607539967831)
                ·
                  refine ⟨1538751356960411309951747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025834237973607539967831 1538751356960411309951747)
                  ·
                    refine ⟨2308127035440616964927621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1538751356960411309951747 2308127035440616964927621)
                    ·
                      refine ⟨432773819145115680923929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2308127035440616964927621 432773819145115680923929)
                      ·
                        rfl

theorem cell23_842824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_842824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842824 prefixEnd_842824 := by exact prefixLift 842824
  have htrace : WordTrace (prefixWord ++ tailWord_842824) baseStart_842824 baseEnd_842824 := by
    simpa [prefixWord, tailWord_842824, baseEnd_842824] using wordTrace_append hprefix tailTrace_842824
  have hstable : (prefixWord ++ tailWord_842824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842824).length < 2 ^ (prefixWord ++ tailWord_842824).sum := by decide
  have hdescent : baseEnd_842824 < baseStart_842824 := by decide
  rcases family_descends (prefixWord ++ tailWord_842824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842834 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_842834 : Nat := 118140960795 + 842834 * 2 ^ 59
def prefixEnd_842834 : Nat := 4983230072969 + 3 ^ 40 * 842834 * 2
def baseEnd_842834 : Nat := 144259651317220213932961

theorem tailTrace_842834 : CollatzResearch.WordTrace tailWord_842834 prefixEnd_842834 144259651317220213932961 := by
  unfold tailWord_842834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685170357140959358073889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20493787619042558288197037 7685170357140959358073889)
  ·
    refine ⟨5763877767855719518555417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7685170357140959358073889 5763877767855719518555417)
    ·
      refine ⟨4322908325891789638916563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5763877767855719518555417 4322908325891789638916563)
      ·
        refine ⟨6484362488837684458374845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322908325891789638916563 6484362488837684458374845)
        ·
          refine ⟨2431635933314131671890567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6484362488837684458374845 2431635933314131671890567)
          ·
            refine ⟨3647453899971197507835851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431635933314131671890567 3647453899971197507835851)
            ·
              refine ⟨5471180849956796261753777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647453899971197507835851 5471180849956796261753777)
              ·
                refine ⟨4103385637467597196315333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471180849956796261753777 4103385637467597196315333)
                ·
                  refine ⟨769384807025174474309125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4103385637467597196315333 769384807025174474309125)
                  ·
                    refine ⟨144259651317220213932961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 769384807025174474309125 144259651317220213932961)
                    ·
                      rfl

theorem cell23_842834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_842834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842834 prefixEnd_842834 := by exact prefixLift 842834
  have htrace : WordTrace (prefixWord ++ tailWord_842834) baseStart_842834 baseEnd_842834 := by
    simpa [prefixWord, tailWord_842834, baseEnd_842834] using wordTrace_append hprefix tailTrace_842834
  have hstable : (prefixWord ++ tailWord_842834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842834).length < 2 ^ (prefixWord ++ tailWord_842834).sum := by decide
  have hdescent : baseEnd_842834 < baseStart_842834 := by decide
  rcases family_descends (prefixWord ++ tailWord_842834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842837 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_842837 : Nat := 118140960795 + 842837 * 2 ^ 59
def prefixEnd_842837 : Nat := 4983230072969 + 3 ^ 40 * 842837 * 2
def baseEnd_842837 : Nat := 432780494393624130061369

theorem tailTrace_842837 : CollatzResearch.WordTrace tailWord_842837 prefixEnd_842837 432780494393624130061369 := by
  unfold tailWord_842837
  simp only [CollatzResearch.WordTrace]
  refine ⟨30740790847552968944654765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20493860565035312629769843 30740790847552968944654765)
  ·
    refine ⟨11527796567832363354245537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30740790847552968944654765 11527796567832363354245537)
    ·
      refine ⟨8645847425874272515684153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11527796567832363354245537 8645847425874272515684153)
      ·
        refine ⟨6484385569405704386763115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8645847425874272515684153 6484385569405704386763115)
        ·
          refine ⟨9726578354108556580144673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484385569405704386763115 9726578354108556580144673)
          ·
            refine ⟨7294933765581417435108505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9726578354108556580144673 7294933765581417435108505)
            ·
              refine ⟨5471200324186063076331379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7294933765581417435108505 5471200324186063076331379)
              ·
                refine ⟨8206800486279094614497069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471200324186063076331379 8206800486279094614497069)
                ·
                  refine ⟨3077550182354660480436401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8206800486279094614497069 3077550182354660480436401)
                  ·
                    refine ⟨2308162636765995360327301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077550182354660480436401 2308162636765995360327301)
                    ·
                      refine ⟨432780494393624130061369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2308162636765995360327301 432780494393624130061369)
                      ·
                        rfl

theorem cell23_842837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_842837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842837 prefixEnd_842837 := by exact prefixLift 842837
  have htrace : WordTrace (prefixWord ++ tailWord_842837) baseStart_842837 baseEnd_842837 := by
    simpa [prefixWord, tailWord_842837, baseEnd_842837] using wordTrace_append hprefix tailTrace_842837
  have hstable : (prefixWord ++ tailWord_842837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842837).length < 2 ^ (prefixWord ++ tailWord_842837).sum := by decide
  have hdescent : baseEnd_842837 < baseStart_842837 := by decide
  rcases family_descends (prefixWord ++ tailWord_842837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842844 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_842844 : Nat := 118140960795 + 842844 * 2 ^ 59
def prefixEnd_842844 : Nat := 4983230072969 + 3 ^ 40 * 842844 * 2
def baseEnd_842844 : Nat := 432784088758205602673837

theorem tailTrace_842844 : CollatzResearch.WordTrace tailWord_842844 prefixEnd_842844 432784088758205602673837 := by
  unfold tailWord_842844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370523079263804570079793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20494030772351739426773057 15370523079263804570079793)
  ·
    refine ⟨11527892309447853427559845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15370523079263804570079793 11527892309447853427559845)
    ·
      refine ⟨2161479808021472517667471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11527892309447853427559845 2161479808021472517667471)
      ·
        refine ⟨3242219712032208776501207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161479808021472517667471 3242219712032208776501207)
        ·
          refine ⟨4863329568048313164751811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242219712032208776501207 4863329568048313164751811)
          ·
            refine ⟨7294994352072469747127717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863329568048313164751811 7294994352072469747127717)
            ·
              refine ⟨1367811441013588077586447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7294994352072469747127717 1367811441013588077586447)
              ·
                refine ⟨2051717161520382116379671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367811441013588077586447 2051717161520382116379671)
                ·
                  refine ⟨3077575742280573174569507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051717161520382116379671 3077575742280573174569507)
                  ·
                    refine ⟨4616363613420859761854261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077575742280573174569507 4616363613420859761854261)
                    ·
                      refine ⟨432784088758205602673837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4616363613420859761854261 432784088758205602673837)
                      ·
                        rfl

theorem cell23_842844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_842844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842844 prefixEnd_842844 := by exact prefixLift 842844
  have htrace : WordTrace (prefixWord ++ tailWord_842844) baseStart_842844 baseEnd_842844 := by
    simpa [prefixWord, tailWord_842844, baseEnd_842844] using wordTrace_append hprefix tailTrace_842844
  have hstable : (prefixWord ++ tailWord_842844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842844).length < 2 ^ (prefixWord ++ tailWord_842844).sum := by decide
  have hdescent : baseEnd_842844 < baseStart_842844 := by decide
  rcases family_descends (prefixWord ++ tailWord_842844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842858 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_842858 : Nat := 118140960795 + 842858 * 2 ^ 59
def prefixEnd_842858 : Nat := 4983230072969 + 3 ^ 40 * 842858 * 2
def baseEnd_842858 : Nat := 432791277487368547898773

theorem tailTrace_842858 : CollatzResearch.WordTrace tailWord_842858 prefixEnd_842858 432791277487368547898773 := by
  unfold tailWord_842858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685389195119222382792307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20494371186984593020779485 7685389195119222382792307)
  ·
    refine ⟨11528083792678833574188461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685389195119222382792307 11528083792678833574188461)
    ·
      refine ⟨4323031422254562590320673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11528083792678833574188461 4323031422254562590320673)
      ·
        refine ⟨3242273566690921942740505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323031422254562590320673 3242273566690921942740505)
        ·
          refine ⟨2431705175018191457055379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242273566690921942740505 2431705175018191457055379)
          ·
            refine ⟨3647557762527287185583069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431705175018191457055379 3647557762527287185583069)
            ·
              refine ⟨1367834160947732694593651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3647557762527287185583069 1367834160947732694593651)
              ·
                refine ⟨2051751241421599041890477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367834160947732694593651 2051751241421599041890477)
                ·
                  refine ⟨769406715533099640708929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2051751241421599041890477 769406715533099640708929)
                  ·
                    refine ⟨577055036649824730531697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 769406715533099640708929 577055036649824730531697)
                    ·
                      refine ⟨432791277487368547898773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577055036649824730531697 432791277487368547898773)
                      ·
                        rfl

theorem cell23_842858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_842858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842858 prefixEnd_842858 := by exact prefixLift 842858
  have htrace : WordTrace (prefixWord ++ tailWord_842858) baseStart_842858 baseEnd_842858 := by
    simpa [prefixWord, tailWord_842858, baseEnd_842858] using wordTrace_append hprefix tailTrace_842858
  have hstable : (prefixWord ++ tailWord_842858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842858).length < 2 ^ (prefixWord ++ tailWord_842858).sum := by decide
  have hdescent : baseEnd_842858 < baseStart_842858 := by decide
  rcases family_descends (prefixWord ++ tailWord_842858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842908 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_842908 : Nat := 118140960795 + 842908 * 2 ^ 59
def prefixEnd_842908 : Nat := 4983230072969 + 3 ^ 40 * 842908 * 2
def baseEnd_842908 : Nat := 432816951520093352273543

theorem tailTrace_842908 : CollatzResearch.WordTrace tailWord_842908 prefixEnd_842908 432816951520093352273543 := by
  unfold tailWord_842908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371690215147874035244689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20495586953530498713659585 15371690215147874035244689)
  ·
    refine ⟨11528767661360905526433517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15371690215147874035244689 11528767661360905526433517)
    ·
      refine ⟨4323287873010339572412569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11528767661360905526433517 4323287873010339572412569)
      ·
        refine ⟨3242465904757754679309427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323287873010339572412569 3242465904757754679309427)
        ·
          refine ⟨4863698857136632018964141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242465904757754679309427 4863698857136632018964141)
          ·
            refine ⟨1823887071426237007111553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863698857136632018964141 1823887071426237007111553)
            ·
              refine ⟨1367915303569677755333665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823887071426237007111553 1367915303569677755333665)
              ·
                refine ⟨1025936477677258316500249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367915303569677755333665 1025936477677258316500249)
                ·
                  refine ⟨769452358257943737375187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1025936477677258316500249 769452358257943737375187)
                  ·
                    refine ⟨1154178537386915606062781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 769452358257943737375187 1154178537386915606062781)
                    ·
                      refine ⟨432816951520093352273543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154178537386915606062781 432816951520093352273543)
                      ·
                        rfl

theorem cell23_842908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_842908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842908 prefixEnd_842908 := by exact prefixLift 842908
  have htrace : WordTrace (prefixWord ++ tailWord_842908) baseStart_842908 baseEnd_842908 := by
    simpa [prefixWord, tailWord_842908, baseEnd_842908] using wordTrace_append hprefix tailTrace_842908
  have hstable : (prefixWord ++ tailWord_842908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842908).length < 2 ^ (prefixWord ++ tailWord_842908).sum := by decide
  have hdescent : baseEnd_842908 < baseStart_842908 := by decide
  rcases family_descends (prefixWord ++ tailWord_842908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842927 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_842927 : Nat := 118140960795 + 842927 * 2 ^ 59
def prefixEnd_842927 : Nat := 4983230072969 + 3 ^ 40 * 842927 * 2
def baseEnd_842927 : Nat := 432826707652528777935955

theorem tailTrace_842927 : CollatzResearch.WordTrace tailWord_842927 prefixEnd_842927 432826707652528777935955 := by
  unfold tailWord_842927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744073417226914315431035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20496048944817942876954023 30744073417226914315431035)
  ·
    refine ⟨46116110125840371473146553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30744073417226914315431035 46116110125840371473146553)
    ·
      refine ⟨34587082594380278604859915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46116110125840371473146553 34587082594380278604859915)
      ·
        refine ⟨51880623891570417907289873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34587082594380278604859915 51880623891570417907289873)
        ·
          refine ⟨38910467918677813430467405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51880623891570417907289873 38910467918677813430467405)
          ·
            refine ⟨14591425469504180036425277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38910467918677813430467405 14591425469504180036425277)
            ·
              refine ⟨5471784551064067513659479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591425469504180036425277 5471784551064067513659479)
              ·
                refine ⟨8207676826596101270489219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471784551064067513659479 8207676826596101270489219)
                ·
                  refine ⟨12311515239894151905733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8207676826596101270489219 12311515239894151905733829)
                  ·
                    refine ⟨2308409107480153482325093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12311515239894151905733829 2308409107480153482325093)
                    ·
                      refine ⟨432826707652528777935955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2308409107480153482325093 432826707652528777935955)
                      ·
                        rfl

theorem cell23_842927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_842927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842927 prefixEnd_842927 := by exact prefixLift 842927
  have htrace : WordTrace (prefixWord ++ tailWord_842927) baseStart_842927 baseEnd_842927 := by
    simpa [prefixWord, tailWord_842927, baseEnd_842927] using wordTrace_append hprefix tailTrace_842927
  have hstable : (prefixWord ++ tailWord_842927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842927).length < 2 ^ (prefixWord ++ tailWord_842927).sum := by decide
  have hdescent : baseEnd_842927 < baseStart_842927 := by decide
  rcases family_descends (prefixWord ++ tailWord_842927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842937 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 9]
def baseStart_842937 : Nat := 118140960795 + 842937 * 2 ^ 59
def prefixEnd_842937 : Nat := 4983230072969 + 3 ^ 40 * 842937 * 2
def baseEnd_842937 : Nat := 48092426939897082090101

theorem tailTrace_842937 : CollatzResearch.WordTrace tailWord_842937 prefixEnd_842937 48092426939897082090101 := by
  unfold tailWord_842937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744438147190686023295065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20496292098127124015530043 30744438147190686023295065)
  ·
    refine ⟨23058328610393014517471299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30744438147190686023295065 23058328610393014517471299)
    ·
      refine ⟨34587492915589521776206949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23058328610393014517471299 34587492915589521776206949)
      ·
        refine ⟨6485154921673035333038803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34587492915589521776206949 6485154921673035333038803)
        ·
          refine ⟨9727732382509552999558205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485154921673035333038803 9727732382509552999558205)
          ·
            refine ⟨3647899643441082374834327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9727732382509552999558205 3647899643441082374834327)
            ·
              refine ⟨5471849465161623562251491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647899643441082374834327 5471849465161623562251491)
              ·
                refine ⟨8207774197742435343377237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471849465161623562251491 8207774197742435343377237)
                ·
                  refine ⟨48092426939897082090101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8207774197742435343377237 48092426939897082090101)
                  ·
                    rfl

theorem cell23_842937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_842937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842937 prefixEnd_842937 := by exact prefixLift 842937
  have htrace : WordTrace (prefixWord ++ tailWord_842937) baseStart_842937 baseEnd_842937 := by
    simpa [prefixWord, tailWord_842937, baseEnd_842937] using wordTrace_append hprefix tailTrace_842937
  have hstable : (prefixWord ++ tailWord_842937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842937).length < 2 ^ (prefixWord ++ tailWord_842937).sum := by decide
  have hdescent : baseEnd_842937 < baseStart_842937 := by decide
  rcases family_descends (prefixWord ++ tailWord_842937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842965 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_842965 : Nat := 118140960795 + 842965 * 2 ^ 59
def prefixEnd_842965 : Nat := 4983230072969 + 3 ^ 40 * 842965 * 2
def baseEnd_842965 : Nat := 432846219917399629260781

theorem tailTrace_842965 : CollatzResearch.WordTrace tailWord_842965 prefixEnd_842965 432846219917399629260781 := by
  unfold tailWord_842965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745459391089246805314349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20496972927392831203542899 30745459391089246805314349)
  ·
    refine ⟨11529547271658467551992881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30745459391089246805314349 11529547271658467551992881)
    ·
      refine ⟨8647160453743850663994661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11529547271658467551992881 8647160453743850663994661)
      ·
        refine ⟨1621342585076971999498999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8647160453743850663994661 1621342585076971999498999)
        ·
          refine ⟨2432013877615457999248499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621342585076971999498999 2432013877615457999248499)
          ·
            refine ⟨3648020816423186998872749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432013877615457999248499 3648020816423186998872749)
            ·
              refine ⟨1368007806158695124577281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3648020816423186998872749 1368007806158695124577281)
              ·
                refine ⟨1026005854619021343432961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368007806158695124577281 1026005854619021343432961)
                ·
                  refine ⟨769504390964266007574721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026005854619021343432961 769504390964266007574721)
                  ·
                    refine ⟨577128293223199505681041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 769504390964266007574721 577128293223199505681041)
                    ·
                      refine ⟨432846219917399629260781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577128293223199505681041 432846219917399629260781)
                      ·
                        rfl

theorem cell23_842965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_842965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_842965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_842965 prefixEnd_842965 := by exact prefixLift 842965
  have htrace : WordTrace (prefixWord ++ tailWord_842965) baseStart_842965 baseEnd_842965 := by
    simpa [prefixWord, tailWord_842965, baseEnd_842965] using wordTrace_append hprefix tailTrace_842965
  have hstable : (prefixWord ++ tailWord_842965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842965).length < 2 ^ (prefixWord ++ tailWord_842965).sum := by decide
  have hdescent : baseEnd_842965 < baseStart_842965 := by decide
  rcases family_descends (prefixWord ++ tailWord_842965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843058 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_843058 : Nat := 118140960795 + 843058 * 2 ^ 59
def prefixEnd_843058 : Nat := 4983230072969 + 3 ^ 40 * 843058 * 2
def baseEnd_843058 : Nat := 432893973618267765397853

theorem tailTrace_843058 : CollatzResearch.WordTrace tailWord_843058 prefixEnd_843058 432893973618267765397853 := by
  unfold tailWord_843058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687212844938080922112457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20499234253168215792299885 7687212844938080922112457)
  ·
    refine ⟨5765409633703560691584343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7687212844938080922112457 5765409633703560691584343)
    ·
      refine ⟨8648114450555341037376515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765409633703560691584343 8648114450555341037376515)
      ·
        refine ⟨12972171675833011556064773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648114450555341037376515 12972171675833011556064773)
        ·
          refine ⟨2432282189218689666762145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12972171675833011556064773 2432282189218689666762145)
          ·
            refine ⟨1824211641914017250071609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432282189218689666762145 1824211641914017250071609)
            ·
              refine ⟨1368158731435512937553707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824211641914017250071609 1368158731435512937553707)
              ·
                refine ⟨2052238097153269406330561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368158731435512937553707 2052238097153269406330561)
                ·
                  refine ⟨1539178572864952054747921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052238097153269406330561 1539178572864952054747921)
                  ·
                    refine ⟨1154383929648714041060941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539178572864952054747921 1154383929648714041060941)
                    ·
                      refine ⟨432893973618267765397853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154383929648714041060941 432893973618267765397853)
                      ·
                        rfl

theorem cell23_843058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_843058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843058 prefixEnd_843058 := by exact prefixLift 843058
  have htrace : WordTrace (prefixWord ++ tailWord_843058) baseStart_843058 baseEnd_843058 := by
    simpa [prefixWord, tailWord_843058, baseEnd_843058] using wordTrace_append hprefix tailTrace_843058
  have hstable : (prefixWord ++ tailWord_843058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843058).length < 2 ^ (prefixWord ++ tailWord_843058).sum := by decide
  have hdescent : baseEnd_843058 < baseStart_843058 := by decide
  rcases family_descends (prefixWord ++ tailWord_843058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843165 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_843165 : Nat := 118140960795 + 843165 * 2 ^ 59
def prefixEnd_843165 : Nat := 4983230072969 + 3 ^ 40 * 843165 * 2
def baseEnd_843165 : Nat := 432948916048298846759861

theorem tailTrace_843165 : CollatzResearch.WordTrace tailWord_843165 prefixEnd_843165 432948916048298846759861 := by
  unfold tailWord_843165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30752753990364680962594949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20501835993576453975063299 30752753990364680962594949)
  ·
    refine ⟨5766141373193377680486553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30752753990364680962594949 5766141373193377680486553)
    ·
      refine ⟨4324606029895033260364915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5766141373193377680486553 4324606029895033260364915)
      ·
        refine ⟨6486909044842549890547373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4324606029895033260364915 6486909044842549890547373)
        ·
          refine ⟨2432590891815956208955265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6486909044842549890547373 2432590891815956208955265)
          ·
            refine ⟨1824443168861967156716449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432590891815956208955265 1824443168861967156716449)
            ·
              refine ⟨1368332376646475367537337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824443168861967156716449 1368332376646475367537337)
              ·
                refine ⟨1026249282484856525653003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368332376646475367537337 1026249282484856525653003)
                ·
                  refine ⟨1539373923727284788479505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026249282484856525653003 1539373923727284788479505)
                  ·
                    refine ⟨1154530442795463591359629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539373923727284788479505 1154530442795463591359629)
                    ·
                      refine ⟨432948916048298846759861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154530442795463591359629 432948916048298846759861)
                      ·
                        rfl

theorem cell23_843165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_843165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843165 prefixEnd_843165 := by exact prefixLift 843165
  have htrace : WordTrace (prefixWord ++ tailWord_843165) baseStart_843165 baseEnd_843165 := by
    simpa [prefixWord, tailWord_843165, baseEnd_843165] using wordTrace_append hprefix tailTrace_843165
  have hstable : (prefixWord ++ tailWord_843165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843165).length < 2 ^ (prefixWord ++ tailWord_843165).sum := by decide
  have hdescent : baseEnd_843165 < baseStart_843165 := by decide
  rcases family_descends (prefixWord ++ tailWord_843165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843196 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_843196 : Nat := 118140960795 + 843196 * 2 ^ 59
def prefixEnd_843196 : Nat := 4983230072969 + 3 ^ 40 * 843196 * 2
def baseEnd_843196 : Nat := 432964833948588225472219

theorem tailTrace_843196 : CollatzResearch.WordTrace tailWord_843196 prefixEnd_843196 432964833948588225472219 := by
  unfold tailWord_843196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376942326626186628486721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20502589768834915504648961 15376942326626186628486721)
  ·
    refine ⟨11532706744969639971365041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15376942326626186628486721 11532706744969639971365041)
    ·
      refine ⟨8649530058727229978523781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11532706744969639971365041 8649530058727229978523781)
      ·
        refine ⟨1621786886011355620973209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8649530058727229978523781 1621786886011355620973209)
        ·
          refine ⟨1216340164508516715729907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621786886011355620973209 1216340164508516715729907)
          ·
            refine ⟨1824510246762775073594861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216340164508516715729907 1824510246762775073594861)
            ·
              refine ⟨684191342536040652598073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824510246762775073594861 684191342536040652598073)
              ·
                refine ⟨513143506902030489448555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684191342536040652598073 513143506902030489448555)
                ·
                  refine ⟨769715260353045734172833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513143506902030489448555 769715260353045734172833)
                  ·
                    refine ⟨577286445264784300629625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 769715260353045734172833 577286445264784300629625)
                    ·
                      refine ⟨432964833948588225472219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577286445264784300629625 432964833948588225472219)
                      ·
                        rfl

theorem cell23_843196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_843196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843196 prefixEnd_843196 := by exact prefixLift 843196
  have htrace : WordTrace (prefixWord ++ tailWord_843196) baseStart_843196 baseEnd_843196 := by
    simpa [prefixWord, tailWord_843196, baseEnd_843196] using wordTrace_append hprefix tailTrace_843196
  have hstable : (prefixWord ++ tailWord_843196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843196).length < 2 ^ (prefixWord ++ tailWord_843196).sum := by decide
  have hdescent : baseEnd_843196 < baseStart_843196 := by decide
  rcases family_descends (prefixWord ++ tailWord_843196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843212 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_843212 : Nat := 118140960795 + 843212 * 2 ^ 59
def prefixEnd_843212 : Nat := 4983230072969 + 3 ^ 40 * 843212 * 2
def baseEnd_843212 : Nat := 432973049639060162872145

theorem tailTrace_843212 : CollatzResearch.WordTrace tailWord_843212 prefixEnd_843212 432973049639060162872145 := by
  unfold tailWord_843212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15377234110597203994777945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20502978814129605326370593 15377234110597203994777945)
  ·
    refine ⟨11532925582947902996083459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15377234110597203994777945 11532925582947902996083459)
    ·
      refine ⟨17299388374421854494125189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11532925582947902996083459 17299388374421854494125189)
      ·
        refine ⟨3243635320204097717648473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17299388374421854494125189 3243635320204097717648473)
        ·
          refine ⟨2432726490153073288236355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243635320204097717648473 2432726490153073288236355)
          ·
            refine ⟨3649089735229609932354533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432726490153073288236355 3649089735229609932354533)
            ·
              refine ⟨684204325355551862316475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649089735229609932354533 684204325355551862316475)
              ·
                refine ⟨1026306488033327793474713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684204325355551862316475 1026306488033327793474713)
                ·
                  refine ⟨769729866024995845106035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026306488033327793474713 769729866024995845106035)
                  ·
                    refine ⟨1154594799037493767659053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 769729866024995845106035 1154594799037493767659053)
                    ·
                      refine ⟨432973049639060162872145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154594799037493767659053 432973049639060162872145)
                      ·
                        rfl

theorem cell23_843212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_843212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843212 prefixEnd_843212 := by exact prefixLift 843212
  have htrace : WordTrace (prefixWord ++ tailWord_843212) baseStart_843212 baseEnd_843212 := by
    simpa [prefixWord, tailWord_843212, baseEnd_843212] using wordTrace_append hprefix tailTrace_843212
  have hstable : (prefixWord ++ tailWord_843212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843212).length < 2 ^ (prefixWord ++ tailWord_843212).sum := by decide
  have hdescent : baseEnd_843212 < baseStart_843212 := by decide
  rcases family_descends (prefixWord ++ tailWord_843212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843221 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_843221 : Nat := 118140960795 + 843221 * 2 ^ 59
def prefixEnd_843221 : Nat := 4983230072969 + 3 ^ 40 * 843221 * 2
def baseEnd_843221 : Nat := 432977670964950627659603

theorem tailTrace_843221 : CollatzResearch.WordTrace tailWord_843221 prefixEnd_843221 432977670964950627659603 := by
  unfold tailWord_843221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30754796478161802526633517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20503197652107868351089011 30754796478161802526633517)
  ·
    refine ⟨11533048679310675947487569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30754796478161802526633517 11533048679310675947487569)
    ·
      refine ⟨8649786509483006960615677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11533048679310675947487569 8649786509483006960615677)
      ·
        refine ⟨3243669941056127610230879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8649786509483006960615677 3243669941056127610230879)
        ·
          refine ⟨4865504911584191415346319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243669941056127610230879 4865504911584191415346319)
          ·
            refine ⟨7298257367376287123019479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865504911584191415346319 7298257367376287123019479)
            ·
              refine ⟨10947386051064430684529219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298257367376287123019479 10947386051064430684529219)
              ·
                refine ⟨16421079076596646026793829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947386051064430684529219 16421079076596646026793829)
                ·
                  refine ⟨3078952326861871130023843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16421079076596646026793829 3078952326861871130023843)
                  ·
                    refine ⟨4618428490292806695035765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078952326861871130023843 4618428490292806695035765)
                    ·
                      refine ⟨432977670964950627659603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4618428490292806695035765 432977670964950627659603)
                      ·
                        rfl

theorem cell23_843221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_843221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843221 prefixEnd_843221 := by exact prefixLift 843221
  have htrace : WordTrace (prefixWord ++ tailWord_843221) baseStart_843221 baseEnd_843221 := by
    simpa [prefixWord, tailWord_843221, baseEnd_843221] using wordTrace_append hprefix tailTrace_843221
  have hstable : (prefixWord ++ tailWord_843221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843221).length < 2 ^ (prefixWord ++ tailWord_843221).sum := by decide
  have hdescent : baseEnd_843221 < baseStart_843221 := by decide
  rcases family_descends (prefixWord ++ tailWord_843221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843222 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_843222 : Nat := 118140960795 + 843222 * 2 ^ 59
def prefixEnd_843222 : Nat := 4983230072969 + 3 ^ 40 * 843222 * 2
def baseEnd_843222 : Nat := 432978184445605123747099

theorem tailTrace_843222 : CollatzResearch.WordTrace tailWord_843222 prefixEnd_843222 432978184445605123747099 := by
  unfold tailWord_843222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922177059447386231088745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20503221967438786464946613 1922177059447386231088745)
  ·
    refine ⟨1441632794585539673316559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1922177059447386231088745 1441632794585539673316559)
    ·
      refine ⟨2162449191878309509974839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441632794585539673316559 2162449191878309509974839)
      ·
        refine ⟨3243673787817464264962259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162449191878309509974839 3243673787817464264962259)
        ·
          refine ⟨4865510681726196397443389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243673787817464264962259 4865510681726196397443389)
          ·
            refine ⟨1824566505647323649041271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865510681726196397443389 1824566505647323649041271)
            ·
              refine ⟨2736849758470985473561907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824566505647323649041271 2736849758470985473561907)
              ·
                refine ⟨4105274637706478210342861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736849758470985473561907 4105274637706478210342861)
                ·
                  refine ⟨1539477989139929328878573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4105274637706478210342861 1539477989139929328878573)
                  ·
                    refine ⟨577304245927473498329465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539477989139929328878573 577304245927473498329465)
                    ·
                      refine ⟨432978184445605123747099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577304245927473498329465 432978184445605123747099)
                      ·
                        rfl

theorem cell23_843222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_843222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843222 prefixEnd_843222 := by exact prefixLift 843222
  have htrace : WordTrace (prefixWord ++ tailWord_843222) baseStart_843222 baseEnd_843222 := by
    simpa [prefixWord, tailWord_843222, baseEnd_843222] using wordTrace_append hprefix tailTrace_843222
  have hstable : (prefixWord ++ tailWord_843222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843222).length < 2 ^ (prefixWord ++ tailWord_843222).sum := by decide
  have hdescent : baseEnd_843222 < baseStart_843222 := by decide
  rcases family_descends (prefixWord ++ tailWord_843222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843235 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 4, 2]
def baseStart_843235 : Nat := 118140960795 + 843235 * 2 ^ 59
def prefixEnd_843235 : Nat := 4983230072969 + 3 ^ 40 * 843235 * 2
def baseEnd_843235 : Nat := 432984859694113572884539

theorem tailTrace_843235 : CollatzResearch.WordTrace tailWord_843235 prefixEnd_843235 432984859694113572884539 := by
  unfold tailWord_843235
  simp only [CollatzResearch.WordTrace]
  refine ⟨30755307100111082917643159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20503538066740721945095439 30755307100111082917643159)
  ·
    refine ⟨46132960650166624376464739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30755307100111082917643159 46132960650166624376464739)
    ·
      refine ⟨69199440975249936564697109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46132960650166624376464739 69199440975249936564697109)
      ·
        refine ⟨3243723795714840776470177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69199440975249936564697109 3243723795714840776470177)
        ·
          refine ⟨2432792846786130582352633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243723795714840776470177 2432792846786130582352633)
          ·
            refine ⟨1824594635089597936764475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432792846786130582352633 1824594635089597936764475)
            ·
              refine ⟨2736891952634396905146713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824594635089597936764475 2736891952634396905146713)
              ·
                refine ⟨2052668964475797678860035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736891952634396905146713 2052668964475797678860035)
                ·
                  refine ⟨3079003446713696518290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052668964475797678860035 3079003446713696518290053)
                  ·
                    refine ⟨577313146258818097179385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079003446713696518290053 577313146258818097179385)
                    ·
                      refine ⟨432984859694113572884539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577313146258818097179385 432984859694113572884539)
                      ·
                        rfl

theorem cell23_843235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_843235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843235 prefixEnd_843235 := by exact prefixLift 843235
  have htrace : WordTrace (prefixWord ++ tailWord_843235) baseStart_843235 baseEnd_843235 := by
    simpa [prefixWord, tailWord_843235, baseEnd_843235] using wordTrace_append hprefix tailTrace_843235
  have hstable : (prefixWord ++ tailWord_843235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843235).length < 2 ^ (prefixWord ++ tailWord_843235).sum := by decide
  have hdescent : baseEnd_843235 < baseStart_843235 := by decide
  rcases family_descends (prefixWord ++ tailWord_843235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843258 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_843258 : Nat := 118140960795 + 843258 * 2 ^ 59
def prefixEnd_843258 : Nat := 4983230072969 + 3 ^ 40 * 843258 * 2
def baseEnd_843258 : Nat := 48110741083240775877437

theorem tailTrace_843258 : CollatzResearch.WordTrace tailWord_843258 prefixEnd_843258 48110741083240775877437 := by
  unfold tailWord_843258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689036494756939461432607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20504097319351838563820285 7689036494756939461432607)
  ·
    refine ⟨11533554742135409192148911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7689036494756939461432607 11533554742135409192148911)
    ·
      refine ⟨17300332113203113788223367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11533554742135409192148911 17300332113203113788223367)
      ·
        refine ⟨25950498169804670682335051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17300332113203113788223367 25950498169804670682335051)
        ·
          refine ⟨38925747254707006023502577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25950498169804670682335051 38925747254707006023502577)
          ·
            refine ⟨29194310441030254517626933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38925747254707006023502577 29194310441030254517626933)
            ·
              refine ⟨2736966603846586361027525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29194310441030254517626933 2736966603846586361027525)
              ·
                refine ⟨513181238221234942692661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2736966603846586361027525 513181238221234942692661)
                ·
                  refine ⟨48110741083240775877437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513181238221234942692661 48110741083240775877437)
                  ·
                    rfl

theorem cell23_843258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_843258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843258 prefixEnd_843258 := by exact prefixLift 843258
  have htrace : WordTrace (prefixWord ++ tailWord_843258) baseStart_843258 baseEnd_843258 := by
    simpa [prefixWord, tailWord_843258, baseEnd_843258] using wordTrace_append hprefix tailTrace_843258
  have hstable : (prefixWord ++ tailWord_843258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843258).length < 2 ^ (prefixWord ++ tailWord_843258).sum := by decide
  have hdescent : baseEnd_843258 < baseStart_843258 := by decide
  rcases family_descends (prefixWord ++ tailWord_843258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843288 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_843288 : Nat := 118140960795 + 843288 * 2 ^ 59
def prefixEnd_843288 : Nat := 4983230072969 + 3 ^ 40 * 843288 * 2
def baseEnd_843288 : Nat := 144337358056267288507265

theorem tailTrace_843288 : CollatzResearch.WordTrace tailWord_843288 prefixEnd_843288 144337358056267288507265 := by
  unfold tailWord_843288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378620084459536484661259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20504826779279381979548345 15378620084459536484661259)
  ·
    refine ⟨23067930126689304726991889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378620084459536484661259 23067930126689304726991889)
    ·
      refine ⟨17300947595016978545243917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23067930126689304726991889 17300947595016978545243917)
      ·
        refine ⟨6487855348131366954466469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17300947595016978545243917 6487855348131366954466469)
        ·
          refine ⟨1216472877774631303962463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6487855348131366954466469 1216472877774631303962463)
          ·
            refine ⟨1824709316661946955943695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216472877774631303962463 1824709316661946955943695)
            ·
              refine ⟨2737063974992920433915543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824709316661946955943695 2737063974992920433915543)
              ·
                refine ⟨4105595962489380650873315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737063974992920433915543 4105595962489380650873315)
                ·
                  refine ⟨6158393943734070976309973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105595962489380650873315 6158393943734070976309973)
                  ·
                    refine ⟨144337358056267288507265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6158393943734070976309973 144337358056267288507265)
                    ·
                      rfl

theorem cell23_843288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_843288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843288 prefixEnd_843288 := by exact prefixLift 843288
  have htrace : WordTrace (prefixWord ++ tailWord_843288) baseStart_843288 baseEnd_843288 := by
    simpa [prefixWord, tailWord_843288, baseEnd_843288] using wordTrace_append hprefix tailTrace_843288
  have hstable : (prefixWord ++ tailWord_843288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843288).length < 2 ^ (prefixWord ++ tailWord_843288).sum := by decide
  have hdescent : baseEnd_843288 < baseStart_843288 := by decide
  rcases family_descends (prefixWord ++ tailWord_843288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843382 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_843382 : Nat := 118140960795 + 843382 * 2 ^ 59
def prefixEnd_843382 : Nat := 4983230072969 + 3 ^ 40 * 843382 * 2
def baseEnd_843382 : Nat := 48117815705591610860707

theorem tailTrace_843382 : CollatzResearch.WordTrace tailWord_843382 prefixEnd_843382 48117815705591610860707 := by
  unfold tailWord_843382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922541789411157938952775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20507112420385684682162933 1922541789411157938952775)
  ·
    refine ⟨2883812684116736908429163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922541789411157938952775 2883812684116736908429163)
    ·
      refine ⟨4325719026175105362643745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883812684116736908429163 4325719026175105362643745)
      ·
        refine ⟨3244289269631329021982809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325719026175105362643745 3244289269631329021982809)
        ·
          refine ⟨2433216952223496766487107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244289269631329021982809 2433216952223496766487107)
          ·
            refine ⟨3649825428335245149730661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433216952223496766487107 3649825428335245149730661)
            ·
              refine ⟨684342267812858465574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649825428335245149730661 684342267812858465574499)
              ·
                refine ⟨1026513401719287698361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684342267812858465574499 1026513401719287698361749)
                ·
                  refine ⟨48117815705591610860707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1026513401719287698361749 48117815705591610860707)
                  ·
                    rfl

theorem cell23_843382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_843382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843382 prefixEnd_843382 := by exact prefixLift 843382
  have htrace : WordTrace (prefixWord ++ tailWord_843382) baseStart_843382 baseEnd_843382 := by
    simpa [prefixWord, tailWord_843382, baseEnd_843382] using wordTrace_append hprefix tailTrace_843382
  have hstable : (prefixWord ++ tailWord_843382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843382).length < 2 ^ (prefixWord ++ tailWord_843382).sum := by decide
  have hdescent : baseEnd_843382 < baseStart_843382 := by decide
  rcases family_descends (prefixWord ++ tailWord_843382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843385 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 4, 3, 2]
def baseStart_843385 : Nat := 118140960795 + 843385 * 2 ^ 59
def prefixEnd_843385 : Nat := 4983230072969 + 3 ^ 40 * 843385 * 2
def baseEnd_843385 : Nat := 433061881792287986008849

theorem tailTrace_843385 : CollatzResearch.WordTrace tailWord_843385 prefixEnd_843385 433061881792287986008849 := by
  unfold tailWord_843385
  simp only [CollatzResearch.WordTrace]
  refine ⟨30760778049567658535603609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20507185366378439023735739 30760778049567658535603609)
  ·
    refine ⟨23070583537175743901702707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30760778049567658535603609 23070583537175743901702707)
    ·
      refine ⟨34605875305763615852554061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23070583537175743901702707 34605875305763615852554061)
      ·
        refine ⟨12977203239661355944707773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34605875305763615852554061 12977203239661355944707773)
        ·
          refine ⟨4866451214873008479265415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12977203239661355944707773 4866451214873008479265415)
          ·
            refine ⟨7299676822309512718898123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866451214873008479265415 7299676822309512718898123)
            ·
              refine ⟨10949515233464269078347185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7299676822309512718898123 10949515233464269078347185)
              ·
                refine ⟨8212136425098201808760389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10949515233464269078347185 8212136425098201808760389)
                ·
                  refine ⟨1539775579705912839142573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8212136425098201808760389 1539775579705912839142573)
                  ·
                    refine ⟨577415842389717314678465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539775579705912839142573 577415842389717314678465)
                    ·
                      refine ⟨433061881792287986008849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577415842389717314678465 433061881792287986008849)
                      ·
                        rfl

theorem cell23_843385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_843385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843385 prefixEnd_843385 := by exact prefixLift 843385
  have htrace : WordTrace (prefixWord ++ tailWord_843385) baseStart_843385 baseEnd_843385 := by
    simpa [prefixWord, tailWord_843385, baseEnd_843385] using wordTrace_append hprefix tailTrace_843385
  have hstable : (prefixWord ++ tailWord_843385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843385).length < 2 ^ (prefixWord ++ tailWord_843385).sum := by decide
  have hdescent : baseEnd_843385 < baseStart_843385 := by decide
  rcases family_descends (prefixWord ++ tailWord_843385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843402 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_843402 : Nat := 118140960795 + 843402 * 2 ^ 59
def prefixEnd_843402 : Nat := 4983230072969 + 3 ^ 40 * 843402 * 2
def baseEnd_843402 : Nat := 433070610963414419496271

theorem tailTrace_843402 : CollatzResearch.WordTrace tailWord_843402 prefixEnd_843402 433070610963414419496271 := by
  unfold tailWord_843402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690349522626517609743115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20507598727004046959314973 7690349522626517609743115)
  ·
    refine ⟨11535524283939776414614673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690349522626517609743115 11535524283939776414614673)
    ·
      refine ⟨8651643212954832310961005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11535524283939776414614673 8651643212954832310961005)
      ·
        refine ⟨3244366204858062116610377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8651643212954832310961005 3244366204858062116610377)
        ·
          refine ⟨2433274653643546587457783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244366204858062116610377 2433274653643546587457783)
          ·
            refine ⟨3649911980465319881186675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433274653643546587457783 3649911980465319881186675)
            ·
              refine ⟨5474867970697979821780013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649911980465319881186675 5474867970697979821780013)
              ·
                refine ⟨2053075489011742433167505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474867970697979821780013 2053075489011742433167505)
                ·
                  refine ⟨1539806616758806824875629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2053075489011742433167505 1539806616758806824875629)
                  ·
                    refine ⟨577427481284552559328361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1539806616758806824875629 577427481284552559328361)
                    ·
                      refine ⟨433070610963414419496271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577427481284552559328361 433070610963414419496271)
                      ·
                        rfl

theorem cell23_843402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_843402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843402 prefixEnd_843402 := by exact prefixLift 843402
  have htrace : WordTrace (prefixWord ++ tailWord_843402) baseStart_843402 baseEnd_843402 := by
    simpa [prefixWord, tailWord_843402, baseEnd_843402] using wordTrace_append hprefix tailTrace_843402
  have hstable : (prefixWord ++ tailWord_843402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843402).length < 2 ^ (prefixWord ++ tailWord_843402).sum := by decide
  have hdescent : baseEnd_843402 < baseStart_843402 := by decide
  rcases family_descends (prefixWord ++ tailWord_843402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843408 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_843408 : Nat := 118140960795 + 843408 * 2 ^ 59
def prefixEnd_843408 : Nat := 4983230072969 + 3 ^ 40 * 843408 * 2
def baseEnd_843408 : Nat := 144357897282447132007081

theorem tailTrace_843408 : CollatzResearch.WordTrace tailWord_843408 prefixEnd_843408 144357897282447132007081 := by
  unfold tailWord_843408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15380808464242166731845439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20507744618989555642460585 15380808464242166731845439)
  ·
    refine ⟨23071212696363250097768159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15380808464242166731845439 23071212696363250097768159)
    ·
      refine ⟨34606819044544875146652239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23071212696363250097768159 34606819044544875146652239)
      ·
        refine ⟨51910228566817312719978359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34606819044544875146652239 51910228566817312719978359)
        ·
          refine ⟨77865342850225969079967539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910228566817312719978359 77865342850225969079967539)
          ·
            refine ⟨116798014275338953619951309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77865342850225969079967539 116798014275338953619951309)
            ·
              refine ⟨43799255353252107607481741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116798014275338953619951309 43799255353252107607481741)
              ·
                refine ⟨16424720757469540352805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43799255353252107607481741 16424720757469540352805653)
                ·
                  refine ⟨769908785506384704037765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16424720757469540352805653 769908785506384704037765)
                  ·
                    refine ⟨144357897282447132007081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 769908785506384704037765 144357897282447132007081)
                    ·
                      rfl

theorem cell23_843408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_843408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843408 prefixEnd_843408 := by exact prefixLift 843408
  have htrace : WordTrace (prefixWord ++ tailWord_843408) baseStart_843408 baseEnd_843408 := by
    simpa [prefixWord, tailWord_843408, baseEnd_843408] using wordTrace_append hprefix tailTrace_843408
  have hstable : (prefixWord ++ tailWord_843408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843408).length < 2 ^ (prefixWord ++ tailWord_843408).sum := by decide
  have hdescent : baseEnd_843408 < baseStart_843408 := by decide
  rcases family_descends (prefixWord ++ tailWord_843408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843466 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_843466 : Nat := 118140960795 + 843466 * 2 ^ 59
def prefixEnd_843466 : Nat := 4983230072969 + 3 ^ 40 * 843466 * 2
def baseEnd_843466 : Nat := 433103473725302169095977

theorem tailTrace_843466 : CollatzResearch.WordTrace tailWord_843466 prefixEnd_843466 433103473725302169095977 := by
  unfold tailWord_843466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690933090568552342325563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20509154908182806246201501 7690933090568552342325563)
  ·
    refine ⟨11536399635852828513488345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690933090568552342325563 11536399635852828513488345)
    ·
      refine ⟨8652299726889621385116259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11536399635852828513488345 8652299726889621385116259)
      ·
        refine ⟨12978449590334432077674389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652299726889621385116259 12978449590334432077674389)
        ·
          refine ⟨608364824546926503640987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12978449590334432077674389 608364824546926503640987)
          ·
            refine ⟨912547236820389755461481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608364824546926503640987 912547236820389755461481)
            ·
              refine ⟨684410427615292316596111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912547236820389755461481 684410427615292316596111)
              ·
                refine ⟨1026615641422938474894167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684410427615292316596111 1026615641422938474894167)
                ·
                  refine ⟨1539923462134407712341251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026615641422938474894167 1539923462134407712341251)
                  ·
                    refine ⟨2309885193201611568511877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539923462134407712341251 2309885193201611568511877)
                    ·
                      refine ⟨433103473725302169095977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2309885193201611568511877 433103473725302169095977)
                      ·
                        rfl

theorem cell23_843466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_843466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843466 prefixEnd_843466 := by exact prefixLift 843466
  have htrace : WordTrace (prefixWord ++ tailWord_843466) baseStart_843466 baseEnd_843466 := by
    simpa [prefixWord, tailWord_843466, baseEnd_843466] using wordTrace_append hprefix tailTrace_843466
  have hstable : (prefixWord ++ tailWord_843466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843466).length < 2 ^ (prefixWord ++ tailWord_843466).sum := by decide
  have hdescent : baseEnd_843466 < baseStart_843466 := by decide
  rcases family_descends (prefixWord ++ tailWord_843466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843482 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_843482 : Nat := 118140960795 + 843482 * 2 ^ 59
def prefixEnd_843482 : Nat := 4983230072969 + 3 ^ 40 * 843482 * 2
def baseEnd_843482 : Nat := 433111689415774106495903

theorem tailTrace_843482 : CollatzResearch.WordTrace tailWord_843482 prefixEnd_843482 433111689415774106495903 := by
  unfold tailWord_843482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691078982554061025471175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20509543953477496067923133 7691078982554061025471175)
  ·
    refine ⟨11536618473831091538206763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7691078982554061025471175 11536618473831091538206763)
    ·
      refine ⟨17304927710746637307310145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536618473831091538206763 17304927710746637307310145)
      ·
        refine ⟨12978695783059977980482609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17304927710746637307310145 12978695783059977980482609)
        ·
          refine ⟨9734021837294983485361957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978695783059977980482609 9734021837294983485361957)
          ·
            refine ⟨1825129094492809403505367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9734021837294983485361957 1825129094492809403505367)
            ·
              refine ⟨2737693641739214105258051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825129094492809403505367 2737693641739214105258051)
              ·
                refine ⟨4106540462608821157887077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737693641739214105258051 4106540462608821157887077)
                ·
                  refine ⟨769976336739153967103827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4106540462608821157887077 769976336739153967103827)
                  ·
                    refine ⟨1154964505108730950655741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 769976336739153967103827 1154964505108730950655741)
                    ·
                      refine ⟨433111689415774106495903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1154964505108730950655741 433111689415774106495903)
                      ·
                        rfl

theorem cell23_843482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_843482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843482 prefixEnd_843482 := by exact prefixLift 843482
  have htrace : WordTrace (prefixWord ++ tailWord_843482) baseStart_843482 baseEnd_843482 := by
    simpa [prefixWord, tailWord_843482, baseEnd_843482] using wordTrace_append hprefix tailTrace_843482
  have hstable : (prefixWord ++ tailWord_843482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843482).length < 2 ^ (prefixWord ++ tailWord_843482).sum := by decide
  have hdescent : baseEnd_843482 < baseStart_843482 := by decide
  rcases family_descends (prefixWord ++ tailWord_843482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843488 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_843488 : Nat := 118140960795 + 843488 * 2 ^ 59
def prefixEnd_843488 : Nat := 4983230072969 + 3 ^ 40 * 843488 * 2
def baseEnd_843488 : Nat := 433114770299701083020875

theorem tailTrace_843488 : CollatzResearch.WordTrace tailWord_843488 prefixEnd_843488 433114770299701083020875 := by
  unfold tailWord_843488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382267384097253563301559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20509689845463004751068745 15382267384097253563301559)
  ·
    refine ⟨23073401076145880344952339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15382267384097253563301559 23073401076145880344952339)
    ·
      refine ⟨34610101614218820517428509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23073401076145880344952339 34610101614218820517428509)
      ·
        refine ⟨12978788105332057694035691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34610101614218820517428509 12978788105332057694035691)
        ·
          refine ⟨19468182157998086541053537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978788105332057694035691 19468182157998086541053537)
          ·
            refine ⟨14601136618498564905790153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19468182157998086541053537 14601136618498564905790153)
            ·
              refine ⟨10950852463873923679342615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14601136618498564905790153 10950852463873923679342615)
              ·
                refine ⟨16426278695810885519013923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950852463873923679342615 16426278695810885519013923)
                ·
                  refine ⟨24639418043716328278520885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16426278695810885519013923 24639418043716328278520885)
                  ·
                    refine ⟨2309945441598405776111333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24639418043716328278520885 2309945441598405776111333)
                    ·
                      refine ⟨433114770299701083020875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2309945441598405776111333 433114770299701083020875)
                      ·
                        rfl

theorem cell23_843488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_843488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843488 prefixEnd_843488 := by exact prefixLift 843488
  have htrace : WordTrace (prefixWord ++ tailWord_843488) baseStart_843488 baseEnd_843488 := by
    simpa [prefixWord, tailWord_843488, baseEnd_843488] using wordTrace_append hprefix tailTrace_843488
  have hstable : (prefixWord ++ tailWord_843488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843488).length < 2 ^ (prefixWord ++ tailWord_843488).sum := by decide
  have hdescent : baseEnd_843488 < baseStart_843488 := by decide
  rcases family_descends (prefixWord ++ tailWord_843488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843555 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3]
def baseStart_843555 : Nat := 118140960795 + 843555 * 2 ^ 59
def prefixEnd_843555 : Nat := 4983230072969 + 3 ^ 40 * 843555 * 2
def baseEnd_843555 : Nat := 433149173503552320883067

theorem tailTrace_843555 : CollatzResearch.WordTrace tailWord_843555 prefixEnd_843555 433149173503552320883067 := by
  unfold tailWord_843555
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766978458951777569292119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20511318972634518379528079 30766978458951777569292119)
  ·
    refine ⟨46150467688427666353938179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30766978458951777569292119 46150467688427666353938179)
    ·
      refine ⟨69225701532641499530907269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46150467688427666353938179 69225701532641499530907269)
      ·
        refine ⟨12979819037370281162045113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69225701532641499530907269 12979819037370281162045113)
        ·
          refine ⟨9734864278027710871533835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12979819037370281162045113 9734864278027710871533835)
          ·
            refine ⟨14602296417041566307300753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734864278027710871533835 14602296417041566307300753)
            ·
              refine ⟨10951722312781174730475565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14602296417041566307300753 10951722312781174730475565)
              ·
                refine ⟨4106895867292940523928337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10951722312781174730475565 4106895867292940523928337)
                ·
                  refine ⟨3080171900469705392946253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106895867292940523928337 3080171900469705392946253)
                  ·
                    refine ⟨1155064462676139522354845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080171900469705392946253 1155064462676139522354845)
                    ·
                      refine ⟨433149173503552320883067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1155064462676139522354845 433149173503552320883067)
                      ·
                        rfl

theorem cell23_843555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_843555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843555 prefixEnd_843555 := by exact prefixLift 843555
  have htrace : WordTrace (prefixWord ++ tailWord_843555) baseStart_843555 baseEnd_843555 := by
    simpa [prefixWord, tailWord_843555, baseEnd_843555] using wordTrace_append hprefix tailTrace_843555
  have hstable : (prefixWord ++ tailWord_843555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843555).length < 2 ^ (prefixWord ++ tailWord_843555).sum := by decide
  have hdescent : baseEnd_843555 < baseStart_843555 := by decide
  rcases family_descends (prefixWord ++ tailWord_843555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843556 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_843556 : Nat := 118140960795 + 843556 * 2 ^ 59
def prefixEnd_843556 : Nat := 4983230072969 + 3 ^ 40 * 843556 * 2
def baseEnd_843556 : Nat := 433149686984206816970563

theorem tailTrace_843556 : CollatzResearch.WordTrace tailWord_843556 prefixEnd_843556 433149686984206816970563 := by
  unfold tailWord_843556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383507465974077370039261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20511343287965436493385681 15383507465974077370039261)
  ·
    refine ⟨5768815299740279013764723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15383507465974077370039261 5768815299740279013764723)
    ·
      refine ⟨8653222949610418520647085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768815299740279013764723 8653222949610418520647085)
      ·
        refine ⟨3244958606103906945242657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8653222949610418520647085 3244958606103906945242657)
        ·
          refine ⟨2433718954577930208931993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244958606103906945242657 2433718954577930208931993)
          ·
            refine ⟨1825289215933447656698995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433718954577930208931993 1825289215933447656698995)
            ·
              refine ⟨2737933823900171485048493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825289215933447656698995 2737933823900171485048493)
              ·
                refine ⟨1026725183962564306893185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737933823900171485048493 1026725183962564306893185)
                ·
                  refine ⟨770043887971923230169889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026725183962564306893185 770043887971923230169889)
                  ·
                    refine ⟨577532915978942422627417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 770043887971923230169889 577532915978942422627417)
                    ·
                      refine ⟨433149686984206816970563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577532915978942422627417 433149686984206816970563)
                      ·
                        rfl

theorem cell23_843556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_843556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843556 prefixEnd_843556 := by exact prefixLift 843556
  have htrace : WordTrace (prefixWord ++ tailWord_843556) baseStart_843556 baseEnd_843556 := by
    simpa [prefixWord, tailWord_843556, baseEnd_843556] using wordTrace_append hprefix tailTrace_843556
  have hstable : (prefixWord ++ tailWord_843556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843556).length < 2 ^ (prefixWord ++ tailWord_843556).sum := by decide
  have hdescent : baseEnd_843556 < baseStart_843556 := by decide
  rcases family_descends (prefixWord ++ tailWord_843556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843590 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_843590 : Nat := 118140960795 + 843590 * 2 ^ 59
def prefixEnd_843590 : Nat := 4983230072969 + 3 ^ 40 * 843590 * 2
def baseEnd_843590 : Nat := 433167145326459683945407

theorem tailTrace_843590 : CollatzResearch.WordTrace tailWord_843590 prefixEnd_843590 433167145326459683945407 := by
  unfold tailWord_843590
  simp only [CollatzResearch.WordTrace]
  refine ⟨961507969182030579588007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20512170009216652364544149 961507969182030579588007)
  ·
    refine ⟨1442261953773045869382011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961507969182030579588007 1442261953773045869382011)
    ·
      refine ⟨2163392930659568804073017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442261953773045869382011 2163392930659568804073017)
      ·
        refine ⟨1622544697994676603054763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163392930659568804073017 1622544697994676603054763)
        ·
          refine ⟨2433817046992014904582145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622544697994676603054763 2433817046992014904582145)
          ·
            refine ⟨1825362785244011178436609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433817046992014904582145 1825362785244011178436609)
            ·
              refine ⟨1369022088933008383827457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825362785244011178436609 1369022088933008383827457)
              ·
                refine ⟨1026766566699756287870593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369022088933008383827457 1026766566699756287870593)
                ·
                  refine ⟨770074925024817215902945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026766566699756287870593 770074925024817215902945)
                  ·
                    refine ⟨577556193768612911927209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 770074925024817215902945 577556193768612911927209)
                    ·
                      refine ⟨433167145326459683945407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577556193768612911927209 433167145326459683945407)
                      ·
                        rfl

theorem cell23_843590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_843590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843590 prefixEnd_843590 := by exact prefixLift 843590
  have htrace : WordTrace (prefixWord ++ tailWord_843590) baseStart_843590 baseEnd_843590 := by
    simpa [prefixWord, tailWord_843590, baseEnd_843590] using wordTrace_append hprefix tailTrace_843590
  have hstable : (prefixWord ++ tailWord_843590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843590).length < 2 ^ (prefixWord ++ tailWord_843590).sum := by decide
  have hdescent : baseEnd_843590 < baseStart_843590 := by decide
  rcases family_descends (prefixWord ++ tailWord_843590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843596 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 5]
def baseStart_843596 : Nat := 118140960795 + 843596 * 2 ^ 59
def prefixEnd_843596 : Nat := 4983230072969 + 3 ^ 40 * 843596 * 2
def baseEnd_843596 : Nat := 48130025134487406718931

theorem tailTrace_843596 : CollatzResearch.WordTrace tailWord_843596 prefixEnd_843596 48130025134487406718931 := by
  unfold tailWord_843596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384236925901620785767321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20512315901202161047689761 15384236925901620785767321)
  ·
    refine ⟨11538177694426215589325491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15384236925901620785767321 11538177694426215589325491)
    ·
      refine ⟨17307266541639323383988237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11538177694426215589325491 17307266541639323383988237)
      ·
        refine ⟨6490224953114746268995589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17307266541639323383988237 6490224953114746268995589)
        ·
          refine ⟨1216917178709014925436673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6490224953114746268995589 1216917178709014925436673)
          ·
            refine ⟨912687884031761194077505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216917178709014925436673 912687884031761194077505)
            ·
              refine ⟨684515913023820895558129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912687884031761194077505 684515913023820895558129)
              ·
                refine ⟨513386934767865671668597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684515913023820895558129 513386934767865671668597)
                ·
                  refine ⟨48130025134487406718931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513386934767865671668597 48130025134487406718931)
                  ·
                    rfl

theorem cell23_843596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_843596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843596 prefixEnd_843596 := by exact prefixLift 843596
  have htrace : WordTrace (prefixWord ++ tailWord_843596) baseStart_843596 baseEnd_843596 := by
    simpa [prefixWord, tailWord_843596, baseEnd_843596] using wordTrace_append hprefix tailTrace_843596
  have hstable : (prefixWord ++ tailWord_843596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843596).length < 2 ^ (prefixWord ++ tailWord_843596).sum := by decide
  have hdescent : baseEnd_843596 < baseStart_843596 := by decide
  rcases family_descends (prefixWord ++ tailWord_843596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843626 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_843626 : Nat := 118140960795 + 843626 * 2 ^ 59
def prefixEnd_843626 : Nat := 4983230072969 + 3 ^ 40 * 843626 * 2
def baseEnd_843626 : Nat := 144395210210007181031747

theorem tailTrace_843626 : CollatzResearch.WordTrace tailWord_843626 prefixEnd_843626 144395210210007181031747 := by
  unfold tailWord_843626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692392010423639173781683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20513045361129704463417821 7692392010423639173781683)
  ·
    refine ⟨11538588015635458760672525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7692392010423639173781683 11538588015635458760672525)
    ·
      refine ⟨4326970505863297035252197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11538588015635458760672525 4326970505863297035252197)
      ·
        refine ⟨811306969849368194109787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4326970505863297035252197 811306969849368194109787)
        ·
          refine ⟨1216960454774052291164681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811306969849368194109787 1216960454774052291164681)
          ·
            refine ⟨912720341080539218373511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216960454774052291164681 912720341080539218373511)
            ·
              refine ⟨1369080511620808827560267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912720341080539218373511 1369080511620808827560267)
              ·
                refine ⟨2053620767431213241340401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369080511620808827560267 2053620767431213241340401)
                ·
                  refine ⟨1540215575573409931005301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2053620767431213241340401 1540215575573409931005301)
                  ·
                    refine ⟨144395210210007181031747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1540215575573409931005301 144395210210007181031747)
                    ·
                      rfl

theorem cell23_843626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_843626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843626 prefixEnd_843626 := by exact prefixLift 843626
  have htrace : WordTrace (prefixWord ++ tailWord_843626) baseStart_843626 baseEnd_843626 := by
    simpa [prefixWord, tailWord_843626, baseEnd_843626] using wordTrace_append hprefix tailTrace_843626
  have hstable : (prefixWord ++ tailWord_843626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843626).length < 2 ^ (prefixWord ++ tailWord_843626).sum := by decide
  have hdescent : baseEnd_843626 < baseStart_843626 := by decide
  rcases family_descends (prefixWord ++ tailWord_843626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843646 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_843646 : Nat := 118140960795 + 843646 * 2 ^ 59
def prefixEnd_843646 : Nat := 4983230072969 + 3 ^ 40 * 843646 * 2
def baseEnd_843646 : Nat := 433195900243111464845149

theorem tailTrace_843646 : CollatzResearch.WordTrace tailWord_843646 prefixEnd_843646 433195900243111464845149 := by
  unfold tailWord_843646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846287187702762513856849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20513531667748066740569861 3846287187702762513856849)
  ·
    refine ⟨2884715390777071885392637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3846287187702762513856849 2884715390777071885392637)
    ·
      refine ⟨1081768271541401957022239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2884715390777071885392637 1081768271541401957022239)
      ·
        refine ⟨1622652407312102935533359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081768271541401957022239 1622652407312102935533359)
        ·
          refine ⟨2433978610968154403300039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622652407312102935533359 2433978610968154403300039)
          ·
            refine ⟨3650967916452231604950059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433978610968154403300039 3650967916452231604950059)
            ·
              refine ⟨5476451874678347407425089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650967916452231604950059 5476451874678347407425089)
              ·
                refine ⟨4107338906008760555568817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476451874678347407425089 4107338906008760555568817)
                ·
                  refine ⟨3080504179506570416676613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107338906008760555568817 3080504179506570416676613)
                  ·
                    refine ⟨577594533657481953126865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080504179506570416676613 577594533657481953126865)
                    ·
                      refine ⟨433195900243111464845149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577594533657481953126865 433195900243111464845149)
                      ·
                        rfl

theorem cell23_843646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_843646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843646 prefixEnd_843646 := by exact prefixLift 843646
  have htrace : WordTrace (prefixWord ++ tailWord_843646) baseStart_843646 baseEnd_843646 := by
    simpa [prefixWord, tailWord_843646, baseEnd_843646] using wordTrace_append hprefix tailTrace_843646
  have hstable : (prefixWord ++ tailWord_843646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843646).length < 2 ^ (prefixWord ++ tailWord_843646).sum := by decide
  have hdescent : baseEnd_843646 < baseStart_843646 := by decide
  rcases family_descends (prefixWord ++ tailWord_843646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843652 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 6]
def baseStart_843652 : Nat := 118140960795 + 843652 * 2 ^ 59
def prefixEnd_843652 : Nat := 4983230072969 + 3 ^ 40 * 843652 * 2
def baseEnd_843652 : Nat := 48133220125226493485569

theorem tailTrace_843652 : CollatzResearch.WordTrace tailWord_843652 prefixEnd_843652 48133220125226493485569 := by
  unfold tailWord_843652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385258169800181567786605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20513677559733575423715473 15385258169800181567786605)
  ·
    refine ⟨5769471813675068087919977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15385258169800181567786605 5769471813675068087919977)
    ·
      refine ⟨4327103860256301065939983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5769471813675068087919977 4327103860256301065939983)
      ·
        refine ⟨6490655790384451598909975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327103860256301065939983 6490655790384451598909975)
        ·
          refine ⟨9735983685576677398364963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490655790384451598909975 9735983685576677398364963)
          ·
            refine ⟨14603975528365016097547445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735983685576677398364963 14603975528365016097547445)
            ·
              refine ⟨1369122705784220259145073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14603975528365016097547445 1369122705784220259145073)
              ·
                refine ⟨1026842029338165194358805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369122705784220259145073 1026842029338165194358805)
                ·
                  refine ⟨48133220125226493485569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1026842029338165194358805 48133220125226493485569)
                  ·
                    rfl

theorem cell23_843652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_843652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843652 prefixEnd_843652 := by exact prefixLift 843652
  have htrace : WordTrace (prefixWord ++ tailWord_843652) baseStart_843652 baseEnd_843652 := by
    simpa [prefixWord, tailWord_843652, baseEnd_843652] using wordTrace_append hprefix tailTrace_843652
  have hstable : (prefixWord ++ tailWord_843652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843652).length < 2 ^ (prefixWord ++ tailWord_843652).sum := by decide
  have hdescent : baseEnd_843652 < baseStart_843652 := by decide
  rcases family_descends (prefixWord ++ tailWord_843652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843665 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_843665 : Nat := 118140960795 + 843665 * 2 ^ 59
def prefixEnd_843665 : Nat := 4983230072969 + 3 ^ 40 * 843665 * 2
def baseEnd_843665 : Nat := 144401885458515630169187

theorem tailTrace_843665 : CollatzResearch.WordTrace tailWord_843665 prefixEnd_843665 144401885458515630169187 := by
  unfold tailWord_843665
  simp only [CollatzResearch.WordTrace]
  refine ⟨30770990488553266355796449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20513993659035510903864299 30770990488553266355796449)
  ·
    refine ⟨23078242866414949766847337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30770990488553266355796449 23078242866414949766847337)
    ·
      refine ⟨17308682149811212325135503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23078242866414949766847337 17308682149811212325135503)
      ·
        refine ⟨25963023224716818487703255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17308682149811212325135503 25963023224716818487703255)
        ·
          refine ⟨38944534837075227731554883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25963023224716818487703255 38944534837075227731554883)
          ·
            refine ⟨58416802255612841597332325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38944534837075227731554883 58416802255612841597332325)
            ·
              refine ⟨10953150422927407799499811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58416802255612841597332325 10953150422927407799499811)
              ·
                refine ⟨16429725634391111699249717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953150422927407799499811 16429725634391111699249717)
                ·
                  refine ⟨1540286778224166721804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16429725634391111699249717 1540286778224166721804661)
                  ·
                    refine ⟨144401885458515630169187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1540286778224166721804661 144401885458515630169187)
                    ·
                      rfl

theorem cell23_843665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_843665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843665 prefixEnd_843665 := by exact prefixLift 843665
  have htrace : WordTrace (prefixWord ++ tailWord_843665) baseStart_843665 baseEnd_843665 := by
    simpa [prefixWord, tailWord_843665, baseEnd_843665] using wordTrace_append hprefix tailTrace_843665
  have hstable : (prefixWord ++ tailWord_843665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843665).length < 2 ^ (prefixWord ++ tailWord_843665).sum := by decide
  have hdescent : baseEnd_843665 < baseStart_843665 := by decide
  rcases family_descends (prefixWord ++ tailWord_843665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843685 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_843685 : Nat := 118140960795 + 843685 * 2 ^ 59
def prefixEnd_843685 : Nat := 4983230072969 + 3 ^ 40 * 843685 * 2
def baseEnd_843685 : Nat := 433215925988636812257469

theorem tailTrace_843685 : CollatzResearch.WordTrace tailWord_843685 prefixEnd_843685 433215925988636812257469 := by
  unfold tailWord_843685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771719948480809771524509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20514479965653873181016339 30771719948480809771524509)
  ·
    refine ⟨11539394980680303664321691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30771719948480809771524509 11539394980680303664321691)
    ·
      refine ⟨17309092471020455496482537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11539394980680303664321691 17309092471020455496482537)
      ·
        refine ⟨12981819353265341622361903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17309092471020455496482537 12981819353265341622361903)
        ·
          refine ⟨19472729029898012433542855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981819353265341622361903 19472729029898012433542855)
          ·
            refine ⟨29209093544847018650314283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19472729029898012433542855 29209093544847018650314283)
            ·
              refine ⟨43813640317270527975471425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29209093544847018650314283 43813640317270527975471425)
              ·
                refine ⟨32860230237952895981603569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43813640317270527975471425 32860230237952895981603569)
                ·
                  refine ⟨24645172678464671986202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32860230237952895981603569 24645172678464671986202677)
                  ·
                    refine ⟨2310484938606062998706501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24645172678464671986202677 2310484938606062998706501)
                    ·
                      refine ⟨433215925988636812257469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2310484938606062998706501 433215925988636812257469)
                      ·
                        rfl

theorem cell23_843685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_843685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843685 prefixEnd_843685 := by exact prefixLift 843685
  have htrace : WordTrace (prefixWord ++ tailWord_843685) baseStart_843685 baseEnd_843685 := by
    simpa [prefixWord, tailWord_843685, baseEnd_843685] using wordTrace_append hprefix tailTrace_843685
  have hstable : (prefixWord ++ tailWord_843685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843685).length < 2 ^ (prefixWord ++ tailWord_843685).sum := by decide
  have hdescent : baseEnd_843685 < baseStart_843685 := by decide
  rcases family_descends (prefixWord ++ tailWord_843685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843695 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 6]
def baseStart_843695 : Nat := 118140960795 + 843695 * 2 ^ 59
def prefixEnd_843695 : Nat := 4983230072969 + 3 ^ 40 * 843695 * 2
def baseEnd_843695 : Nat := 144407020265060591044141

theorem tailTrace_843695 : CollatzResearch.WordTrace tailWord_843695 prefixEnd_843695 144407020265060591044141 := by
  unfold tailWord_843695
  simp only [CollatzResearch.WordTrace]
  refine ⟨30772084678444581479388539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20514723118963054319592359 30772084678444581479388539)
  ·
    refine ⟨46158127017666872219082809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30772084678444581479388539 46158127017666872219082809)
    ·
      refine ⟨34618595263250154164312107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46158127017666872219082809 34618595263250154164312107)
      ·
        refine ⟨51927892894875231246468161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34618595263250154164312107 51927892894875231246468161)
        ·
          refine ⟨38945919671156423434851121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51927892894875231246468161 38945919671156423434851121)
          ·
            refine ⟨29209439753367317576138341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38945919671156423434851121 29209439753367317576138341)
            ·
              refine ⟨5476769953756372045525939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29209439753367317576138341 5476769953756372045525939)
              ·
                refine ⟨8215154930634558068288909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476769953756372045525939 8215154930634558068288909)
                ·
                  refine ⟨3080683098987959275608341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8215154930634558068288909 3080683098987959275608341)
                  ·
                    refine ⟨144407020265060591044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3080683098987959275608341 144407020265060591044141)
                    ·
                      rfl

theorem cell23_843695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_843695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843695 prefixEnd_843695 := by exact prefixLift 843695
  have htrace : WordTrace (prefixWord ++ tailWord_843695) baseStart_843695 baseEnd_843695 := by
    simpa [prefixWord, tailWord_843695, baseEnd_843695] using wordTrace_append hprefix tailTrace_843695
  have hstable : (prefixWord ++ tailWord_843695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843695).length < 2 ^ (prefixWord ++ tailWord_843695).sum := by decide
  have hdescent : baseEnd_843695 < baseStart_843695 := by decide
  rcases family_descends (prefixWord ++ tailWord_843695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843712 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_843712 : Nat := 118140960795 + 843712 * 2 ^ 59
def prefixEnd_843712 : Nat := 4983230072969 + 3 ^ 40 * 843712 * 2
def baseEnd_843712 : Nat := 144409929988769402206615

theorem tailTrace_843712 : CollatzResearch.WordTrace tailWord_843712 prefixEnd_843712 144409929988769402206615 := by
  unfold tailWord_843712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386352359691496691378695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20515136479588662255171593 15386352359691496691378695)
  ·
    refine ⟨23079528539537245037068043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386352359691496691378695 23079528539537245037068043)
    ·
      refine ⟨34619292809305867555602065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079528539537245037068043 34619292809305867555602065)
      ·
        refine ⟨25964469606979400666701549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34619292809305867555602065 25964469606979400666701549)
        ·
          refine ⟨9736676102617275250013081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25964469606979400666701549 9736676102617275250013081)
          ·
            refine ⟨7302507076962956437509811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736676102617275250013081 7302507076962956437509811)
            ·
              refine ⟨10953760615444434656264717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302507076962956437509811 10953760615444434656264717)
              ·
                refine ⟨4107660230791662996099269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10953760615444434656264717 4107660230791662996099269)
                ·
                  refine ⟨770186293273436811768613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4107660230791662996099269 770186293273436811768613)
                  ·
                    refine ⟨144409929988769402206615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770186293273436811768613 144409929988769402206615)
                    ·
                      rfl

theorem cell23_843712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_843712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843712 prefixEnd_843712 := by exact prefixLift 843712
  have htrace : WordTrace (prefixWord ++ tailWord_843712) baseStart_843712 baseEnd_843712 := by
    simpa [prefixWord, tailWord_843712, baseEnd_843712] using wordTrace_append hprefix tailTrace_843712
  have hstable : (prefixWord ++ tailWord_843712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843712).length < 2 ^ (prefixWord ++ tailWord_843712).sum := by decide
  have hdescent : baseEnd_843712 < baseStart_843712 := by decide
  rcases family_descends (prefixWord ++ tailWord_843712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843715 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_843715 : Nat := 118140960795 + 843715 * 2 ^ 59
def prefixEnd_843715 : Nat := 4983230072969 + 3 ^ 40 * 843715 * 2
def baseEnd_843715 : Nat := 433231330408271694882331

theorem tailTrace_843715 : CollatzResearch.WordTrace tailWord_843715 prefixEnd_843715 433231330408271694882331 := by
  unfold tailWord_843715
  simp only [CollatzResearch.WordTrace]
  refine ⟨30772814138372124895116599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20515209425581416596744399 30772814138372124895116599)
  ·
    refine ⟨46159221207558187342674899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30772814138372124895116599 46159221207558187342674899)
    ·
      refine ⟨69238831811337281014012349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46159221207558187342674899 69238831811337281014012349)
      ·
        refine ⟨25964561929251480380254631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69238831811337281014012349 25964561929251480380254631)
        ·
          refine ⟨38946842893877220570381947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25964561929251480380254631 38946842893877220570381947)
          ·
            refine ⟨58420264340815830855572921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38946842893877220570381947 58420264340815830855572921)
            ·
              refine ⟨43815198255611873141679691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58420264340815830855572921 43815198255611873141679691)
              ·
                refine ⟨65722797383417809712519537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43815198255611873141679691 65722797383417809712519537)
                ·
                  refine ⟨49292098037563357284389653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65722797383417809712519537 49292098037563357284389653)
                  ·
                    refine ⟨2310567095510782372705765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49292098037563357284389653 2310567095510782372705765)
                    ·
                      refine ⟨433231330408271694882331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2310567095510782372705765 433231330408271694882331)
                      ·
                        rfl

theorem cell23_843715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_843715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843715 prefixEnd_843715 := by exact prefixLift 843715
  have htrace : WordTrace (prefixWord ++ tailWord_843715) baseStart_843715 baseEnd_843715 := by
    simpa [prefixWord, tailWord_843715, baseEnd_843715] using wordTrace_append hprefix tailTrace_843715
  have hstable : (prefixWord ++ tailWord_843715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843715).length < 2 ^ (prefixWord ++ tailWord_843715).sum := by decide
  have hdescent : baseEnd_843715 < baseStart_843715 := by decide
  rcases family_descends (prefixWord ++ tailWord_843715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843722 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_843722 : Nat := 118140960795 + 843722 * 2 ^ 59
def prefixEnd_843722 : Nat := 4983230072969 + 3 ^ 40 * 843722 * 2
def baseEnd_843722 : Nat := 433234924772853167494799

theorem tailTrace_843722 : CollatzResearch.WordTrace tailWord_843722 prefixEnd_843722 433234924772853167494799 := by
  unfold tailWord_843722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7693267362336691272655355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20515379632897843393747613 7693267362336691272655355)
  ·
    refine ⟨11539901043505036908983033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7693267362336691272655355 11539901043505036908983033)
    ·
      refine ⟨8654925782628777681737275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11539901043505036908983033 8654925782628777681737275)
      ·
        refine ⟨12982388673943166522605913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8654925782628777681737275 12982388673943166522605913)
        ·
          refine ⟨9736791505457374891954435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12982388673943166522605913 9736791505457374891954435)
          ·
            refine ⟨14605187258186062337931653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9736791505457374891954435 14605187258186062337931653)
            ·
              refine ⟨2738472610909886688362185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14605187258186062337931653 2738472610909886688362185)
              ·
                refine ⟨2053854458182415016271639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738472610909886688362185 2053854458182415016271639)
                ·
                  refine ⟨3080781687273622524407459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053854458182415016271639 3080781687273622524407459)
                  ·
                    refine ⟨4621172530910433786611189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3080781687273622524407459 4621172530910433786611189)
                    ·
                      refine ⟨433234924772853167494799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4621172530910433786611189 433234924772853167494799)
                      ·
                        rfl

theorem cell23_843722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_843722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843722 prefixEnd_843722 := by exact prefixLift 843722
  have htrace : WordTrace (prefixWord ++ tailWord_843722) baseStart_843722 baseEnd_843722 := by
    simpa [prefixWord, tailWord_843722, baseEnd_843722] using wordTrace_append hprefix tailTrace_843722
  have hstable : (prefixWord ++ tailWord_843722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843722).length < 2 ^ (prefixWord ++ tailWord_843722).sum := by decide
  have hdescent : baseEnd_843722 < baseStart_843722 := by decide
  rcases family_descends (prefixWord ++ tailWord_843722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843732 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_843732 : Nat := 118140960795 + 843732 * 2 ^ 59
def prefixEnd_843732 : Nat := 4983230072969 + 3 ^ 40 * 843732 * 2
def baseEnd_843732 : Nat := 433240059579398128369753

theorem tailTrace_843732 : CollatzResearch.WordTrace tailWord_843732 prefixEnd_843732 433240059579398128369753 := by
  unfold tailWord_843732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386717089655268399242725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20515622786207024532323633 15386717089655268399242725)
  ·
    refine ⟨2885009454310362824858011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15386717089655268399242725 2885009454310362824858011)
    ·
      refine ⟨4327514181465544237287017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885009454310362824858011 4327514181465544237287017)
      ·
        refine ⟨3245635636099158177965263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4327514181465544237287017 3245635636099158177965263)
        ·
          refine ⟨4868453454148737266947895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245635636099158177965263 4868453454148737266947895)
          ·
            refine ⟨7302680181223105900421843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868453454148737266947895 7302680181223105900421843)
            ·
              refine ⟨10954020271834658850632765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302680181223105900421843 10954020271834658850632765)
              ·
                refine ⟨4107757601937997068987287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10954020271834658850632765 4107757601937997068987287)
                ·
                  refine ⟨6161636402906995603480931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107757601937997068987287 6161636402906995603480931)
                  ·
                    refine ⟨9242454604360493405221397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6161636402906995603480931 9242454604360493405221397)
                    ·
                      refine ⟨433240059579398128369753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9242454604360493405221397 433240059579398128369753)
                      ·
                        rfl

theorem cell23_843732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_843732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843732 prefixEnd_843732 := by exact prefixLift 843732
  have htrace : WordTrace (prefixWord ++ tailWord_843732) baseStart_843732 baseEnd_843732 := by
    simpa [prefixWord, tailWord_843732, baseEnd_843732] using wordTrace_append hprefix tailTrace_843732
  have hstable : (prefixWord ++ tailWord_843732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843732).length < 2 ^ (prefixWord ++ tailWord_843732).sum := by decide
  have hdescent : baseEnd_843732 < baseStart_843732 := by decide
  rcases family_descends (prefixWord ++ tailWord_843732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843746 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_843746 : Nat := 118140960795 + 843746 * 2 ^ 59
def prefixEnd_843746 : Nat := 4983230072969 + 3 ^ 40 * 843746 * 2
def baseEnd_843746 : Nat := 144415749436187024531563

theorem tailTrace_843746 : CollatzResearch.WordTrace tailWord_843746 prefixEnd_843746 144415749436187024531563 := by
  unfold tailWord_843746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7693486200314954297373773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20515963200839878126330061 7693486200314954297373773)
  ·
    refine ⟨2885057325118107861515165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7693486200314954297373773 2885057325118107861515165)
    ·
      refine ⟨1081896496919290448068187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2885057325118107861515165 1081896496919290448068187)
      ·
        refine ⟨1622844745378935672102281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081896496919290448068187 1622844745378935672102281)
        ·
          refine ⟨1217133559034201754076711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622844745378935672102281 1217133559034201754076711)
          ·
            refine ⟨1825700338551302631115067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217133559034201754076711 1825700338551302631115067)
            ·
              refine ⟨2738550507826953946672601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825700338551302631115067 2738550507826953946672601)
              ·
                refine ⟨2053912880870215460004451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738550507826953946672601 2053912880870215460004451)
                ·
                  refine ⟨3080869321305323190006677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053912880870215460004451 3080869321305323190006677)
                  ·
                    refine ⟨144415749436187024531563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3080869321305323190006677 144415749436187024531563)
                    ·
                      rfl

theorem cell23_843746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_843746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843746 prefixEnd_843746 := by exact prefixLift 843746
  have htrace : WordTrace (prefixWord ++ tailWord_843746) baseStart_843746 baseEnd_843746 := by
    simpa [prefixWord, tailWord_843746, baseEnd_843746] using wordTrace_append hprefix tailTrace_843746
  have hstable : (prefixWord ++ tailWord_843746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843746).length < 2 ^ (prefixWord ++ tailWord_843746).sum := by decide
  have hdescent : baseEnd_843746 < baseStart_843746 := by decide
  rcases family_descends (prefixWord ++ tailWord_843746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843755 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 7]
def baseStart_843755 : Nat := 118140960795 + 843755 * 2 ^ 59
def prefixEnd_843755 : Nat := 4983230072969 + 3 ^ 40 * 843755 * 2
def baseEnd_843755 : Nat := 144417289878150512794049

theorem tailTrace_843755 : CollatzResearch.WordTrace tailWord_843755 prefixEnd_843755 144417289878150512794049 := by
  unfold tailWord_843755
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774273058227211726572719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20516182038818141151048479 30774273058227211726572719)
  ·
    refine ⟨46161409587340817589859079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30774273058227211726572719 46161409587340817589859079)
    ·
      refine ⟨69242114381011226384788619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46161409587340817589859079 69242114381011226384788619)
      ·
        refine ⟨103863171571516839577182929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69242114381011226384788619 103863171571516839577182929)
        ·
          refine ⟨77897378678637629682887197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103863171571516839577182929 77897378678637629682887197)
          ·
            refine ⟨29211517004489111131082699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77897378678637629682887197 29211517004489111131082699)
            ·
              refine ⟨43817275506733666696624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29211517004489111131082699 43817275506733666696624049)
              ·
                refine ⟨32862956630050250022468037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43817275506733666696624049 32862956630050250022468037)
                ·
                  refine ⟨6161804368134421879212757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32862956630050250022468037 6161804368134421879212757)
                  ·
                    refine ⟨144417289878150512794049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6161804368134421879212757 144417289878150512794049)
                    ·
                      rfl

theorem cell23_843755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_843755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843755 prefixEnd_843755 := by exact prefixLift 843755
  have htrace : WordTrace (prefixWord ++ tailWord_843755) baseStart_843755 baseEnd_843755 := by
    simpa [prefixWord, tailWord_843755, baseEnd_843755] using wordTrace_append hprefix tailTrace_843755
  have hstable : (prefixWord ++ tailWord_843755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843755).length < 2 ^ (prefixWord ++ tailWord_843755).sum := by decide
  have hdescent : baseEnd_843755 < baseStart_843755 := by decide
  rcases family_descends (prefixWord ++ tailWord_843755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843786 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_843786 : Nat := 118140960795 + 843786 * 2 ^ 59
def prefixEnd_843786 : Nat := 4983230072969 + 3 ^ 40 * 843786 * 2
def baseEnd_843786 : Nat := 433267787534740917094505

theorem tailTrace_843786 : CollatzResearch.WordTrace tailWord_843786 prefixEnd_843786 433267787534740917094505 := by
  unfold tailWord_843786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7693850930278726005237803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20516935814076602680634141 7693850930278726005237803)
  ·
    refine ⟨11540776395418089007856705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7693850930278726005237803 11540776395418089007856705)
    ·
      refine ⟨8655582296563566755892529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11540776395418089007856705 8655582296563566755892529)
      ·
        refine ⟨6491686722422675066919397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8655582296563566755892529 6491686722422675066919397)
        ·
          refine ⟨1217191260454251575047387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6491686722422675066919397 1217191260454251575047387)
          ·
            refine ⟨1825786890681377362571081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217191260454251575047387 1825786890681377362571081)
            ·
              refine ⟨1369340168011033021928311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825786890681377362571081 1369340168011033021928311)
              ·
                refine ⟨2054010252016549532892467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369340168011033021928311 2054010252016549532892467)
                ·
                  refine ⟨3081015378024824299338701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054010252016549532892467 3081015378024824299338701)
                  ·
                    refine ⟨1155380766759309112252013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081015378024824299338701 1155380766759309112252013)
                    ·
                      refine ⟨433267787534740917094505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1155380766759309112252013 433267787534740917094505)
                      ·
                        rfl

theorem cell23_843786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_843786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843786 prefixEnd_843786 := by exact prefixLift 843786
  have htrace : WordTrace (prefixWord ++ tailWord_843786) baseStart_843786 baseEnd_843786 := by
    simpa [prefixWord, tailWord_843786, baseEnd_843786] using wordTrace_append hprefix tailTrace_843786
  have hstable : (prefixWord ++ tailWord_843786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843786).length < 2 ^ (prefixWord ++ tailWord_843786).sum := by decide
  have hdescent : baseEnd_843786 < baseStart_843786 := by decide
  rcases family_descends (prefixWord ++ tailWord_843786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843813 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_843813 : Nat := 118140960795 + 843813 * 2 ^ 59
def prefixEnd_843813 : Nat := 4983230072969 + 3 ^ 40 * 843813 * 2
def baseEnd_843813 : Nat := 433281651512412311456881

theorem tailTrace_843813 : CollatzResearch.WordTrace tailWord_843813 prefixEnd_843813 433281651512412311456881 := by
  unfold tailWord_843813
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776388492017087632184093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20517592328011391754789395 30776388492017087632184093)
  ·
    refine ⟨11541145684506407862069035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30776388492017087632184093 11541145684506407862069035)
    ·
      refine ⟨17311718526759611793103553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11541145684506407862069035 17311718526759611793103553)
      ·
        refine ⟨12983788895069708844827665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17311718526759611793103553 12983788895069708844827665)
        ·
          refine ⟨9737841671302281633620749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983788895069708844827665 9737841671302281633620749)
          ·
            refine ⟨3651690626738355612607781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9737841671302281633620749 3651690626738355612607781)
            ·
              refine ⟨684691992513441677363959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3651690626738355612607781 684691992513441677363959)
              ·
                refine ⟨1027037988770162516045939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684691992513441677363959 1027037988770162516045939)
                ·
                  refine ⟨1540556983155243774068909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027037988770162516045939 1540556983155243774068909)
                  ·
                    refine ⟨577708868683216415275841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1540556983155243774068909 577708868683216415275841)
                    ·
                      refine ⟨433281651512412311456881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577708868683216415275841 433281651512412311456881)
                      ·
                        rfl

theorem cell23_843813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_843813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843813 prefixEnd_843813 := by exact prefixLift 843813
  have htrace : WordTrace (prefixWord ++ tailWord_843813) baseStart_843813 baseEnd_843813 := by
    simpa [prefixWord, tailWord_843813, baseEnd_843813] using wordTrace_append hprefix tailTrace_843813
  have hstable : (prefixWord ++ tailWord_843813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843813).length < 2 ^ (prefixWord ++ tailWord_843813).sum := by decide
  have hdescent : baseEnd_843813 < baseStart_843813 := by decide
  rcases family_descends (prefixWord ++ tailWord_843813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843846 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_843846 : Nat := 118140960795 + 843846 * 2 ^ 59
def prefixEnd_843846 : Nat := 4983230072969 + 3 ^ 40 * 843846 * 2
def baseEnd_843846 : Nat := 433298596374010682344229

theorem tailTrace_843846 : CollatzResearch.WordTrace tailWord_843846 prefixEnd_843846 433298596374010682344229 := by
  unfold tailWord_843846
  simp only [CollatzResearch.WordTrace]
  refine ⟨961799753153047945879231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20518394733931689512090261 961799753153047945879231)
  ·
    refine ⟨1442699629729571918818847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961799753153047945879231 1442699629729571918818847)
    ·
      refine ⟨2164049444594357878228271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442699629729571918818847 2164049444594357878228271)
      ·
        refine ⟨3246074166891536817342407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164049444594357878228271 3246074166891536817342407)
        ·
          refine ⟨4869111250337305226013611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246074166891536817342407 4869111250337305226013611)
          ·
            refine ⟨7303666875505957839020417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869111250337305226013611 7303666875505957839020417)
            ·
              refine ⟨5477750156629468379265313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7303666875505957839020417 5477750156629468379265313)
              ·
                refine ⟨4108312617472101284448985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5477750156629468379265313 4108312617472101284448985)
                ·
                  refine ⟨3081234463104075963336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108312617472101284448985 3081234463104075963336739)
                  ·
                    refine ⟨4621851694656113945005109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081234463104075963336739 4621851694656113945005109)
                    ·
                      refine ⟨433298596374010682344229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4621851694656113945005109 433298596374010682344229)
                      ·
                        rfl

theorem cell23_843846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_843846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843846 prefixEnd_843846 := by exact prefixLift 843846
  have htrace : WordTrace (prefixWord ++ tailWord_843846) baseStart_843846 baseEnd_843846 := by
    simpa [prefixWord, tailWord_843846, baseEnd_843846] using wordTrace_append hprefix tailTrace_843846
  have hstable : (prefixWord ++ tailWord_843846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843846).length < 2 ^ (prefixWord ++ tailWord_843846).sum := by decide
  have hdescent : baseEnd_843846 < baseStart_843846 := by decide
  rcases family_descends (prefixWord ++ tailWord_843846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843879 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 2, 5]
def baseStart_843879 : Nat := 118140960795 + 843879 * 2 ^ 59
def prefixEnd_843879 : Nat := 4983230072969 + 3 ^ 40 * 843879 * 2
def baseEnd_843879 : Nat := 144438513745203017743859

theorem tailTrace_843879 : CollatzResearch.WordTrace tailWord_843879 prefixEnd_843879 144438513745203017743859 := by
  unfold tailWord_843879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30778795709777980904086691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20519197139851987269391127 30778795709777980904086691)
  ·
    refine ⟨46168193564666971356130037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30778795709777980904086691 46168193564666971356130037)
    ·
      refine ⟨4328268146687528564637191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46168193564666971356130037 4328268146687528564637191)
      ·
        refine ⟨6492402220031292846955787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328268146687528564637191 6492402220031292846955787)
        ·
          refine ⟨9738603330046939270433681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492402220031292846955787 9738603330046939270433681)
          ·
            refine ⟨7303952497535204452825261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9738603330046939270433681 7303952497535204452825261)
            ·
              refine ⟨2738982186575701669809473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7303952497535204452825261 2738982186575701669809473)
              ·
                refine ⟨2054236639931776252357105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738982186575701669809473 2054236639931776252357105)
                ·
                  refine ⟨1540677479948832189267829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054236639931776252357105 1540677479948832189267829)
                  ·
                    refine ⟨144438513745203017743859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1540677479948832189267829 144438513745203017743859)
                    ·
                      rfl

theorem cell23_843879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_843879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843879 prefixEnd_843879 := by exact prefixLift 843879
  have htrace : WordTrace (prefixWord ++ tailWord_843879) baseStart_843879 baseEnd_843879 := by
    simpa [prefixWord, tailWord_843879, baseEnd_843879] using wordTrace_append hprefix tailTrace_843879
  have hstable : (prefixWord ++ tailWord_843879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843879).length < 2 ^ (prefixWord ++ tailWord_843879).sum := by decide
  have hdescent : baseEnd_843879 < baseStart_843879 := by decide
  rcases family_descends (prefixWord ++ tailWord_843879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843886 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_843886 : Nat := 118140960795 + 843886 * 2 ^ 59
def prefixEnd_843886 : Nat := 4983230072969 + 3 ^ 40 * 843886 * 2
def baseEnd_843886 : Nat := 433319135600190525844045

theorem tailTrace_843886 : CollatzResearch.WordTrace tailWord_843886 prefixEnd_843886 433319135600190525844045 := by
  unfold tailWord_843886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847381377594077637448939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20519367347168414066394341 3847381377594077637448939)
  ·
    refine ⟨5771072066391116456173409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847381377594077637448939 5771072066391116456173409)
    ·
      refine ⟨4328304049793337342130057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5771072066391116456173409 4328304049793337342130057)
      ·
        refine ⟨3246228037345003006597543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4328304049793337342130057 3246228037345003006597543)
        ·
          refine ⟨4869342056017504509896315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246228037345003006597543 4869342056017504509896315)
          ·
            refine ⟨7304013084026256764844473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869342056017504509896315 7304013084026256764844473)
            ·
              refine ⟨5478009813019692573633355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304013084026256764844473 5478009813019692573633355)
              ·
                refine ⟨8217014719529538860450033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478009813019692573633355 8217014719529538860450033)
                ·
                  refine ⟨6162761039647154145337525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217014719529538860450033 6162761039647154145337525)
                  ·
                    refine ⟨577758847466920701125393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6162761039647154145337525 577758847466920701125393)
                    ·
                      refine ⟨433319135600190525844045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577758847466920701125393 433319135600190525844045)
                      ·
                        rfl

theorem cell23_843886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_843886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843886 prefixEnd_843886 := by exact prefixLift 843886
  have htrace : WordTrace (prefixWord ++ tailWord_843886) baseStart_843886 baseEnd_843886 := by
    simpa [prefixWord, tailWord_843886, baseEnd_843886] using wordTrace_append hprefix tailTrace_843886
  have hstable : (prefixWord ++ tailWord_843886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843886).length < 2 ^ (prefixWord ++ tailWord_843886).sum := by decide
  have hdescent : baseEnd_843886 < baseStart_843886 := by decide
  rcases family_descends (prefixWord ++ tailWord_843886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843936 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_843936 : Nat := 118140960795 + 843936 * 2 ^ 59
def prefixEnd_843936 : Nat := 4983230072969 + 3 ^ 40 * 843936 * 2
def baseEnd_843936 : Nat := 433344809632915330218815

theorem tailTrace_843936 : CollatzResearch.WordTrace tailWord_843936 prefixEnd_843936 433344809632915330218815 := by
  unfold tailWord_843936
  simp only [CollatzResearch.WordTrace]
  refine ⟨15390437335285739819455831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20520583113714319759274441 15390437335285739819455831)
  ·
    refine ⟨23085656002928609729183747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15390437335285739819455831 23085656002928609729183747)
    ·
      refine ⟨34628484004392914593775621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23085656002928609729183747 34628484004392914593775621)
      ·
        refine ⟨6492840750823671486332929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34628484004392914593775621 6492840750823671486332929)
        ·
          refine ⟨4869630563117753614749697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6492840750823671486332929 4869630563117753614749697)
          ·
            refine ⟨3652222922338315211062273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4869630563117753614749697 3652222922338315211062273)
            ·
              refine ⟨2739167191753736408296705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652222922338315211062273 2739167191753736408296705)
              ·
                refine ⟨2054375393815302306222529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739167191753736408296705 2054375393815302306222529)
                ·
                  refine ⟨1540781545361476729666897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054375393815302306222529 1540781545361476729666897)
                  ·
                    refine ⟨1155586159021107547250173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540781545361476729666897 1155586159021107547250173)
                    ·
                      refine ⟨433344809632915330218815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1155586159021107547250173 433344809632915330218815)
                      ·
                        rfl

theorem cell23_843936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_843936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843936 prefixEnd_843936 := by exact prefixLift 843936
  have htrace : WordTrace (prefixWord ++ tailWord_843936) baseStart_843936 baseEnd_843936 := by
    simpa [prefixWord, tailWord_843936, baseEnd_843936] using wordTrace_append hprefix tailTrace_843936
  have hstable : (prefixWord ++ tailWord_843936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843936).length < 2 ^ (prefixWord ++ tailWord_843936).sum := by decide
  have hdescent : baseEnd_843936 < baseStart_843936 := by decide
  rcases family_descends (prefixWord ++ tailWord_843936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843952 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_843952 : Nat := 118140960795 + 843952 * 2 ^ 59
def prefixEnd_843952 : Nat := 4983230072969 + 3 ^ 40 * 843952 * 2
def baseEnd_843952 : Nat := 144451008441129089206247

theorem tailTrace_843952 : CollatzResearch.WordTrace tailWord_843952 prefixEnd_843952 144451008441129089206247 := by
  unfold tailWord_843952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15390729119256757185747055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20520972159009009580996073 15390729119256757185747055)
  ·
    refine ⟨23086093678885135778620583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15390729119256757185747055 23086093678885135778620583)
    ·
      refine ⟨34629140518327703667930875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23086093678885135778620583 34629140518327703667930875)
      ·
        refine ⟨51943710777491555501896313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34629140518327703667930875 51943710777491555501896313)
        ·
          refine ⟨38957783083118666626422235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51943710777491555501896313 38957783083118666626422235)
          ·
            refine ⟨58436674624677999939633353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38957783083118666626422235 58436674624677999939633353)
            ·
              refine ⟨43827505968508499954725015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58436674624677999939633353 43827505968508499954725015)
              ·
                refine ⟨65741258952762749932087523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43827505968508499954725015 65741258952762749932087523)
                ·
                  refine ⟨98611888429144124898131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65741258952762749932087523 98611888429144124898131285)
                  ·
                    refine ⟨144451008441129089206247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 98611888429144124898131285 144451008441129089206247)
                    ·
                      rfl

theorem cell23_843952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_843952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843952 prefixEnd_843952 := by exact prefixLift 843952
  have htrace : WordTrace (prefixWord ++ tailWord_843952) baseStart_843952 baseEnd_843952 := by
    simpa [prefixWord, tailWord_843952, baseEnd_843952] using wordTrace_append hprefix tailTrace_843952
  have hstable : (prefixWord ++ tailWord_843952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843952).length < 2 ^ (prefixWord ++ tailWord_843952).sum := by decide
  have hdescent : baseEnd_843952 < baseStart_843952 := by decide
  rcases family_descends (prefixWord ++ tailWord_843952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843970 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_843970 : Nat := 118140960795 + 843970 * 2 ^ 59
def prefixEnd_843970 : Nat := 4983230072969 + 3 ^ 40 * 843970 * 2
def baseEnd_843970 : Nat := 433362267975168197193659

theorem tailTrace_843970 : CollatzResearch.WordTrace tailWord_843970 prefixEnd_843970 433362267975168197193659 := by
  unfold tailWord_843970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695528688112075861412341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20521409834965535630432909 7695528688112075861412341)
  ·
    refine ⟨721455814510507112007407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7695528688112075861412341 721455814510507112007407)
    ·
      refine ⟨1082183721765760668011111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721455814510507112007407 1082183721765760668011111)
      ·
        refine ⟨1623275582648641002016667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082183721765760668011111 1623275582648641002016667)
        ·
          refine ⟨2434913373972961503025001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623275582648641002016667 2434913373972961503025001)
          ·
            refine ⟨1826185030479721127268751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434913373972961503025001 1826185030479721127268751)
            ·
              refine ⟨2739277545719581690903127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826185030479721127268751 2739277545719581690903127)
              ·
                refine ⟨4108916318579372536354691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739277545719581690903127 4108916318579372536354691)
                ·
                  refine ⟨6163374477869058804532037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108916318579372536354691 6163374477869058804532037)
                  ·
                    refine ⟨1155632714600448525849757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6163374477869058804532037 1155632714600448525849757)
                    ·
                      refine ⟨433362267975168197193659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1155632714600448525849757 433362267975168197193659)
                      ·
                        rfl

theorem cell23_843970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_843970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843970 prefixEnd_843970 := by exact prefixLift 843970
  have htrace : WordTrace (prefixWord ++ tailWord_843970) baseStart_843970 baseEnd_843970 := by
    simpa [prefixWord, tailWord_843970, baseEnd_843970] using wordTrace_append hprefix tailTrace_843970
  have hstable : (prefixWord ++ tailWord_843970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843970).length < 2 ^ (prefixWord ++ tailWord_843970).sum := by decide
  have hdescent : baseEnd_843970 < baseStart_843970 := by decide
  rcases family_descends (prefixWord ++ tailWord_843970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843990 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_843990 : Nat := 118140960795 + 843990 * 2 ^ 59
def prefixEnd_843990 : Nat := 4983230072969 + 3 ^ 40 * 843990 * 2
def baseEnd_843990 : Nat := 48152504176473124327063

theorem tailTrace_843990 : CollatzResearch.WordTrace tailWord_843990 prefixEnd_843990 48152504176473124327063 := by
  unfold tailWord_843990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923927763273490428836089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20521896141583897907584949 1923927763273490428836089)
  ·
    refine ⟨1442945822455117821627067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923927763273490428836089 1442945822455117821627067)
    ·
      refine ⟨2164418733682676732440601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442945822455117821627067 2164418733682676732440601)
      ·
        refine ⟨1623314050262007549330451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2164418733682676732440601 1623314050262007549330451)
        ·
          refine ⟨2434971075393011323995677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623314050262007549330451 2434971075393011323995677)
          ·
            refine ⟨913114153272379246498379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2434971075393011323995677 913114153272379246498379)
            ·
              refine ⟨1369671229908568869747569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913114153272379246498379 1369671229908568869747569)
              ·
                refine ⟨1027253422431426652310677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369671229908568869747569 1027253422431426652310677)
                ·
                  refine ⟨48152504176473124327063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1027253422431426652310677 48152504176473124327063)
                  ·
                    rfl

theorem cell23_843990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_843990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_843990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_843990 prefixEnd_843990 := by exact prefixLift 843990
  have htrace : WordTrace (prefixWord ++ tailWord_843990) baseStart_843990 baseEnd_843990 := by
    simpa [prefixWord, tailWord_843990, baseEnd_843990] using wordTrace_append hprefix tailTrace_843990
  have hstable : (prefixWord ++ tailWord_843990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843990).length < 2 ^ (prefixWord ++ tailWord_843990).sum := by decide
  have hdescent : baseEnd_843990 < baseStart_843990 := by decide
  rcases family_descends (prefixWord ++ tailWord_843990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844009 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_844009 : Nat := 118140960795 + 844009 * 2 ^ 59
def prefixEnd_844009 : Nat := 4983230072969 + 3 ^ 40 * 844009 * 2
def baseEnd_844009 : Nat := 433382293720693544605979

theorem tailTrace_844009 : CollatzResearch.WordTrace tailWord_844009 prefixEnd_844009 433382293720693544605979 := by
  unfold tailWord_844009
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783537199307013106319081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20522358132871342070879387 30783537199307013106319081)
  ·
    refine ⟨23087652899480259829739311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30783537199307013106319081 23087652899480259829739311)
    ·
      refine ⟨34631479349220389744608967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23087652899480259829739311 34631479349220389744608967)
      ·
        refine ⟨51947219023830584616913451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34631479349220389744608967 51947219023830584616913451)
        ·
          refine ⟨77920828535745876925370177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51947219023830584616913451 77920828535745876925370177)
          ·
            refine ⟨58440621401809407694027633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77920828535745876925370177 58440621401809407694027633)
            ·
              refine ⟨43830466051357055770520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58440621401809407694027633 43830466051357055770520725)
              ·
                refine ⟨2054553096157361989243159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43830466051357055770520725 2054553096157361989243159)
                ·
                  refine ⟨3081829644236042983864739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054553096157361989243159 3081829644236042983864739)
                  ·
                    refine ⟨4622744466354064475797109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081829644236042983864739 4622744466354064475797109)
                    ·
                      refine ⟨433382293720693544605979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4622744466354064475797109 433382293720693544605979)
                      ·
                        rfl

theorem cell23_844009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_844009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844009 prefixEnd_844009 := by exact prefixLift 844009
  have htrace : WordTrace (prefixWord ++ tailWord_844009) baseStart_844009 baseEnd_844009 := by
    simpa [prefixWord, tailWord_844009, baseEnd_844009] using wordTrace_append hprefix tailTrace_844009
  have hstable : (prefixWord ++ tailWord_844009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844009).length < 2 ^ (prefixWord ++ tailWord_844009).sum := by decide
  have hdescent : baseEnd_844009 < baseStart_844009 := by decide
  rcases family_descends (prefixWord ++ tailWord_844009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844016 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_844016 : Nat := 118140960795 + 844016 * 2 ^ 59
def prefixEnd_844016 : Nat := 4983230072969 + 3 ^ 40 * 844016 * 2
def baseEnd_844016 : Nat := 144461962695091672406149

theorem tailTrace_844016 : CollatzResearch.WordTrace tailWord_844016 prefixEnd_844016 144461962695091672406149 := by
  unfold tailWord_844016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391896255140826650911951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20522528340187768867882601 15391896255140826650911951)
  ·
    refine ⟨23087844382711239976367927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15391896255140826650911951 23087844382711239976367927)
    ·
      refine ⟨34631766574066859964551891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23087844382711239976367927 34631766574066859964551891)
      ·
        refine ⟨51947649861100289946827837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34631766574066859964551891 51947649861100289946827837)
        ·
          refine ⟨19480368697912608730060439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51947649861100289946827837 19480368697912608730060439)
          ·
            refine ⟨29220553046868913095090659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19480368697912608730060439 29220553046868913095090659)
            ·
              refine ⟨43830829570303369642635989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29220553046868913095090659 43830829570303369642635989)
              ·
                refine ⟨1027285068053985225999281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43830829570303369642635989 1027285068053985225999281)
                ·
                  refine ⟨770463801040488919499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027285068053985225999281 770463801040488919499461)
                  ·
                    refine ⟨144461962695091672406149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770463801040488919499461 144461962695091672406149)
                    ·
                      rfl

theorem cell23_844016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_844016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844016 prefixEnd_844016 := by exact prefixLift 844016
  have htrace : WordTrace (prefixWord ++ tailWord_844016) baseStart_844016 baseEnd_844016 := by
    simpa [prefixWord, tailWord_844016, baseEnd_844016] using wordTrace_append hprefix tailTrace_844016
  have hstable : (prefixWord ++ tailWord_844016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844016).length < 2 ^ (prefixWord ++ tailWord_844016).sum := by decide
  have hdescent : baseEnd_844016 < baseStart_844016 := by decide
  rcases family_descends (prefixWord ++ tailWord_844016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844019 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_844019 : Nat := 118140960795 + 844019 * 2 ^ 59
def prefixEnd_844019 : Nat := 4983230072969 + 3 ^ 40 * 844019 * 2
def baseEnd_844019 : Nat := 433387428527238505480933

theorem tailTrace_844019 : CollatzResearch.WordTrace tailWord_844019 prefixEnd_844019 433387428527238505480933 := by
  unfold tailWord_844019
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783901929270784814183111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20522601286180523209455407 30783901929270784814183111)
  ·
    refine ⟨46175852893906177221274667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30783901929270784814183111 46175852893906177221274667)
    ·
      refine ⟨69263779340859265831912001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46175852893906177221274667 69263779340859265831912001)
      ·
        refine ⟨51947834505644449373934001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69263779340859265831912001 51947834505644449373934001)
        ·
          refine ⟨38960875879233337030450501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51947834505644449373934001 38960875879233337030450501)
          ·
            refine ⟨7305164227356250693209469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38960875879233337030450501 7305164227356250693209469)
            ·
              refine ⟨2739436585258594009953551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7305164227356250693209469 2739436585258594009953551)
              ·
                refine ⟨4109154877887891014930327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739436585258594009953551 4109154877887891014930327)
                ·
                  refine ⟨6163732316831836522395491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109154877887891014930327 6163732316831836522395491)
                  ·
                    refine ⟨9245598475247754783593237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163732316831836522395491 9245598475247754783593237)
                    ·
                      refine ⟨433387428527238505480933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9245598475247754783593237 433387428527238505480933)
                      ·
                        rfl

theorem cell23_844019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_844019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844019 prefixEnd_844019 := by exact prefixLift 844019
  have htrace : WordTrace (prefixWord ++ tailWord_844019) baseStart_844019 baseEnd_844019 := by
    simpa [prefixWord, tailWord_844019, baseEnd_844019] using wordTrace_append hprefix tailTrace_844019
  have hstable : (prefixWord ++ tailWord_844019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844019).length < 2 ^ (prefixWord ++ tailWord_844019).sum := by decide
  have hdescent : baseEnd_844019 < baseStart_844019 := by decide
  rcases family_descends (prefixWord ++ tailWord_844019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844034 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_844034 : Nat := 118140960795 + 844034 * 2 ^ 59
def prefixEnd_844034 : Nat := 4983230072969 + 3 ^ 40 * 844034 * 2
def baseEnd_844034 : Nat := 433395130737055946793365

theorem tailTrace_844034 : CollatzResearch.WordTrace tailWord_844034 prefixEnd_844034 433395130737055946793365 := by
  unfold tailWord_844034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696112256054110593994789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20522966016144294917319437 7696112256054110593994789)
  ·
    refine ⟨1443021048010145736374023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7696112256054110593994789 1443021048010145736374023)
    ·
      refine ⟨2164531572015218604561035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443021048010145736374023 2164531572015218604561035)
      ·
        refine ⟨3246797358022827906841553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164531572015218604561035 3246797358022827906841553)
        ·
          refine ⟨2435098018517120930131165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246797358022827906841553 2435098018517120930131165)
          ·
            refine ⟨913161756943920348799187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2435098018517120930131165 913161756943920348799187)
            ·
              refine ⟨1369742635415880523198781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913161756943920348799187 1369742635415880523198781)
              ·
                refine ⟨513653488280955196199543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369742635415880523198781 513653488280955196199543)
                ·
                  refine ⟨770480232421432794299315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513653488280955196199543 770480232421432794299315)
                  ·
                    refine ⟨1155720348632149191448973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 770480232421432794299315 1155720348632149191448973)
                    ·
                      refine ⟨433395130737055946793365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1155720348632149191448973 433395130737055946793365)
                      ·
                        rfl

theorem cell23_844034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_844034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844034 prefixEnd_844034 := by exact prefixLift 844034
  have htrace : WordTrace (prefixWord ++ tailWord_844034) baseStart_844034 baseEnd_844034 := by
    simpa [prefixWord, tailWord_844034, baseEnd_844034] using wordTrace_append hprefix tailTrace_844034
  have hstable : (prefixWord ++ tailWord_844034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844034).length < 2 ^ (prefixWord ++ tailWord_844034).sum := by decide
  have hdescent : baseEnd_844034 < baseStart_844034 := by decide
  rcases family_descends (prefixWord ++ tailWord_844034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844083 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 3, 3, 2]
def baseStart_844083 : Nat := 118140960795 + 844083 * 2 ^ 59
def prefixEnd_844083 : Nat := 4983230072969 + 3 ^ 40 * 844083 * 2
def baseEnd_844083 : Nat := 433420291289126255080639

theorem tailTrace_844083 : CollatzResearch.WordTrace tailWord_844083 prefixEnd_844083 433420291289126255080639 := by
  unfold tailWord_844083
  simp only [CollatzResearch.WordTrace]
  refine ⟨30786236201038923744512903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20524157467359282496341935 30786236201038923744512903)
  ·
    refine ⟨46179354301558385616769355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30786236201038923744512903 46179354301558385616769355)
    ·
      refine ⟨69269031452337578425154033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46179354301558385616769355 69269031452337578425154033)
      ·
        refine ⟨51951773589253183818865525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69269031452337578425154033 51951773589253183818865525)
        ·
          refine ⟨4870478773992485983018643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51951773589253183818865525 4870478773992485983018643)
          ·
            refine ⟨7305718160988728974527965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870478773992485983018643 7305718160988728974527965)
            ·
              refine ⟨2739644310370773365447987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7305718160988728974527965 2739644310370773365447987)
              ·
                refine ⟨4109466465556160048171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739644310370773365447987 4109466465556160048171981)
                ·
                  refine ⟨1541049924583560018064493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4109466465556160048171981 1541049924583560018064493)
                  ·
                    refine ⟨577893721718835006774185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541049924583560018064493 577893721718835006774185)
                    ·
                      refine ⟨433420291289126255080639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577893721718835006774185 433420291289126255080639)
                      ·
                        rfl

theorem cell23_844083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3, 2].length) (baseStart_844083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844083 prefixEnd_844083 := by exact prefixLift 844083
  have htrace : WordTrace (prefixWord ++ tailWord_844083) baseStart_844083 baseEnd_844083 := by
    simpa [prefixWord, tailWord_844083, baseEnd_844083] using wordTrace_append hprefix tailTrace_844083
  have hstable : (prefixWord ++ tailWord_844083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844083).length < 2 ^ (prefixWord ++ tailWord_844083).sum := by decide
  have hdescent : baseEnd_844083 < baseStart_844083 := by decide
  rcases family_descends (prefixWord ++ tailWord_844083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844130 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_844130 : Nat := 118140960795 + 844130 * 2 ^ 59
def prefixEnd_844130 : Nat := 4983230072969 + 3 ^ 40 * 844130 * 2
def baseEnd_844130 : Nat := 433444424879887571192923

theorem tailTrace_844130 : CollatzResearch.WordTrace tailWord_844130 prefixEnd_844130 433444424879887571192923 := by
  unfold tailWord_844130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696987607967162692868461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20525300287912433847649229 7696987607967162692868461)
  ·
    refine ⟨2886370352987686009825673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7696987607967162692868461 2886370352987686009825673)
    ·
      refine ⟨2164777764740764507369255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2886370352987686009825673 2164777764740764507369255)
      ·
        refine ⟨3247166647111146761053883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164777764740764507369255 3247166647111146761053883)
        ·
          refine ⟨4870749970666720141580825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247166647111146761053883 4870749970666720141580825)
          ·
            refine ⟨3653062478000040106185619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870749970666720141580825 3653062478000040106185619)
            ·
              refine ⟨5479593717000060159278429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653062478000040106185619 5479593717000060159278429)
              ·
                refine ⟨2054847643875022559729411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5479593717000060159278429 2054847643875022559729411)
                ·
                  refine ⟨3082271465812533839594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054847643875022559729411 3082271465812533839594117)
                  ·
                    refine ⟨577925899839850094923897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082271465812533839594117 577925899839850094923897)
                    ·
                      refine ⟨433444424879887571192923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 577925899839850094923897 433444424879887571192923)
                      ·
                        rfl

theorem cell23_844130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_844130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844130 prefixEnd_844130 := by exact prefixLift 844130
  have htrace : WordTrace (prefixWord ++ tailWord_844130) baseStart_844130 baseEnd_844130 := by
    simpa [prefixWord, tailWord_844130, baseEnd_844130] using wordTrace_append hprefix tailTrace_844130
  have hstable : (prefixWord ++ tailWord_844130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844130).length < 2 ^ (prefixWord ++ tailWord_844130).sum := by decide
  have hdescent : baseEnd_844130 < baseStart_844130 := by decide
  rcases family_descends (prefixWord ++ tailWord_844130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844136 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 9]
def baseStart_844136 : Nat := 118140960795 + 844136 * 2 ^ 59
def prefixEnd_844136 : Nat := 4983230072969 + 3 ^ 40 * 844136 * 2
def baseEnd_844136 : Nat := 48160833973757171968655

theorem tailTrace_844136 : CollatzResearch.WordTrace tailWord_844136 prefixEnd_844136 48160833973757171968655 := by
  unfold tailWord_844136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394084634923456898096131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20525446179897942530794841 15394084634923456898096131)
  ·
    refine ⟨23091126952385185347144197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15394084634923456898096131 23091126952385185347144197)
    ·
      refine ⟨4329586303572222252589537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23091126952385185347144197 4329586303572222252589537)
      ·
        refine ⟨3247189727679166689442153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4329586303572222252589537 3247189727679166689442153)
        ·
          refine ⟨2435392295759375017081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247189727679166689442153 2435392295759375017081615)
          ·
            refine ⟨3653088443639062525622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435392295759375017081615 3653088443639062525622423)
            ·
              refine ⟨5479632665458593788433635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653088443639062525622423 5479632665458593788433635)
              ·
                refine ⟨8219448998187890682650453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479632665458593788433635 8219448998187890682650453)
                ·
                  refine ⟨48160833973757171968655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8219448998187890682650453 48160833973757171968655)
                  ·
                    rfl

theorem cell23_844136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_844136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844136 prefixEnd_844136 := by exact prefixLift 844136
  have htrace : WordTrace (prefixWord ++ tailWord_844136) baseStart_844136 baseEnd_844136 := by
    simpa [prefixWord, tailWord_844136, baseEnd_844136] using wordTrace_append hprefix tailTrace_844136
  have hstable : (prefixWord ++ tailWord_844136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844136).length < 2 ^ (prefixWord ++ tailWord_844136).sum := by decide
  have hdescent : baseEnd_844136 < baseStart_844136 := by decide
  rcases family_descends (prefixWord ++ tailWord_844136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844139 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_844139 : Nat := 118140960795 + 844139 * 2 ^ 59
def prefixEnd_844139 : Nat := 4983230072969 + 3 ^ 40 * 844139 * 2
def baseEnd_844139 : Nat := 433449046205778035980381

theorem tailTrace_844139 : CollatzResearch.WordTrace tailWord_844139 prefixEnd_844139 433449046205778035980381 := by
  unfold tailWord_844139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30788278688836045308551471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20525519125890696872367647 30788278688836045308551471)
  ·
    refine ⟨46182418033254067962827207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30788278688836045308551471 46182418033254067962827207)
    ·
      refine ⟨69273627049881101944240811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46182418033254067962827207 69273627049881101944240811)
      ·
        refine ⟨103910440574821652916361217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69273627049881101944240811 103910440574821652916361217)
        ·
          refine ⟨77932830431116239687270913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103910440574821652916361217 77932830431116239687270913)
          ·
            refine ⟨58449622823337179765453185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77932830431116239687270913 58449622823337179765453185)
            ·
              refine ⟨43837217117502884824089889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58449622823337179765453185 43837217117502884824089889)
              ·
                refine ⟨32877912838127163618067417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43837217117502884824089889 32877912838127163618067417)
                ·
                  refine ⟨24658434628595372713550563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32877912838127163618067417 24658434628595372713550563)
                  ·
                    refine ⟨36987651942893059070325845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24658434628595372713550563 36987651942893059070325845)
                    ·
                      refine ⟨433449046205778035980381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36987651942893059070325845 433449046205778035980381)
                      ·
                        rfl

theorem cell23_844139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_844139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844139 prefixEnd_844139 := by exact prefixLift 844139
  have htrace : WordTrace (prefixWord ++ tailWord_844139) baseStart_844139 baseEnd_844139 := by
    simpa [prefixWord, tailWord_844139, baseEnd_844139] using wordTrace_append hprefix tailTrace_844139
  have hstable : (prefixWord ++ tailWord_844139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844139).length < 2 ^ (prefixWord ++ tailWord_844139).sum := by decide
  have hdescent : baseEnd_844139 < baseStart_844139 := by decide
  rcases family_descends (prefixWord ++ tailWord_844139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844170 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_844170 : Nat := 118140960795 + 844170 * 2 ^ 59
def prefixEnd_844170 : Nat := 4983230072969 + 3 ^ 40 * 844170 * 2
def baseEnd_844170 : Nat := 48162773789563046076971

theorem tailTrace_844170 : CollatzResearch.WordTrace tailWord_844170 prefixEnd_844170 48162773789563046076971 := by
  unfold tailWord_844170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697352337930934400732491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20526272901149158401953309 7697352337930934400732491)
  ·
    refine ⟨11546028506896401601098737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697352337930934400732491 11546028506896401601098737)
    ·
      refine ⟨8659521380172301200824053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11546028506896401601098737 8659521380172301200824053)
      ·
        refine ⟨811830129391153237577255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8659521380172301200824053 811830129391153237577255)
        ·
          refine ⟨1217745194086729856365883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811830129391153237577255 1217745194086729856365883)
          ·
            refine ⟨1826617791130094784548825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217745194086729856365883 1826617791130094784548825)
            ·
              refine ⟨1369963343347571088411619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826617791130094784548825 1369963343347571088411619)
              ·
                refine ⟨2054945015021356632617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369963343347571088411619 2054945015021356632617429)
                ·
                  refine ⟨48162773789563046076971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2054945015021356632617429 48162773789563046076971)
                  ·
                    rfl

theorem cell23_844170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_844170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844170 prefixEnd_844170 := by exact prefixLift 844170
  have htrace : WordTrace (prefixWord ++ tailWord_844170) baseStart_844170 baseEnd_844170 := by
    simpa [prefixWord, tailWord_844170, baseEnd_844170] using wordTrace_append hprefix tailTrace_844170
  have hstable : (prefixWord ++ tailWord_844170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844170).length < 2 ^ (prefixWord ++ tailWord_844170).sum := by decide
  have hdescent : baseEnd_844170 < baseStart_844170 := by decide
  rcases family_descends (prefixWord ++ tailWord_844170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844220 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_844220 : Nat := 118140960795 + 844220 * 2 ^ 59
def prefixEnd_844220 : Nat := 4983230072969 + 3 ^ 40 * 844220 * 2
def baseEnd_844220 : Nat := 433490638138792219067509

theorem tailTrace_844220 : CollatzResearch.WordTrace tailWord_844220 prefixEnd_844220 433490638138792219067509 := by
  unfold tailWord_844220
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395616500771298071125057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20527488667695064094833409 15395616500771298071125057)
  ·
    refine ⟨11546712375578473553343793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15395616500771298071125057 11546712375578473553343793)
    ·
      refine ⟨8660034281683855165007845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11546712375578473553343793 8660034281683855165007845)
      ·
        refine ⟨1623756427815722843438971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8660034281683855165007845 1623756427815722843438971)
        ·
          refine ⟨2435634641723584265158457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623756427815722843438971 2435634641723584265158457)
          ·
            refine ⟨1826725981292688198868843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435634641723584265158457 1826725981292688198868843)
            ·
              refine ⟨2740088971939032298303265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826725981292688198868843 2740088971939032298303265)
              ·
                refine ⟨2055066728954274223727449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740088971939032298303265 2055066728954274223727449)
                ·
                  refine ⟨1541300046715705667795587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055066728954274223727449 1541300046715705667795587)
                  ·
                    refine ⟨2311950070073558501693381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1541300046715705667795587 2311950070073558501693381)
                    ·
                      refine ⟨433490638138792219067509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2311950070073558501693381 433490638138792219067509)
                      ·
                        rfl

theorem cell23_844220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_844220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844220 prefixEnd_844220 := by exact prefixLift 844220
  have htrace : WordTrace (prefixWord ++ tailWord_844220) baseStart_844220 baseEnd_844220 := by
    simpa [prefixWord, tailWord_844220, baseEnd_844220] using wordTrace_append hprefix tailTrace_844220
  have hstable : (prefixWord ++ tailWord_844220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844220).length < 2 ^ (prefixWord ++ tailWord_844220).sum := by decide
  have hdescent : baseEnd_844220 < baseStart_844220 := by decide
  rcases family_descends (prefixWord ++ tailWord_844220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844277 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 6]
def baseStart_844277 : Nat := 118140960795 + 844277 * 2 ^ 59
def prefixEnd_844277 : Nat := 4983230072969 + 3 ^ 40 * 844277 * 2
def baseEnd_844277 : Nat := 48168878504010944006083

theorem tailTrace_844277 : CollatzResearch.WordTrace tailWord_844277 prefixEnd_844277 48168878504010944006083 := by
  unfold tailWord_844277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30793311962336094877075085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20528874641557396584716723 30793311962336094877075085)
  ·
    refine ⟨11547491985876035578903157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30793311962336094877075085 11547491985876035578903157)
    ·
      refine ⟨1082577373675878335522171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11547491985876035578903157 1082577373675878335522171)
      ·
        refine ⟨1623866060513817503283257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082577373675878335522171 1623866060513817503283257)
        ·
          refine ⟨1217899545385363127462443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623866060513817503283257 1217899545385363127462443)
          ·
            refine ⟨1826849318078044691193665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217899545385363127462443 1826849318078044691193665)
            ·
              refine ⟨1370136988558533518395249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826849318078044691193665 1370136988558533518395249)
              ·
                refine ⟨1027602741418900138796437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370136988558533518395249 1027602741418900138796437)
                ·
                  refine ⟨48168878504010944006083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1027602741418900138796437 48168878504010944006083)
                  ·
                    rfl

theorem cell23_844277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_844277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844277 prefixEnd_844277 := by exact prefixLift 844277
  have htrace : WordTrace (prefixWord ++ tailWord_844277) baseStart_844277 baseEnd_844277 := by
    simpa [prefixWord, tailWord_844277, baseEnd_844277] using wordTrace_append hprefix tailTrace_844277
  have hstable : (prefixWord ++ tailWord_844277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844277).length < 2 ^ (prefixWord ++ tailWord_844277).sum := by decide
  have hdescent : baseEnd_844277 < baseStart_844277 := by decide
  rcases family_descends (prefixWord ++ tailWord_844277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844280 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_844280 : Nat := 118140960795 + 844280 * 2 ^ 59
def prefixEnd_844280 : Nat := 4983230072969 + 3 ^ 40 * 844280 * 2
def baseEnd_844280 : Nat := 433521446978061984317233

theorem tailTrace_844280 : CollatzResearch.WordTrace tailWord_844280 prefixEnd_844280 433521446978061984317233 := by
  unfold tailWord_844280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15396710690662613194717147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20528947587550150926289529 15396710690662613194717147)
  ·
    refine ⟨23095066035993919792075721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15396710690662613194717147 23095066035993919792075721)
    ·
      refine ⟨17321299526995439844056791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23095066035993919792075721 17321299526995439844056791)
      ·
        refine ⟨25981949290493159766085187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17321299526995439844056791 25981949290493159766085187)
        ·
          refine ⟨38972923935739739649127781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25981949290493159766085187 38972923935739739649127781)
          ·
            refine ⟨7307423237951201184211459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38972923935739739649127781 7307423237951201184211459)
            ·
              refine ⟨10961134856926801776317189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307423237951201184211459 10961134856926801776317189)
              ·
                refine ⟨2055212785673775333059473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10961134856926801776317189 2055212785673775333059473)
                ·
                  refine ⟨1541409589255331499794605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055212785673775333059473 1541409589255331499794605)
                  ·
                    refine ⟨578028595970749312422977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541409589255331499794605 578028595970749312422977)
                    ·
                      refine ⟨433521446978061984317233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578028595970749312422977 433521446978061984317233)
                      ·
                        rfl

theorem cell23_844280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_844280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844280 prefixEnd_844280 := by exact prefixLift 844280
  have htrace : WordTrace (prefixWord ++ tailWord_844280) baseStart_844280 baseEnd_844280 := by
    simpa [prefixWord, tailWord_844280, baseEnd_844280] using wordTrace_append hprefix tailTrace_844280
  have hstable : (prefixWord ++ tailWord_844280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844280).length < 2 ^ (prefixWord ++ tailWord_844280).sum := by decide
  have hdescent : baseEnd_844280 < baseStart_844280 := by decide
  rcases family_descends (prefixWord ++ tailWord_844280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844287 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 1, 1, 3]
def baseStart_844287 : Nat := 118140960795 + 844287 * 2 ^ 59
def prefixEnd_844287 : Nat := 4983230072969 + 3 ^ 40 * 844287 * 2
def baseEnd_844287 : Nat := 433525041342643456929701

theorem tailTrace_844287 : CollatzResearch.WordTrace tailWord_844287 prefixEnd_844287 433525041342643456929701 := by
  unfold tailWord_844287
  simp only [CollatzResearch.WordTrace]
  refine ⟨30793676692299866584939115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20529117794866577723292743 30793676692299866584939115)
  ·
    refine ⟨46190515038449799877408673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30793676692299866584939115 46190515038449799877408673)
    ·
      refine ⟨34642886278837349908056505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46190515038449799877408673 34642886278837349908056505)
      ·
        refine ⟨25982164709128012431042379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34642886278837349908056505 25982164709128012431042379)
        ·
          refine ⟨38973247063692018646563569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25982164709128012431042379 38973247063692018646563569)
          ·
            refine ⟨29229935297769013984922677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38973247063692018646563569 29229935297769013984922677)
            ·
              refine ⟨2740306434165845061086501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29229935297769013984922677 2740306434165845061086501)
              ·
                refine ⟨513807456406095948953719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2740306434165845061086501 513807456406095948953719)
                ·
                  refine ⟨770711184609143923430579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513807456406095948953719 770711184609143923430579)
                  ·
                    refine ⟨1156066776913715885145869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 770711184609143923430579 1156066776913715885145869)
                    ·
                      refine ⟨433525041342643456929701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156066776913715885145869 433525041342643456929701)
                      ·
                        rfl

theorem cell23_844287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_844287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844287 prefixEnd_844287 := by exact prefixLift 844287
  have htrace : WordTrace (prefixWord ++ tailWord_844287) baseStart_844287 baseEnd_844287 := by
    simpa [prefixWord, tailWord_844287, baseEnd_844287] using wordTrace_append hprefix tailTrace_844287
  have hstable : (prefixWord ++ tailWord_844287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844287).length < 2 ^ (prefixWord ++ tailWord_844287).sum := by decide
  have hdescent : baseEnd_844287 < baseStart_844287 := by decide
  rcases family_descends (prefixWord ++ tailWord_844287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844293 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_844293 : Nat := 118140960795 + 844293 * 2 ^ 59
def prefixEnd_844293 : Nat := 4983230072969 + 3 ^ 40 * 844293 * 2
def baseEnd_844293 : Nat := 433528122226570433454673

theorem tailTrace_844293 : CollatzResearch.WordTrace tailWord_844293 prefixEnd_844293 433528122226570433454673 := by
  unfold tailWord_844293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30793895530278129609657533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20529263686852086406438355 30793895530278129609657533)
  ·
    refine ⟨11547710823854298603621575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30793895530278129609657533 11547710823854298603621575)
    ·
      refine ⟨17321566235781447905432363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547710823854298603621575 17321566235781447905432363)
      ·
        refine ⟨25982349353672171858148545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17321566235781447905432363 25982349353672171858148545)
        ·
          refine ⟨19486762015254128893611409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25982349353672171858148545 19486762015254128893611409)
          ·
            refine ⟨14615071511440596670208557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19486762015254128893611409 14615071511440596670208557)
            ·
              refine ⟨5480651816790223751328209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14615071511440596670208557 5480651816790223751328209)
              ·
                refine ⟨4110488862592667813496157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480651816790223751328209 4110488862592667813496157)
                ·
                  refine ⟨1541433323472250430061059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4110488862592667813496157 1541433323472250430061059)
                  ·
                    refine ⟨2312149985208375645091589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1541433323472250430061059 2312149985208375645091589)
                    ·
                      refine ⟨433528122226570433454673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2312149985208375645091589 433528122226570433454673)
                      ·
                        rfl

theorem cell23_844293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_844293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844293 prefixEnd_844293 := by exact prefixLift 844293
  have htrace : WordTrace (prefixWord ++ tailWord_844293) baseStart_844293 baseEnd_844293 := by
    simpa [prefixWord, tailWord_844293, baseEnd_844293] using wordTrace_append hprefix tailTrace_844293
  have hstable : (prefixWord ++ tailWord_844293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844293).length < 2 ^ (prefixWord ++ tailWord_844293).sum := by decide
  have hdescent : baseEnd_844293 < baseStart_844293 := by decide
  rcases family_descends (prefixWord ++ tailWord_844293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844294 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_844294 : Nat := 118140960795 + 844294 * 2 ^ 59
def prefixEnd_844294 : Nat := 4983230072969 + 3 ^ 40 * 844294 * 2
def baseEnd_844294 : Nat := 48169848411913881060241

theorem tailTrace_844294 : CollatzResearch.WordTrace tailWord_844294 prefixEnd_844294 48169848411913881060241 := by
  unfold tailWord_844294
  simp only [CollatzResearch.WordTrace]
  refine ⟨962310375102328336888873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20529288002183004520295957 962310375102328336888873)
  ·
    refine ⟨721732781326746252666655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 962310375102328336888873 721732781326746252666655)
    ·
      refine ⟨1082599171990119378999983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721732781326746252666655 1082599171990119378999983)
      ·
        refine ⟨1623898757985179068499975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082599171990119378999983 1623898757985179068499975)
        ·
          refine ⟨2435848136977768602749963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623898757985179068499975 2435848136977768602749963)
          ·
            refine ⟨3653772205466652904124945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435848136977768602749963 3653772205466652904124945)
            ·
              refine ⟨2740329154099989678093709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653772205466652904124945 2740329154099989678093709)
              ·
                refine ⟨1027623432787496129285141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2740329154099989678093709 1027623432787496129285141)
                ·
                  refine ⟨48169848411913881060241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1027623432787496129285141 48169848411913881060241)
                  ·
                    rfl

theorem cell23_844294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_844294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844294 prefixEnd_844294 := by exact prefixLift 844294
  have htrace : WordTrace (prefixWord ++ tailWord_844294) baseStart_844294 baseEnd_844294 := by
    simpa [prefixWord, tailWord_844294, baseEnd_844294] using wordTrace_append hprefix tailTrace_844294
  have hstable : (prefixWord ++ tailWord_844294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844294).length < 2 ^ (prefixWord ++ tailWord_844294).sum := by decide
  have hdescent : baseEnd_844294 < baseStart_844294 := by decide
  rcases family_descends (prefixWord ++ tailWord_844294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844344 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_844344 : Nat := 118140960795 + 844344 * 2 ^ 59
def prefixEnd_844344 : Nat := 4983230072969 + 3 ^ 40 * 844344 * 2
def baseEnd_844344 : Nat := 433554309739949733916939

theorem tailTrace_844344 : CollatzResearch.WordTrace tailWord_844344 prefixEnd_844344 433554309739949733916939 := by
  unfold tailWord_844344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397877826546682659882043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20530503768728910213176057 15397877826546682659882043)
  ·
    refine ⟨23096816739820023989823065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15397877826546682659882043 23096816739820023989823065)
    ·
      refine ⟨17322612554865017992367299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23096816739820023989823065 17322612554865017992367299)
      ·
        refine ⟨25983918832297526988550949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17322612554865017992367299 25983918832297526988550949)
        ·
          refine ⟨4871984781055786310353303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25983918832297526988550949 4871984781055786310353303)
          ·
            refine ⟨7307977171583679465529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871984781055786310353303 7307977171583679465529955)
            ·
              refine ⟨10961965757375519198294933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7307977171583679465529955 10961965757375519198294933)
              ·
                refine ⟨513842144876977462420075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10961965757375519198294933 513842144876977462420075)
                ·
                  refine ⟨770763217315466193630113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513842144876977462420075 770763217315466193630113)
                  ·
                    refine ⟨578072412986599645222585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 770763217315466193630113 578072412986599645222585)
                    ·
                      refine ⟨433554309739949733916939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578072412986599645222585 433554309739949733916939)
                      ·
                        rfl

theorem cell23_844344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_844344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844344 prefixEnd_844344 := by exact prefixLift 844344
  have htrace : WordTrace (prefixWord ++ tailWord_844344) baseStart_844344 baseEnd_844344 := by
    simpa [prefixWord, tailWord_844344, baseEnd_844344] using wordTrace_append hprefix tailTrace_844344
  have hstable : (prefixWord ++ tailWord_844344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844344).length < 2 ^ (prefixWord ++ tailWord_844344).sum := by decide
  have hdescent : baseEnd_844344 < baseStart_844344 := by decide
  rcases family_descends (prefixWord ++ tailWord_844344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844373 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_844373 : Nat := 118140960795 + 844373 * 2 ^ 59
def prefixEnd_844373 : Nat := 4983230072969 + 3 ^ 40 * 844373 * 2
def baseEnd_844373 : Nat := 433569200678930120454305

theorem tailTrace_844373 : CollatzResearch.WordTrace tailWord_844373 prefixEnd_844373 433569200678930120454305 := by
  unfold tailWord_844373
  simp only [CollatzResearch.WordTrace]
  refine ⟨30796813369988303272569773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20531208913325535515046515 30796813369988303272569773)
  ·
    refine ⟨11548805013745613727213665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30796813369988303272569773 11548805013745613727213665)
    ·
      refine ⟨8661603760309210295410249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11548805013745613727213665 8661603760309210295410249)
      ·
        refine ⟨6496202820231907721557687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661603760309210295410249 6496202820231907721557687)
        ·
          refine ⟨9744304230347861582336531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496202820231907721557687 9744304230347861582336531)
          ·
            refine ⟨14616456345521792373504797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9744304230347861582336531 14616456345521792373504797)
            ·
              refine ⟨5481171129570672140064299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14616456345521792373504797 5481171129570672140064299)
              ·
                refine ⟨8221756694356008210096449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481171129570672140064299 8221756694356008210096449)
                ·
                  refine ⟨6166317520767006157572337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8221756694356008210096449 6166317520767006157572337)
                  ·
                    refine ⟨4624738140575254618179253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166317520767006157572337 4624738140575254618179253)
                    ·
                      refine ⟨433569200678930120454305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4624738140575254618179253 433569200678930120454305)
                      ·
                        rfl

theorem cell23_844373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_844373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844373 prefixEnd_844373 := by exact prefixLift 844373
  have htrace : WordTrace (prefixWord ++ tailWord_844373) baseStart_844373 baseEnd_844373 := by
    simpa [prefixWord, tailWord_844373, baseEnd_844373] using wordTrace_append hprefix tailTrace_844373
  have hstable : (prefixWord ++ tailWord_844373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844373).length < 2 ^ (prefixWord ++ tailWord_844373).sum := by decide
  have hdescent : baseEnd_844373 < baseStart_844373 := by decide
  rcases family_descends (prefixWord ++ tailWord_844373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844387 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 1, 3, 2]
def baseStart_844387 : Nat := 118140960795 + 844387 * 2 ^ 59
def prefixEnd_844387 : Nat := 4983230072969 + 3 ^ 40 * 844387 * 2
def baseEnd_844387 : Nat := 433576389408093065679241

theorem tailTrace_844387 : CollatzResearch.WordTrace tailWord_844387 prefixEnd_844387 433576389408093065679241 := by
  unfold tailWord_844387
  simp only [CollatzResearch.WordTrace]
  refine ⟨30797323991937583663579415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20531549327958389109052943 30797323991937583663579415)
  ·
    refine ⟨46195985987906375495369123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30797323991937583663579415 46195985987906375495369123)
    ·
      refine ⟨69293978981859563243053685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46195985987906375495369123 69293978981859563243053685)
      ·
        refine ⟨6496310529549334054036283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69293978981859563243053685 6496310529549334054036283)
        ·
          refine ⟨9744465794324001081054425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496310529549334054036283 9744465794324001081054425)
          ·
            refine ⟨7308349345743000810790819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9744465794324001081054425 7308349345743000810790819)
            ·
              refine ⟨10962524018614501216186229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308349345743000810790819 10962524018614501216186229)
              ·
                refine ⟨1027736626745109489017459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10962524018614501216186229 1027736626745109489017459)
                ·
                  refine ⟨1541604940117664233526189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027736626745109489017459 1541604940117664233526189)
                  ·
                    refine ⟨578101852544124087572321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541604940117664233526189 578101852544124087572321)
                    ·
                      refine ⟨433576389408093065679241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578101852544124087572321 433576389408093065679241)
                      ·
                        rfl

theorem cell23_844387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_844387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844387 prefixEnd_844387 := by exact prefixLift 844387
  have htrace : WordTrace (prefixWord ++ tailWord_844387) baseStart_844387 baseEnd_844387 := by
    simpa [prefixWord, tailWord_844387, baseEnd_844387] using wordTrace_append hprefix tailTrace_844387
  have hstable : (prefixWord ++ tailWord_844387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844387).length < 2 ^ (prefixWord ++ tailWord_844387).sum := by decide
  have hdescent : baseEnd_844387 < baseStart_844387 := by decide
  rcases family_descends (prefixWord ++ tailWord_844387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844417 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_844417 : Nat := 118140960795 + 844417 * 2 ^ 59
def prefixEnd_844417 : Nat := 4983230072969 + 3 ^ 40 * 844417 * 2
def baseEnd_844417 : Nat := 433591793827727948304103

theorem tailTrace_844417 : CollatzResearch.WordTrace tailWord_844417 prefixEnd_844417 433591793827727948304103 := by
  unfold tailWord_844417
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798418181828898787171505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20532278787885932524781003 30798418181828898787171505)
  ·
    refine ⟨23098813636371674090378629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30798418181828898787171505 23098813636371674090378629)
    ·
      refine ⟨4331027556819688891945993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23098813636371674090378629 4331027556819688891945993)
      ·
        refine ⟨3248270667614766668959495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4331027556819688891945993 3248270667614766668959495)
        ·
          refine ⟨4872406001422150003439243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248270667614766668959495 4872406001422150003439243)
          ·
            refine ⟨7308609002133225005158865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872406001422150003439243 7308609002133225005158865)
            ·
              refine ⟨5481456751599918753869149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308609002133225005158865 5481456751599918753869149)
              ·
                refine ⟨2055546281849969532700931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5481456751599918753869149 2055546281849969532700931)
                ·
                  refine ⟨3083319422774954299051397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055546281849969532700931 3083319422774954299051397)
                  ·
                    refine ⟨578122391770303931072137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083319422774954299051397 578122391770303931072137)
                    ·
                      refine ⟨433591793827727948304103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578122391770303931072137 433591793827727948304103)
                      ·
                        rfl

theorem cell23_844417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_844417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844417 prefixEnd_844417 := by exact prefixLift 844417
  have htrace : WordTrace (prefixWord ++ tailWord_844417) baseStart_844417 baseEnd_844417 := by
    simpa [prefixWord, tailWord_844417, baseEnd_844417] using wordTrace_append hprefix tailTrace_844417
  have hstable : (prefixWord ++ tailWord_844417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844417).length < 2 ^ (prefixWord ++ tailWord_844417).sum := by decide
  have hdescent : baseEnd_844417 < baseStart_844417 := by decide
  rcases family_descends (prefixWord ++ tailWord_844417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844420 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_844420 : Nat := 118140960795 + 844420 * 2 ^ 59
def prefixEnd_844420 : Nat := 4983230072969 + 3 ^ 40 * 844420 * 2
def baseEnd_844420 : Nat := 433593334269691436566589

theorem tailTrace_844420 : CollatzResearch.WordTrace tailWord_844420 prefixEnd_844420 433593334269691436566589 := by
  unfold tailWord_844420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399263800409015149765357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20532351733878686866353809 15399263800409015149765357)
  ·
    refine ⟨5774723925153380681162009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15399263800409015149765357 5774723925153380681162009)
    ·
      refine ⟨4331042943865035510871507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5774723925153380681162009 4331042943865035510871507)
      ·
        refine ⟨6496564415797553266307261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331042943865035510871507 6496564415797553266307261)
        ·
          refine ⟨2436211655924082474865223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6496564415797553266307261 2436211655924082474865223)
          ·
            refine ⟨3654317483886123712297835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436211655924082474865223 3654317483886123712297835)
            ·
              refine ⟨5481476225829185568446753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654317483886123712297835 5481476225829185568446753)
              ·
                refine ⟨4111107169371889176335065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5481476225829185568446753 4111107169371889176335065)
                ·
                  refine ⟨3083330377028916882251299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111107169371889176335065 3083330377028916882251299)
                  ·
                    refine ⟨4624995565543375323376949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083330377028916882251299 4624995565543375323376949)
                    ·
                      refine ⟨433593334269691436566589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4624995565543375323376949 433593334269691436566589)
                      ·
                        rfl

theorem cell23_844420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_844420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844420 prefixEnd_844420 := by exact prefixLift 844420
  have htrace : WordTrace (prefixWord ++ tailWord_844420) baseStart_844420 baseEnd_844420 := by
    simpa [prefixWord, tailWord_844420, baseEnd_844420] using wordTrace_append hprefix tailTrace_844420
  have hstable : (prefixWord ++ tailWord_844420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844420).length < 2 ^ (prefixWord ++ tailWord_844420).sum := by decide
  have hdescent : baseEnd_844420 < baseStart_844420 := by decide
  rcases family_descends (prefixWord ++ tailWord_844420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844423 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 9]
def baseStart_844423 : Nat := 118140960795 + 844423 * 2 ^ 59
def prefixEnd_844423 : Nat := 4983230072969 + 3 ^ 40 * 844423 * 2
def baseEnd_844423 : Nat := 48177208301294991647675

theorem tailTrace_844423 : CollatzResearch.WordTrace tailWord_844423 prefixEnd_844423 48177208301294991647675 := by
  unfold tailWord_844423
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798637019807161811889923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20532424679871441207926615 30798637019807161811889923)
  ·
    refine ⟨46197955529710742717834885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30798637019807161811889923 46197955529710742717834885)
    ·
      refine ⟨8662116661820764259594041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46197955529710742717834885 8662116661820764259594041)
      ·
        refine ⟨6496587496365573194695531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8662116661820764259594041 6496587496365573194695531)
        ·
          refine ⟨9744881244548359792043297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496587496365573194695531 9744881244548359792043297)
          ·
            refine ⟨7308660933411269844032473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9744881244548359792043297 7308660933411269844032473)
            ·
              refine ⟨5481495700058452383024355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308660933411269844032473 5481495700058452383024355)
              ·
                refine ⟨8222243550087678574536533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481495700058452383024355 8222243550087678574536533)
                ·
                  refine ⟨48177208301294991647675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8222243550087678574536533 48177208301294991647675)
                  ·
                    rfl

theorem cell23_844423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 9].length) (baseStart_844423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844423 prefixEnd_844423 := by exact prefixLift 844423
  have htrace : WordTrace (prefixWord ++ tailWord_844423) baseStart_844423 baseEnd_844423 := by
    simpa [prefixWord, tailWord_844423, baseEnd_844423] using wordTrace_append hprefix tailTrace_844423
  have hstable : (prefixWord ++ tailWord_844423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844423).length < 2 ^ (prefixWord ++ tailWord_844423).sum := by decide
  have hdescent : baseEnd_844423 < baseStart_844423 := by decide
  rcases family_descends (prefixWord ++ tailWord_844423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844434 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_844434 : Nat := 118140960795 + 844434 * 2 ^ 59
def prefixEnd_844434 : Nat := 4983230072969 + 3 ^ 40 * 844434 * 2
def baseEnd_844434 : Nat := 433600522998854381791525

theorem tailTrace_844434 : CollatzResearch.WordTrace tailWord_844434 prefixEnd_844434 433600522998854381791525 := by
  unfold tailWord_844434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699759555691827672635089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20532692148511540460360237 7699759555691827672635089)
  ·
    refine ⟨5774819666768870754476317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7699759555691827672635089 5774819666768870754476317)
    ·
      refine ⟨2165557375038326532928619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5774819666768870754476317 2165557375038326532928619)
      ·
        refine ⟨3248336062557489799392929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165557375038326532928619 3248336062557489799392929)
        ·
          refine ⟨2436252046918117349544697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3248336062557489799392929 2436252046918117349544697)
          ·
            refine ⟨1827189035188588012158523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436252046918117349544697 1827189035188588012158523)
            ·
              refine ⟨2740783552782882018237785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827189035188588012158523 2740783552782882018237785)
              ·
                refine ⟨2055587664587161513678339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740783552782882018237785 2055587664587161513678339)
                ·
                  refine ⟨3083381496880742270517509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055587664587161513678339 3083381496880742270517509)
                  ·
                    refine ⟨578134030665139175722033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083381496880742270517509 578134030665139175722033)
                    ·
                      refine ⟨433600522998854381791525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578134030665139175722033 433600522998854381791525)
                      ·
                        rfl

theorem cell23_844434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_844434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844434 prefixEnd_844434 := by exact prefixLift 844434
  have htrace : WordTrace (prefixWord ++ tailWord_844434) baseStart_844434 baseEnd_844434 := by
    simpa [prefixWord, tailWord_844434, baseEnd_844434] using wordTrace_append hprefix tailTrace_844434
  have hstable : (prefixWord ++ tailWord_844434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844434).length < 2 ^ (prefixWord ++ tailWord_844434).sum := by decide
  have hdescent : baseEnd_844434 < baseStart_844434 := by decide
  rcases family_descends (prefixWord ++ tailWord_844434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844453 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_844453 : Nat := 118140960795 + 844453 * 2 ^ 59
def prefixEnd_844453 : Nat := 4983230072969 + 3 ^ 40 * 844453 * 2
def baseEnd_844453 : Nat := 144536759710429935817979

theorem tailTrace_844453 : CollatzResearch.WordTrace tailWord_844453 prefixEnd_844453 144536759710429935817979 := by
  unfold tailWord_844453
  simp only [CollatzResearch.WordTrace]
  refine ⟨30799731209698476935482013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20533154139798984623654675 30799731209698476935482013)
  ·
    refine ⟨11549899203636928850805755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30799731209698476935482013 11549899203636928850805755)
    ·
      refine ⟨17324848805455393276208633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549899203636928850805755 17324848805455393276208633)
      ·
        refine ⟨12993636604091544957156475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17324848805455393276208633 12993636604091544957156475)
        ·
          refine ⟨19490454906137317435734713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993636604091544957156475 19490454906137317435734713)
          ·
            refine ⟨14617841179602988076801035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19490454906137317435734713 14617841179602988076801035)
            ·
              refine ⟨21926761769404482115201553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14617841179602988076801035 21926761769404482115201553)
              ·
                refine ⟨16445071327053361586401165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21926761769404482115201553 16445071327053361586401165)
                ·
                  refine ⟨6166901747645010594900437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16445071327053361586401165 6166901747645010594900437)
                  ·
                    refine ⟨144536759710429935817979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6166901747645010594900437 144536759710429935817979)
                    ·
                      rfl

theorem cell23_844453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_844453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844453 prefixEnd_844453 := by exact prefixLift 844453
  have htrace : WordTrace (prefixWord ++ tailWord_844453) baseStart_844453 baseEnd_844453 := by
    simpa [prefixWord, tailWord_844453, baseEnd_844453] using wordTrace_append hprefix tailTrace_844453
  have hstable : (prefixWord ++ tailWord_844453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844453).length < 2 ^ (prefixWord ++ tailWord_844453).sum := by decide
  have hdescent : baseEnd_844453 < baseStart_844453 := by decide
  rcases family_descends (prefixWord ++ tailWord_844453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844517 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_844517 : Nat := 118140960795 + 844517 * 2 ^ 59
def prefixEnd_844517 : Nat := 4983230072969 + 3 ^ 40 * 844517 * 2
def baseEnd_844517 : Nat := 144547713964392519017881

theorem tailTrace_844517 : CollatzResearch.WordTrace tailWord_844517 prefixEnd_844517 144547713964392519017881 := by
  unfold tailWord_844517
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802065481466615865811805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20534710320977743910541203 30802065481466615865811805)
  ·
    refine ⟨11550774555549980949679427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30802065481466615865811805 11550774555549980949679427)
    ·
      refine ⟨17326161833324971424519141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550774555549980949679427 17326161833324971424519141)
      ·
        refine ⟨3248655343748432142097339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17326161833324971424519141 3248655343748432142097339)
        ·
          refine ⟨4872983015622648213146009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248655343748432142097339 4872983015622648213146009)
          ·
            refine ⟨3654737261716986159859507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4872983015622648213146009 3654737261716986159859507)
            ·
              refine ⟨5482105892575479239789261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654737261716986159859507 5482105892575479239789261)
              ·
                refine ⟨2055789709715804714920973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5482105892575479239789261 2055789709715804714920973)
                ·
                  refine ⟨770921141143426768095365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2055789709715804714920973 770921141143426768095365)
                  ·
                    refine ⟨144547713964392519017881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770921141143426768095365 144547713964392519017881)
                    ·
                      rfl

theorem cell23_844517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_844517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844517 prefixEnd_844517 := by exact prefixLift 844517
  have htrace : WordTrace (prefixWord ++ tailWord_844517) baseStart_844517 baseEnd_844517 := by
    simpa [prefixWord, tailWord_844517, baseEnd_844517] using wordTrace_append hprefix tailTrace_844517
  have hstable : (prefixWord ++ tailWord_844517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844517).length < 2 ^ (prefixWord ++ tailWord_844517).sum := by decide
  have hdescent : baseEnd_844517 < baseStart_844517 := by decide
  rcases family_descends (prefixWord ++ tailWord_844517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844551 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 1, 4]
def baseStart_844551 : Nat := 118140960795 + 844551 * 2 ^ 59
def prefixEnd_844551 : Nat := 4983230072969 + 3 ^ 40 * 844551 * 2
def baseEnd_844551 : Nat := 144553533411810141342829

theorem tailTrace_844551 : CollatzResearch.WordTrace tailWord_844551 prefixEnd_844551 144553533411810141342829 := by
  unfold tailWord_844551
  simp only [CollatzResearch.WordTrace]
  refine ⟨30803305563343439672549507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20535537042228959781699671 30803305563343439672549507)
  ·
    refine ⟨46204958345015159508824261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30803305563343439672549507 46204958345015159508824261)
    ·
      refine ⟨8663429689690342407904549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46204958345015159508824261 8663429689690342407904549)
      ·
        refine ⟨1624393066816939201482103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8663429689690342407904549 1624393066816939201482103)
        ·
          refine ⟨2436589600225408802223155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624393066816939201482103 2436589600225408802223155)
          ·
            refine ⟨3654884400338113203334733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436589600225408802223155 3654884400338113203334733)
            ·
              refine ⟨1370581650126792451250525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654884400338113203334733 1370581650126792451250525)
              ·
                refine ⟨513968118797547169218947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370581650126792451250525 513968118797547169218947)
                ·
                  refine ⟨770952178196320753828421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513968118797547169218947 770952178196320753828421)
                  ·
                    refine ⟨144553533411810141342829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770952178196320753828421 144553533411810141342829)
                    ·
                      rfl

theorem cell23_844551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_844551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844551 prefixEnd_844551 := by exact prefixLift 844551
  have htrace : WordTrace (prefixWord ++ tailWord_844551) baseStart_844551 baseEnd_844551 := by
    simpa [prefixWord, tailWord_844551, baseEnd_844551] using wordTrace_append hprefix tailTrace_844551
  have hstable : (prefixWord ++ tailWord_844551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844551).length < 2 ^ (prefixWord ++ tailWord_844551).sum := by decide
  have hdescent : baseEnd_844551 < baseStart_844551 := by decide
  rcases family_descends (prefixWord ++ tailWord_844551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844584 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_844584 : Nat := 118140960795 + 844584 * 2 ^ 59
def prefixEnd_844584 : Nat := 4983230072969 + 3 ^ 40 * 844584 * 2
def baseEnd_844584 : Nat := 433677545097028794915835

theorem tailTrace_844584 : CollatzResearch.WordTrace tailWord_844584 prefixEnd_844584 433677545097028794915835 := by
  unfold tailWord_844584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402254586111943154250403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20536339448149257539000537 15402254586111943154250403)
  ·
    refine ⟨23103381879167914731375605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15402254586111943154250403 23103381879167914731375605)
    ·
      refine ⟨2165942051171992006066463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23103381879167914731375605 2165942051171992006066463)
      ·
        refine ⟨3248913076757988009099695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165942051171992006066463 3248913076757988009099695)
        ·
          refine ⟨4873369615136982013649543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248913076757988009099695 4873369615136982013649543)
          ·
            refine ⟨7310054422705473020474315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873369615136982013649543 7310054422705473020474315)
            ·
              refine ⟨10965081634058209530711473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310054422705473020474315 10965081634058209530711473)
              ·
                refine ⟨8223811225543657148033605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965081634058209530711473 8223811225543657148033605)
                ·
                  refine ⟨1541964604789435715256301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8223811225543657148033605 1541964604789435715256301)
                  ·
                    refine ⟨578236726796038393221113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1541964604789435715256301 578236726796038393221113)
                    ·
                      refine ⟨433677545097028794915835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578236726796038393221113 433677545097028794915835)
                      ·
                        rfl

theorem cell23_844584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_844584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844584 prefixEnd_844584 := by exact prefixLift 844584
  have htrace : WordTrace (prefixWord ++ tailWord_844584) baseStart_844584 baseEnd_844584 := by
    simpa [prefixWord, tailWord_844584, baseEnd_844584] using wordTrace_append hprefix tailTrace_844584
  have hstable : (prefixWord ++ tailWord_844584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844584).length < 2 ^ (prefixWord ++ tailWord_844584).sum := by decide
  have hdescent : baseEnd_844584 < baseStart_844584 := by decide
  rcases family_descends (prefixWord ++ tailWord_844584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844607 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 6]
def baseStart_844607 : Nat := 118140960795 + 844607 * 2 ^ 59
def prefixEnd_844607 : Nat := 4983230072969 + 3 ^ 40 * 844607 * 2
def baseEnd_844607 : Nat := 144563118384027401642743

theorem tailTrace_844607 : CollatzResearch.WordTrace tailWord_844607 prefixEnd_844607 144563118384027401642743 := by
  unfold tailWord_844607
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805348051140561236588075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20536898700760374157725383 30805348051140561236588075)
  ·
    refine ⟨46208022076710841854882113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805348051140561236588075 46208022076710841854882113)
    ·
      refine ⟨34656016557533131391161585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46208022076710841854882113 34656016557533131391161585)
      ·
        refine ⟨25992012418149848543371189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34656016557533131391161585 25992012418149848543371189)
        ·
          refine ⟨2436751164201548300941049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25992012418149848543371189 2436751164201548300941049)
          ·
            refine ⟨1827563373151161225705787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436751164201548300941049 1827563373151161225705787)
            ·
              refine ⟨2741345059726741838558681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827563373151161225705787 2741345059726741838558681)
              ·
                refine ⟨2056008794795056378919011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741345059726741838558681 2056008794795056378919011)
                ·
                  refine ⟨3084013192192584568378517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056008794795056378919011 3084013192192584568378517)
                  ·
                    refine ⟨144563118384027401642743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3084013192192584568378517 144563118384027401642743)
                    ·
                      rfl

theorem cell23_844607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_844607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844607 prefixEnd_844607 := by exact prefixLift 844607
  have htrace : WordTrace (prefixWord ++ tailWord_844607) baseStart_844607 baseEnd_844607 := by
    simpa [prefixWord, tailWord_844607, baseEnd_844607] using wordTrace_append hprefix tailTrace_844607
  have hstable : (prefixWord ++ tailWord_844607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844607).length < 2 ^ (prefixWord ++ tailWord_844607).sum := by decide
  have hdescent : baseEnd_844607 < baseStart_844607 := by decide
  rcases family_descends (prefixWord ++ tailWord_844607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844617 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_844617 : Nat := 118140960795 + 844617 * 2 ^ 59
def prefixEnd_844617 : Nat := 4983230072969 + 3 ^ 40 * 844617 * 2
def baseEnd_844617 : Nat := 433694489958627165803183

theorem tailTrace_844617 : CollatzResearch.WordTrace tailWord_844617 prefixEnd_844617 433694489958627165803183 := by
  unfold tailWord_844617
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805712781104332944452105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20537141854069555296301403 30805712781104332944452105)
  ·
    refine ⟨23104284585828249708339079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30805712781104332944452105 23104284585828249708339079)
    ·
      refine ⟨34656426878742374562508619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23104284585828249708339079 34656426878742374562508619)
      ·
        refine ⟨51984640318113561843762929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34656426878742374562508619 51984640318113561843762929)
        ·
          refine ⟨38988480238585171382822197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51984640318113561843762929 38988480238585171382822197)
          ·
            refine ⟨3655170022367359817139581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38988480238585171382822197 3655170022367359817139581)
            ·
              refine ⟨1370688758387759931427343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3655170022367359817139581 1370688758387759931427343)
              ·
                refine ⟨2056033137581639897141015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370688758387759931427343 2056033137581639897141015)
                ·
                  refine ⟨3084049706372459845711523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056033137581639897141015 3084049706372459845711523)
                  ·
                    refine ⟨4626074559558689768567285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3084049706372459845711523 4626074559558689768567285)
                    ·
                      refine ⟨433694489958627165803183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4626074559558689768567285 433694489958627165803183)
                      ·
                        rfl

theorem cell23_844617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_844617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844617 prefixEnd_844617 := by exact prefixLift 844617
  have htrace : WordTrace (prefixWord ++ tailWord_844617) baseStart_844617 baseEnd_844617 := by
    simpa [prefixWord, tailWord_844617, baseEnd_844617] using wordTrace_append hprefix tailTrace_844617
  have hstable : (prefixWord ++ tailWord_844617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844617).length < 2 ^ (prefixWord ++ tailWord_844617).sum := by decide
  have hdescent : baseEnd_844617 < baseStart_844617 := by decide
  rcases family_descends (prefixWord ++ tailWord_844617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844620 : List Nat := [2, 2, 1, 3, 3, 12]
def baseStart_844620 : Nat := 118140960795 + 844620 * 2 ^ 59
def prefixEnd_844620 : Nat := 4983230072969 + 3 ^ 40 * 844620 * 2
def baseEnd_844620 : Nat := 1784757326751401868583

theorem tailTrace_844620 : CollatzResearch.WordTrace tailWord_844620 prefixEnd_844620 1784757326751401868583 := by
  unfold tailWord_844620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402911100046732228405657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20537214800062309637874209 15402911100046732228405657)
  ·
    refine ⟨11552183325035049171304243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15402911100046732228405657 11552183325035049171304243)
    ·
      refine ⟨17328274987552573756956365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552183325035049171304243 17328274987552573756956365)
      ·
        refine ⟨6498103120332215158858637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17328274987552573756956365 6498103120332215158858637)
        ·
          refine ⟨2436788670124580684571989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6498103120332215158858637 2436788670124580684571989)
          ·
            refine ⟨1784757326751401868583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2436788670124580684571989 1784757326751401868583)
            ·
              rfl

theorem cell23_844620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 12].length) (baseStart_844620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844620 prefixEnd_844620 := by exact prefixLift 844620
  have htrace : WordTrace (prefixWord ++ tailWord_844620) baseStart_844620 baseEnd_844620 := by
    simpa [prefixWord, tailWord_844620, baseEnd_844620] using wordTrace_append hprefix tailTrace_844620
  have hstable : (prefixWord ++ tailWord_844620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844620).length < 2 ^ (prefixWord ++ tailWord_844620).sum := by decide
  have hdescent : baseEnd_844620 < baseStart_844620 := by decide
  rcases family_descends (prefixWord ++ tailWord_844620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844625 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_844625 : Nat := 118140960795 + 844625 * 2 ^ 59
def prefixEnd_844625 : Nat := 4983230072969 + 3 ^ 40 * 844625 * 2
def baseEnd_844625 : Nat := 433698597803863134503147

theorem tailTrace_844625 : CollatzResearch.WordTrace tailWord_844625 prefixEnd_844625 433698597803863134503147 := by
  unfold tailWord_844625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30806004565075350310743329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20537336376716900207162219 30806004565075350310743329)
  ·
    refine ⟨23104503423806512733057497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30806004565075350310743329 23104503423806512733057497)
    ·
      refine ⟨17328377567854884549793123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23104503423806512733057497 17328377567854884549793123)
      ·
        refine ⟨25992566351782326824689685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17328377567854884549793123 25992566351782326824689685)
        ·
          refine ⟨1218401547739796569907329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25992566351782326824689685 1218401547739796569907329)
          ·
            refine ⟨913801160804847427430497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218401547739796569907329 913801160804847427430497)
            ·
              refine ⟨685350870603635570572873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913801160804847427430497 685350870603635570572873)
              ·
                refine ⟨514013152952726677929655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685350870603635570572873 514013152952726677929655)
                ·
                  refine ⟨771019729429090016894483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514013152952726677929655 771019729429090016894483)
                  ·
                    refine ⟨1156529594143635025341725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771019729429090016894483 1156529594143635025341725)
                    ·
                      refine ⟨433698597803863134503147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156529594143635025341725 433698597803863134503147)
                      ·
                        rfl

theorem cell23_844625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_844625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844625 prefixEnd_844625 := by exact prefixLift 844625
  have htrace : WordTrace (prefixWord ++ tailWord_844625) baseStart_844625 baseEnd_844625 := by
    simpa [prefixWord, tailWord_844625, baseEnd_844625] using wordTrace_append hprefix tailTrace_844625
  have hstable : (prefixWord ++ tailWord_844625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844625).length < 2 ^ (prefixWord ++ tailWord_844625).sum := by decide
  have hdescent : baseEnd_844625 < baseStart_844625 := by decide
  rcases family_descends (prefixWord ++ tailWord_844625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844644 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_844644 : Nat := 118140960795 + 844644 * 2 ^ 59
def prefixEnd_844644 : Nat := 4983230072969 + 3 ^ 40 * 844644 * 2
def baseEnd_844644 : Nat := 433708353936298560165559

theorem tailTrace_844644 : CollatzResearch.WordTrace tailWord_844644 prefixEnd_844644 433708353936298560165559 := by
  unfold tailWord_844644
  simp only [CollatzResearch.WordTrace]
  refine ⟨15403348776003258277842493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20537798368004344370456657 15403348776003258277842493)
  ·
    refine ⟨5776255791001221854190935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15403348776003258277842493 5776255791001221854190935)
    ·
      refine ⟨8664383686501832781286403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776255791001221854190935 8664383686501832781286403)
      ·
        refine ⟨12996575529752749171929605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664383686501832781286403 12996575529752749171929605)
        ·
          refine ⟨2436857911828640469736801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12996575529752749171929605 2436857911828640469736801)
          ·
            refine ⟨1827643433871480352302601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436857911828640469736801 1827643433871480352302601)
            ·
              refine ⟨1370732575403610264226951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827643433871480352302601 1370732575403610264226951)
              ·
                refine ⟨2056098863105415396340427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370732575403610264226951 2056098863105415396340427)
                ·
                  refine ⟨3084148294658123094510641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056098863105415396340427 3084148294658123094510641)
                  ·
                    refine ⟨2313111220993592320882981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084148294658123094510641 2313111220993592320882981)
                    ·
                      refine ⟨433708353936298560165559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2313111220993592320882981 433708353936298560165559)
                      ·
                        rfl

theorem cell23_844644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_844644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844644 prefixEnd_844644 := by exact prefixLift 844644
  have htrace : WordTrace (prefixWord ++ tailWord_844644) baseStart_844644 baseEnd_844644 := by
    simpa [prefixWord, tailWord_844644, baseEnd_844644] using wordTrace_append hprefix tailTrace_844644
  have hstable : (prefixWord ++ tailWord_844644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844644).length < 2 ^ (prefixWord ++ tailWord_844644).sum := by decide
  have hdescent : baseEnd_844644 < baseStart_844644 := by decide
  rcases family_descends (prefixWord ++ tailWord_844644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844681 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_844681 : Nat := 118140960795 + 844681 * 2 ^ 59
def prefixEnd_844681 : Nat := 4983230072969 + 3 ^ 40 * 844681 * 2
def baseEnd_844681 : Nat := 433727352720514915402889

theorem tailTrace_844681 : CollatzResearch.WordTrace tailWord_844681 prefixEnd_844681 433727352720514915402889 := by
  unfold tailWord_844681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30808047052872471874781897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20538698035248314583187931 30808047052872471874781897)
  ·
    refine ⟨23106035289654353906086423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30808047052872471874781897 23106035289654353906086423)
    ·
      refine ⟨34659052934481530859129635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23106035289654353906086423 34659052934481530859129635)
      ·
        refine ⟨51988579401722296288694453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34659052934481530859129635 51988579401722296288694453)
        ·
          refine ⟨4873929318911465277065105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51988579401722296288694453 4873929318911465277065105)
          ·
            refine ⟨3655446989183598957798829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873929318911465277065105 3655446989183598957798829)
            ·
              refine ⟨1370792620943849609174561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3655446989183598957798829 1370792620943849609174561)
              ·
                refine ⟨1028094465707887206880921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370792620943849609174561 1028094465707887206880921)
                ·
                  refine ⟨771070849280915405160691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028094465707887206880921 771070849280915405160691)
                  ·
                    refine ⟨1156606273921373107741037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771070849280915405160691 1156606273921373107741037)
                    ·
                      refine ⟨433727352720514915402889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156606273921373107741037 433727352720514915402889)
                      ·
                        rfl

theorem cell23_844681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_844681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844681 prefixEnd_844681 := by exact prefixLift 844681
  have htrace : WordTrace (prefixWord ++ tailWord_844681) baseStart_844681 baseEnd_844681 := by
    simpa [prefixWord, tailWord_844681, baseEnd_844681] using wordTrace_append hprefix tailTrace_844681
  have hstable : (prefixWord ++ tailWord_844681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844681).length < 2 ^ (prefixWord ++ tailWord_844681).sum := by decide
  have hdescent : baseEnd_844681 < baseStart_844681 := by decide
  rcases family_descends (prefixWord ++ tailWord_844681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844698 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_844698 : Nat := 118140960795 + 844698 * 2 ^ 59
def prefixEnd_844698 : Nat := 4983230072969 + 3 ^ 40 * 844698 * 2
def baseEnd_844698 : Nat := 433736081891641348890311

theorem tailTrace_844698 : CollatzResearch.WordTrace tailWord_844698 prefixEnd_844698 433736081891641348890311 := by
  unfold tailWord_844698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702166773452720944537687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20539111395873922518767165 7702166773452720944537687)
  ·
    refine ⟨11553250160179081416806531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702166773452720944537687 11553250160179081416806531)
    ·
      refine ⟨17329875240268622125209797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11553250160179081416806531 17329875240268622125209797)
      ·
        refine ⟨3249351607550366648476837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17329875240268622125209797 3249351607550366648476837)
        ·
          refine ⟨609253426415693746589407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3249351607550366648476837 609253426415693746589407)
          ·
            refine ⟨913880139623540619884111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609253426415693746589407 913880139623540619884111)
            ·
              refine ⟨1370820209435310929826167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913880139623540619884111 1370820209435310929826167)
              ·
                refine ⟨2056230314152966394739251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370820209435310929826167 2056230314152966394739251)
                ·
                  refine ⟨3084345471229449592108877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056230314152966394739251 3084345471229449592108877)
                  ·
                    refine ⟨1156629551711043597040829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3084345471229449592108877 1156629551711043597040829)
                    ·
                      refine ⟨433736081891641348890311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156629551711043597040829 433736081891641348890311)
                      ·
                        rfl

theorem cell23_844698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_844698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844698 prefixEnd_844698 := by exact prefixLift 844698
  have htrace : WordTrace (prefixWord ++ tailWord_844698) baseStart_844698 baseEnd_844698 := by
    simpa [prefixWord, tailWord_844698, baseEnd_844698] using wordTrace_append hprefix tailTrace_844698
  have hstable : (prefixWord ++ tailWord_844698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844698).length < 2 ^ (prefixWord ++ tailWord_844698).sum := by decide
  have hdescent : baseEnd_844698 < baseStart_844698 := by decide
  rcases family_descends (prefixWord ++ tailWord_844698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844707 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3]
def baseStart_844707 : Nat := 118140960795 + 844707 * 2 ^ 59
def prefixEnd_844707 : Nat := 4983230072969 + 3 ^ 40 * 844707 * 2
def baseEnd_844707 : Nat := 433740703217531813677769

theorem tailTrace_844707 : CollatzResearch.WordTrace tailWord_844707 prefixEnd_844707 433740703217531813677769 := by
  unfold tailWord_844707
  simp only [CollatzResearch.WordTrace]
  refine ⟨30808995350778278315228375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20539330233852185543485583 30808995350778278315228375)
  ·
    refine ⟨46213493026167417472842563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30808995350778278315228375 46213493026167417472842563)
    ·
      refine ⟨69320239539251126209263845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46213493026167417472842563 69320239539251126209263845)
      ·
        refine ⟨12997544913609586164236971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69320239539251126209263845 12997544913609586164236971)
        ·
          refine ⟨19496317370414379246355457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12997544913609586164236971 19496317370414379246355457)
          ·
            refine ⟨14622238027810784434766593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19496317370414379246355457 14622238027810784434766593)
            ·
              refine ⟨10966678520858088326074945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14622238027810784434766593 10966678520858088326074945)
              ·
                refine ⟨8225008890643566244556209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10966678520858088326074945 8225008890643566244556209)
                ·
                  refine ⟨6168756667982674683417157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8225008890643566244556209 6168756667982674683417157)
                  ·
                    refine ⟨1156641875246751503140717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168756667982674683417157 1156641875246751503140717)
                    ·
                      refine ⟨433740703217531813677769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156641875246751503140717 433740703217531813677769)
                      ·
                        rfl

theorem cell23_844707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_844707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844707 prefixEnd_844707 := by exact prefixLift 844707
  have htrace : WordTrace (prefixWord ++ tailWord_844707) baseStart_844707 baseEnd_844707 := by
    simpa [prefixWord, tailWord_844707, baseEnd_844707] using wordTrace_append hprefix tailTrace_844707
  have hstable : (prefixWord ++ tailWord_844707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844707).length < 2 ^ (prefixWord ++ tailWord_844707).sum := by decide
  have hdescent : baseEnd_844707 < baseStart_844707 := by decide
  rcases family_descends (prefixWord ++ tailWord_844707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844794 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_844794 : Nat := 118140960795 + 844794 * 2 ^ 59
def prefixEnd_844794 : Nat := 4983230072969 + 3 ^ 40 * 844794 * 2
def baseEnd_844794 : Nat := 433785376034472973289869

theorem tailTrace_844794 : CollatzResearch.WordTrace tailWord_844794 prefixEnd_844794 433785376034472973289869 := by
  unfold tailWord_844794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703042125365773043411359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20541445667642061449096957 7703042125365773043411359)
  ·
    refine ⟨11554563188048659565117039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703042125365773043411359 11554563188048659565117039)
    ·
      refine ⟨17331844782072989347675559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554563188048659565117039 17331844782072989347675559)
      ·
        refine ⟨25997767173109484021513339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331844782072989347675559 25997767173109484021513339)
        ·
          refine ⟨38996650759664226032270009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25997767173109484021513339 38996650759664226032270009)
          ·
            refine ⟨29247488069748169524202507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38996650759664226032270009 29247488069748169524202507)
            ·
              refine ⟨43871232104622254286303761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29247488069748169524202507 43871232104622254286303761)
              ·
                refine ⟨32903424078466690714727821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43871232104622254286303761 32903424078466690714727821)
                ·
                  refine ⟨12338784029425009018022933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32903424078466690714727821 12338784029425009018022933)
                  ·
                    refine ⟨578380501379297297719825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12338784029425009018022933 578380501379297297719825)
                    ·
                      refine ⟨433785376034472973289869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578380501379297297719825 433785376034472973289869)
                      ·
                        rfl

theorem cell23_844794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_844794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844794 prefixEnd_844794 := by exact prefixLift 844794
  have htrace : WordTrace (prefixWord ++ tailWord_844794) baseStart_844794 baseEnd_844794 := by
    simpa [prefixWord, tailWord_844794, baseEnd_844794] using wordTrace_append hprefix tailTrace_844794
  have hstable : (prefixWord ++ tailWord_844794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844794).length < 2 ^ (prefixWord ++ tailWord_844794).sum := by decide
  have hdescent : baseEnd_844794 < baseStart_844794 := by decide
  rcases family_descends (prefixWord ++ tailWord_844794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844797 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_844797 : Nat := 118140960795 + 844797 * 2 ^ 59
def prefixEnd_844797 : Nat := 4983230072969 + 3 ^ 40 * 844797 * 2
def baseEnd_844797 : Nat := 433786916476436461552355

theorem tailTrace_844797 : CollatzResearch.WordTrace tailWord_844797 prefixEnd_844797 433786916476436461552355 := by
  unfold tailWord_844797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30812277920452223686004645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20541518613634815790669763 30812277920452223686004645)
  ·
    refine ⟨5777302110084791941125871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30812277920452223686004645 5777302110084791941125871)
    ·
      refine ⟨8665953165127187911688807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777302110084791941125871 8665953165127187911688807)
      ·
        refine ⟨12998929747690781867533211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8665953165127187911688807 12998929747690781867533211)
        ·
          refine ⟨19498394621536172801299817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12998929747690781867533211 19498394621536172801299817)
          ·
            refine ⟨14623795966152129600974863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19498394621536172801299817 14623795966152129600974863)
            ·
              refine ⟨21935693949228194401462295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14623795966152129600974863 21935693949228194401462295)
              ·
                refine ⟨32903540923842291602193443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21935693949228194401462295 32903540923842291602193443)
                ·
                  refine ⟨49355311385763437403290165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32903540923842291602193443 49355311385763437403290165)
                  ·
                    refine ⟨4627060442415322256558453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49355311385763437403290165 4627060442415322256558453)
                    ·
                      refine ⟨433786916476436461552355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4627060442415322256558453 433786916476436461552355)
                      ·
                        rfl

theorem cell23_844797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_844797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844797 prefixEnd_844797 := by exact prefixLift 844797
  have htrace : WordTrace (prefixWord ++ tailWord_844797) baseStart_844797 baseEnd_844797 := by
    simpa [prefixWord, tailWord_844797, baseEnd_844797] using wordTrace_append hprefix tailTrace_844797
  have hstable : (prefixWord ++ tailWord_844797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844797).length < 2 ^ (prefixWord ++ tailWord_844797).sum := by decide
  have hdescent : baseEnd_844797 < baseStart_844797 := by decide
  rcases family_descends (prefixWord ++ tailWord_844797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844811 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 4, 2]
def baseStart_844811 : Nat := 118140960795 + 844811 * 2 ^ 59
def prefixEnd_844811 : Nat := 4983230072969 + 3 ^ 40 * 844811 * 2
def baseEnd_844811 : Nat := 433794105205599406777291

theorem tailTrace_844811 : CollatzResearch.WordTrace tailWord_844811 prefixEnd_844811 433794105205599406777291 := by
  unfold tailWord_844811
  simp only [CollatzResearch.WordTrace]
  refine ⟨30812788542401504077014287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20541859028267669384676191 30812788542401504077014287)
  ·
    refine ⟨46219182813602256115521431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30812788542401504077014287 46219182813602256115521431)
    ·
      refine ⟨69328774220403384173282147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46219182813602256115521431 69328774220403384173282147)
      ·
        refine ⟨103993161330605076259923221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69328774220403384173282147 103993161330605076259923221)
        ·
          refine ⟨4874679437372112949683901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103993161330605076259923221 4874679437372112949683901)
          ·
            refine ⟨1828004789014542356131463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4874679437372112949683901 1828004789014542356131463)
            ·
              refine ⟨2742007183521813534197195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828004789014542356131463 2742007183521813534197195)
              ·
                refine ⟨4113010775282720301295793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742007183521813534197195 4113010775282720301295793)
                ·
                  refine ⟨3084758081462040225971845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113010775282720301295793 3084758081462040225971845)
                  ·
                    refine ⟨578392140274132542369721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084758081462040225971845 578392140274132542369721)
                    ·
                      refine ⟨433794105205599406777291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578392140274132542369721 433794105205599406777291)
                      ·
                        rfl

theorem cell23_844811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 4, 2].length) (baseStart_844811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844811 prefixEnd_844811 := by exact prefixLift 844811
  have htrace : WordTrace (prefixWord ++ tailWord_844811) baseStart_844811 baseEnd_844811 := by
    simpa [prefixWord, tailWord_844811, baseEnd_844811] using wordTrace_append hprefix tailTrace_844811
  have hstable : (prefixWord ++ tailWord_844811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844811).length < 2 ^ (prefixWord ++ tailWord_844811).sum := by decide
  have hdescent : baseEnd_844811 < baseStart_844811 := by decide
  rcases family_descends (prefixWord ++ tailWord_844811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844821 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_844821 : Nat := 118140960795 + 844821 * 2 ^ 59
def prefixEnd_844821 : Nat := 4983230072969 + 3 ^ 40 * 844821 * 2
def baseEnd_844821 : Nat := 144599746670714789217415

theorem tailTrace_844821 : CollatzResearch.WordTrace tailWord_844821 prefixEnd_844821 144599746670714789217415 := by
  unfold tailWord_844821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813153272365275784878317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20542102181576850523252211 30813153272365275784878317)
  ·
    refine ⟨11554932477136978419329369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30813153272365275784878317 11554932477136978419329369)
    ·
      refine ⟨8666199357852733814497027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11554932477136978419329369 8666199357852733814497027)
      ·
        refine ⟨12999299036779100721745541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666199357852733814497027 12999299036779100721745541)
        ·
          refine ⟨2437368569396081385327289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12999299036779100721745541 2437368569396081385327289)
          ·
            refine ⟨1828026427047061038995467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437368569396081385327289 1828026427047061038995467)
            ·
              refine ⟨2742039640570591558493201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828026427047061038995467 2742039640570591558493201)
              ·
                refine ⟨2056529730427943668869901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742039640570591558493201 2056529730427943668869901)
                ·
                  refine ⟨771198648910478875826213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2056529730427943668869901 771198648910478875826213)
                  ·
                    refine ⟨144599746670714789217415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771198648910478875826213 144599746670714789217415)
                    ·
                      rfl

theorem cell23_844821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_844821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844821 prefixEnd_844821 := by exact prefixLift 844821
  have htrace : WordTrace (prefixWord ++ tailWord_844821) baseStart_844821 baseEnd_844821 := by
    simpa [prefixWord, tailWord_844821, baseEnd_844821] using wordTrace_append hprefix tailTrace_844821
  have hstable : (prefixWord ++ tailWord_844821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844821).length < 2 ^ (prefixWord ++ tailWord_844821).sum := by decide
  have hdescent : baseEnd_844821 < baseStart_844821 := by decide
  rcases family_descends (prefixWord ++ tailWord_844821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844828 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_844828 : Nat := 118140960795 + 844828 * 2 ^ 59
def prefixEnd_844828 : Nat := 4983230072969 + 3 ^ 40 * 844828 * 2
def baseEnd_844828 : Nat := 433802834376725840264713

theorem tailTrace_844828 : CollatzResearch.WordTrace tailWord_844828 prefixEnd_844828 433802834376725840264713 := by
  unfold tailWord_844828
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406704291669957990191569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20542272388893277320255425 15406704291669957990191569)
  ·
    refine ⟨11555028218752468492643677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15406704291669957990191569 11555028218752468492643677)
    ·
      refine ⟨4333135582032175684741379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11555028218752468492643677 4333135582032175684741379)
      ·
        refine ⟨6499703373048263527112069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333135582032175684741379 6499703373048263527112069)
        ·
          refine ⟨1218694382446549411333513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6499703373048263527112069 1218694382446549411333513)
          ·
            refine ⟨914020786834912058500135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218694382446549411333513 914020786834912058500135)
            ·
              refine ⟨1371031180252368087750203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914020786834912058500135 1371031180252368087750203)
              ·
                refine ⟨2056546770378552131625305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371031180252368087750203 2056546770378552131625305)
                ·
                  refine ⟨1542410077783914098718979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056546770378552131625305 1542410077783914098718979)
                  ·
                    refine ⟨2313615116675871148078469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1542410077783914098718979 2313615116675871148078469)
                    ·
                      refine ⟨433802834376725840264713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2313615116675871148078469 433802834376725840264713)
                      ·
                        rfl

theorem cell23_844828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_844828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844828 prefixEnd_844828 := by exact prefixLift 844828
  have htrace : WordTrace (prefixWord ++ tailWord_844828) baseStart_844828 baseEnd_844828 := by
    simpa [prefixWord, tailWord_844828, baseEnd_844828] using wordTrace_append hprefix tailTrace_844828
  have hstable : (prefixWord ++ tailWord_844828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844828).length < 2 ^ (prefixWord ++ tailWord_844828).sum := by decide
  have hdescent : baseEnd_844828 < baseStart_844828 := by decide
  rcases family_descends (prefixWord ++ tailWord_844828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844831 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_844831 : Nat := 118140960795 + 844831 * 2 ^ 59
def prefixEnd_844831 : Nat := 4983230072969 + 3 ^ 40 * 844831 * 2
def baseEnd_844831 : Nat := 433804374818689328527199

theorem tailTrace_844831 : CollatzResearch.WordTrace tailWord_844831 prefixEnd_844831 433804374818689328527199 := by
  unfold tailWord_844831
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813518002329047492742347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20542345334886031661828231 30813518002329047492742347)
  ·
    refine ⟨46220277003493571239113521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30813518002329047492742347 46220277003493571239113521)
    ·
      refine ⟨34665207752620178429335141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46220277003493571239113521 34665207752620178429335141)
      ·
        refine ⟨6499726453616283455500339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34665207752620178429335141 6499726453616283455500339)
        ·
          refine ⟨9749589680424425183250509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499726453616283455500339 9749589680424425183250509)
          ·
            refine ⟨3656096130159159443718941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9749589680424425183250509 3656096130159159443718941)
            ·
              refine ⟨1371036048809684791394603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3656096130159159443718941 1371036048809684791394603)
              ·
                refine ⟨2056554073214527187091905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371036048809684791394603 2056554073214527187091905)
                ·
                  refine ⟨1542415554910895390318929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056554073214527187091905 1542415554910895390318929)
                  ·
                    refine ⟨1156811666183171542739197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542415554910895390318929 1156811666183171542739197)
                    ·
                      refine ⟨433804374818689328527199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156811666183171542739197 433804374818689328527199)
                      ·
                        rfl

theorem cell23_844831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_844831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844831 prefixEnd_844831 := by exact prefixLift 844831
  have htrace : WordTrace (prefixWord ++ tailWord_844831) baseStart_844831 baseEnd_844831 := by
    simpa [prefixWord, tailWord_844831, baseEnd_844831] using wordTrace_append hprefix tailTrace_844831
  have hstable : (prefixWord ++ tailWord_844831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844831).length < 2 ^ (prefixWord ++ tailWord_844831).sum := by decide
  have hdescent : baseEnd_844831 < baseStart_844831 := by decide
  rcases family_descends (prefixWord ++ tailWord_844831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844871 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_844871 : Nat := 118140960795 + 844871 * 2 ^ 59
def prefixEnd_844871 : Nat := 4983230072969 + 3 ^ 40 * 844871 * 2
def baseEnd_844871 : Nat := 433824914044869172027015

theorem tailTrace_844871 : CollatzResearch.WordTrace tailWord_844871 prefixEnd_844871 433824914044869172027015 := by
  unfold tailWord_844871
  simp only [CollatzResearch.WordTrace]
  refine ⟨30814976922184134324198467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20543317948122756216132311 30814976922184134324198467)
  ·
    refine ⟨46222465383276201486297701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30814976922184134324198467 46222465383276201486297701)
    ·
      refine ⟨8666712259364287778680819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46222465383276201486297701 8666712259364287778680819)
      ·
        refine ⟨13000068389046431668021229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666712259364287778680819 13000068389046431668021229)
        ·
          refine ⟨4875025645892411875507961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13000068389046431668021229 4875025645892411875507961)
          ·
            refine ⟨3656269234419308906630971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4875025645892411875507961 3656269234419308906630971)
            ·
              refine ⟨5484403851628963359946457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656269234419308906630971 5484403851628963359946457)
              ·
                refine ⟨4113302888721722519959843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5484403851628963359946457 4113302888721722519959843)
                ·
                  refine ⟨6169954333082583779939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113302888721722519959843 6169954333082583779939765)
                  ·
                    refine ⟨578433218726492229369353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6169954333082583779939765 578433218726492229369353)
                    ·
                      refine ⟨433824914044869172027015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578433218726492229369353 433824914044869172027015)
                      ·
                        rfl

theorem cell23_844871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_844871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844871 prefixEnd_844871 := by exact prefixLift 844871
  have htrace : WordTrace (prefixWord ++ tailWord_844871) baseStart_844871 baseEnd_844871 := by
    simpa [prefixWord, tailWord_844871, baseEnd_844871] using wordTrace_append hprefix tailTrace_844871
  have hstable : (prefixWord ++ tailWord_844871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844871).length < 2 ^ (prefixWord ++ tailWord_844871).sum := by decide
  have hdescent : baseEnd_844871 < baseStart_844871 := by decide
  rcases family_descends (prefixWord ++ tailWord_844871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844898 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_844898 : Nat := 118140960795 + 844898 * 2 ^ 59
def prefixEnd_844898 : Nat := 4983230072969 + 3 ^ 40 * 844898 * 2
def baseEnd_844898 : Nat := 144612926007513522129797

theorem tailTrace_844898 : CollatzResearch.WordTrace tailWord_844898 prefixEnd_844898 144612926007513522129797 := by
  unfold tailWord_844898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703990423271579483857837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20543974462057545290287565 7703990423271579483857837)
  ·
    refine ⟨2888996408726842306446689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7703990423271579483857837 2888996408726842306446689)
    ·
      refine ⟨2166747306545131729835017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2888996408726842306446689 2166747306545131729835017)
      ·
        refine ⟨1625060479908848797376263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166747306545131729835017 1625060479908848797376263)
        ·
          refine ⟨2437590719863273196064395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625060479908848797376263 2437590719863273196064395)
          ·
            refine ⟨3656386079794909794096593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437590719863273196064395 3656386079794909794096593)
            ·
              refine ⟨2742289559846182345572445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656386079794909794096593 2742289559846182345572445)
              ·
                refine ⟨1028358584942318379589667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742289559846182345572445 1028358584942318379589667)
                ·
                  refine ⟨1542537877413477569384501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028358584942318379589667 1542537877413477569384501)
                  ·
                    refine ⟨144612926007513522129797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1542537877413477569384501 144612926007513522129797)
                    ·
                      rfl

theorem cell23_844898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_844898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844898 prefixEnd_844898 := by exact prefixLift 844898
  have htrace : WordTrace (prefixWord ++ tailWord_844898) baseStart_844898 baseEnd_844898 := by
    simpa [prefixWord, tailWord_844898, baseEnd_844898] using wordTrace_append hprefix tailTrace_844898
  have hstable : (prefixWord ++ tailWord_844898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844898).length < 2 ^ (prefixWord ++ tailWord_844898).sum := by decide
  have hdescent : baseEnd_844898 < baseStart_844898 := by decide
  rcases family_descends (prefixWord ++ tailWord_844898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844901 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_844901 : Nat := 118140960795 + 844901 * 2 ^ 59
def prefixEnd_844901 : Nat := 4983230072969 + 3 ^ 40 * 844901 * 2
def baseEnd_844901 : Nat := 433840318464504054651877

theorem tailTrace_844901 : CollatzResearch.WordTrace tailWord_844901 prefixEnd_844901 433840318464504054651877 := by
  unfold tailWord_844901
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816071112075449447790557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20544047408050299631860371 30816071112075449447790557)
  ·
    refine ⟨11556026667028293542921459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30816071112075449447790557 11556026667028293542921459)
    ·
      refine ⟨17334040000542440314382189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11556026667028293542921459 17334040000542440314382189)
      ·
        refine ⟨6500265000203415117893321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17334040000542440314382189 6500265000203415117893321)
        ·
          refine ⟨4875198750152561338419991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6500265000203415117893321 4875198750152561338419991)
          ·
            refine ⟨7312798125228842007629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875198750152561338419991 7312798125228842007629987)
            ·
              refine ⟨10969197187843263011444981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312798125228842007629987 10969197187843263011444981)
              ·
                refine ⟨1028362236360305907322967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10969197187843263011444981 1028362236360305907322967)
                ·
                  refine ⟨1542543354540458860984451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028362236360305907322967 1542543354540458860984451)
                  ·
                    refine ⟨2313815031810688291476677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1542543354540458860984451 2313815031810688291476677)
                    ·
                      refine ⟨433840318464504054651877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2313815031810688291476677 433840318464504054651877)
                      ·
                        rfl

theorem cell23_844901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_844901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844901 prefixEnd_844901 := by exact prefixLift 844901
  have htrace : WordTrace (prefixWord ++ tailWord_844901) baseStart_844901 baseEnd_844901 := by
    simpa [prefixWord, tailWord_844901, baseEnd_844901] using wordTrace_append hprefix tailTrace_844901
  have hstable : (prefixWord ++ tailWord_844901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844901).length < 2 ^ (prefixWord ++ tailWord_844901).sum := by decide
  have hdescent : baseEnd_844901 < baseStart_844901 := by decide
  rcases family_descends (prefixWord ++ tailWord_844901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844911 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 2, 4]
def baseStart_844911 : Nat := 118140960795 + 844911 * 2 ^ 59
def prefixEnd_844911 : Nat := 4983230072969 + 3 ^ 40 * 844911 * 2
def baseEnd_844911 : Nat := 144615151090349671842277

theorem tailTrace_844911 : CollatzResearch.WordTrace tailWord_844911 prefixEnd_844911 144615151090349671842277 := by
  unfold tailWord_844911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816435842039221155654587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20544290561359480770436391 30816435842039221155654587)
  ·
    refine ⟨46224653763058831733481881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30816435842039221155654587 46224653763058831733481881)
    ·
      refine ⟨34668490322294123800111411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46224653763058831733481881 34668490322294123800111411)
      ·
        refine ⟨52002735483441185700167117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34668490322294123800111411 52002735483441185700167117)
        ·
          refine ⟨19501025806290444637562669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52002735483441185700167117 19501025806290444637562669)
          ·
            refine ⟨7312884677358916739086001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19501025806290444637562669 7312884677358916739086001)
            ·
              refine ⟨5484663508019187554314501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312884677358916739086001 5484663508019187554314501)
              ·
                refine ⟨1028374407753597666433969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5484663508019187554314501 1028374407753597666433969)
                ·
                  refine ⟨771280805815198249825477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028374407753597666433969 771280805815198249825477)
                  ·
                    refine ⟨144615151090349671842277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771280805815198249825477 144615151090349671842277)
                    ·
                      rfl

theorem cell23_844911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_844911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844911 prefixEnd_844911 := by exact prefixLift 844911
  have htrace : WordTrace (prefixWord ++ tailWord_844911) baseStart_844911 baseEnd_844911 := by
    simpa [prefixWord, tailWord_844911, baseEnd_844911] using wordTrace_append hprefix tailTrace_844911
  have hstable : (prefixWord ++ tailWord_844911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844911).length < 2 ^ (prefixWord ++ tailWord_844911).sum := by decide
  have hdescent : baseEnd_844911 < baseStart_844911 := by decide
  rcases family_descends (prefixWord ++ tailWord_844911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844914 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_844914 : Nat := 118140960795 + 844914 * 2 ^ 59
def prefixEnd_844914 : Nat := 4983230072969 + 3 ^ 40 * 844914 * 2
def baseEnd_844914 : Nat := 433846993713012503789317

theorem tailTrace_844914 : CollatzResearch.WordTrace tailWord_844914 prefixEnd_844914 433846993713012503789317 := by
  unfold tailWord_844914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704136315257088167003449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20544363507352235112009197 7704136315257088167003449)
  ·
    refine ⟨5778102236442816125252587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7704136315257088167003449 5778102236442816125252587)
    ·
      refine ⟨8667153354664224187878881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778102236442816125252587 8667153354664224187878881)
      ·
        refine ⟨6500365015998168140909161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8667153354664224187878881 6500365015998168140909161)
        ·
          refine ⟨4875273761998626105681871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6500365015998168140909161 4875273761998626105681871)
          ·
            refine ⟨7312910642997939158522807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875273761998626105681871 7312910642997939158522807)
            ·
              refine ⟨10969365964496908737784211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312910642997939158522807 10969365964496908737784211)
              ·
                refine ⟨16454048946745363106676317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10969365964496908737784211 16454048946745363106676317)
                ·
                  refine ⟨6170268355029511165003619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16454048946745363106676317 6170268355029511165003619)
                  ·
                    refine ⟨9255402532544266747505429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170268355029511165003619 9255402532544266747505429)
                    ·
                      refine ⟨433846993713012503789317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9255402532544266747505429 433846993713012503789317)
                      ·
                        rfl

theorem cell23_844914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_844914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844914 prefixEnd_844914 := by exact prefixLift 844914
  have htrace : WordTrace (prefixWord ++ tailWord_844914) baseStart_844914 baseEnd_844914 := by
    simpa [prefixWord, tailWord_844914, baseEnd_844914] using wordTrace_append hprefix tailTrace_844914
  have hstable : (prefixWord ++ tailWord_844914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844914).length < 2 ^ (prefixWord ++ tailWord_844914).sum := by decide
  have hdescent : baseEnd_844914 < baseStart_844914 := by decide
  rcases family_descends (prefixWord ++ tailWord_844914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844924 : List Nat := [2, 2, 2, 1, 1, 3, 4, 8]
def baseStart_844924 : Nat := 118140960795 + 844924 * 2 ^ 59
def prefixEnd_844924 : Nat := 4983230072969 + 3 ^ 40 * 844924 * 2
def baseEnd_844924 : Nat := 16068597352576202394973

theorem tailTrace_844924 : CollatzResearch.WordTrace tailWord_844924 prefixEnd_844924 16068597352576202394973 := by
  unfold tailWord_844924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408454995496062187938913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20544606660661416250585217 15408454995496062187938913)
  ·
    refine ⟨11556341246622046640954185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15408454995496062187938913 11556341246622046640954185)
    ·
      refine ⟨8667255934966534980715639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11556341246622046640954185 8667255934966534980715639)
      ·
        refine ⟨13000883902449802471073459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667255934966534980715639 13000883902449802471073459)
        ·
          refine ⟨19501325853674703706610189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13000883902449802471073459 19501325853674703706610189)
          ·
            refine ⟨7312997195128013889978821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19501325853674703706610189 7312997195128013889978821)
            ·
              refine ⟨1371186974086502604371029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7312997195128013889978821 1371186974086502604371029)
              ·
                refine ⟨16068597352576202394973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1371186974086502604371029 16068597352576202394973)
                ·
                  rfl

theorem cell23_844924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 8].length) (baseStart_844924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844924 prefixEnd_844924 := by exact prefixLift 844924
  have htrace : WordTrace (prefixWord ++ tailWord_844924) baseStart_844924 baseEnd_844924 := by
    simpa [prefixWord, tailWord_844924, baseEnd_844924] using wordTrace_append hprefix tailTrace_844924
  have hstable : (prefixWord ++ tailWord_844924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844924).length < 2 ^ (prefixWord ++ tailWord_844924).sum := by decide
  have hdescent : baseEnd_844924 < baseStart_844924 := by decide
  rcases family_descends (prefixWord ++ tailWord_844924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844928 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_844928 : Nat := 118140960795 + 844928 * 2 ^ 59
def prefixEnd_844928 : Nat := 4983230072969 + 3 ^ 40 * 844928 * 2
def baseEnd_844928 : Nat := 144618060814058483004751

theorem tailTrace_844928 : CollatzResearch.WordTrace tailWord_844928 prefixEnd_844928 144618060814058483004751 := by
  unfold tailWord_844928
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408527941488816529511719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20544703921985088706015625 15408527941488816529511719)
  ·
    refine ⟨23112791912233224794267579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15408527941488816529511719 23112791912233224794267579)
    ·
      refine ⟨34669187868349837191401369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112791912233224794267579 34669187868349837191401369)
      ·
        refine ⟨26001890901262377893551027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34669187868349837191401369 26001890901262377893551027)
        ·
          refine ⟨39002836351893566840326541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26001890901262377893551027 39002836351893566840326541)
          ·
            refine ⟨14626063631960087565122453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39002836351893566840326541 14626063631960087565122453)
            ·
              refine ⟨685596732748129104615115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14626063631960087565122453 685596732748129104615115)
              ·
                refine ⟨1028395099122193656922673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685596732748129104615115 1028395099122193656922673)
                ·
                  refine ⟨771296324341645242692005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028395099122193656922673 771296324341645242692005)
                  ·
                    refine ⟨144618060814058483004751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771296324341645242692005 144618060814058483004751)
                    ·
                      rfl

theorem cell23_844928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_844928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844928 prefixEnd_844928 := by exact prefixLift 844928
  have htrace : WordTrace (prefixWord ++ tailWord_844928) baseStart_844928 baseEnd_844928 := by
    simpa [prefixWord, tailWord_844928, baseEnd_844928] using wordTrace_append hprefix tailTrace_844928
  have hstable : (prefixWord ++ tailWord_844928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844928).length < 2 ^ (prefixWord ++ tailWord_844928).sum := by decide
  have hdescent : baseEnd_844928 < baseStart_844928 := by decide
  rcases family_descends (prefixWord ++ tailWord_844928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844951 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_844951 : Nat := 118140960795 + 844951 * 2 ^ 59
def prefixEnd_844951 : Nat := 4983230072969 + 3 ^ 40 * 844951 * 2
def baseEnd_844951 : Nat := 433865992497228859026647

theorem tailTrace_844951 : CollatzResearch.WordTrace tailWord_844951 prefixEnd_844951 433865992497228859026647 := by
  unfold tailWord_844951
  simp only [CollatzResearch.WordTrace]
  refine ⟨30817894761894307987110707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20545263174596205324740471 30817894761894307987110707)
  ·
    refine ⟨46226842142841461980666061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30817894761894307987110707 46226842142841461980666061)
    ·
      refine ⟨17335065803565548242749773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46226842142841461980666061 17335065803565548242749773)
      ·
        refine ⟨6500649676337080591031165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17335065803565548242749773 6500649676337080591031165)
        ·
          refine ⟨2437743628626405221636687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6500649676337080591031165 2437743628626405221636687)
          ·
            refine ⟨3656615442939607832455031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437743628626405221636687 3656615442939607832455031)
            ·
              refine ⟨5484923164409411748682547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656615442939607832455031 5484923164409411748682547)
              ·
                refine ⟨8227384746614117623023821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484923164409411748682547 8227384746614117623023821)
                ·
                  refine ⟨3085269279980294108633933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8227384746614117623023821 3085269279980294108633933)
                  ·
                    refine ⟨1156975979992610290737725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085269279980294108633933 1156975979992610290737725)
                    ·
                      refine ⟨433865992497228859026647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1156975979992610290737725 433865992497228859026647)
                      ·
                        rfl

theorem cell23_844951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_844951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844951 prefixEnd_844951 := by exact prefixLift 844951
  have htrace : WordTrace (prefixWord ++ tailWord_844951) baseStart_844951 baseEnd_844951 := by
    simpa [prefixWord, tailWord_844951, baseEnd_844951] using wordTrace_append hprefix tailTrace_844951
  have hstable : (prefixWord ++ tailWord_844951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844951).length < 2 ^ (prefixWord ++ tailWord_844951).sum := by decide
  have hdescent : baseEnd_844951 < baseStart_844951 := by decide
  rcases family_descends (prefixWord ++ tailWord_844951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844978 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_844978 : Nat := 118140960795 + 844978 * 2 ^ 59
def prefixEnd_844978 : Nat := 4983230072969 + 3 ^ 40 * 844978 * 2
def baseEnd_844978 : Nat := 433879856474900253389023

theorem tailTrace_844978 : CollatzResearch.WordTrace tailWord_844978 prefixEnd_844978 433879856474900253389023 := by
  unfold tailWord_844978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704719883199122899585897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20545919688530994398895725 7704719883199122899585897)
  ·
    refine ⟨5778539912399342174689423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7704719883199122899585897 5778539912399342174689423)
    ·
      refine ⟨8667809868599013262034135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778539912399342174689423 8667809868599013262034135)
      ·
        refine ⟨13001714802898519893051203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667809868599013262034135 13001714802898519893051203)
        ·
          refine ⟨19502572204347779839576805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001714802898519893051203 19502572204347779839576805)
          ·
            refine ⟨3656732288315208719920651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19502572204347779839576805 3656732288315208719920651)
            ·
              refine ⟨5485098432472813079880977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656732288315208719920651 5485098432472813079880977)
              ·
                refine ⟨4113823824354609809910733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485098432472813079880977 4113823824354609809910733)
                ·
                  refine ⟨1542683934132978678716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4113823824354609809910733 1542683934132978678716525)
                  ·
                    refine ⟨578506475299867004518697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1542683934132978678716525 578506475299867004518697)
                    ·
                      refine ⟨433879856474900253389023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578506475299867004518697 433879856474900253389023)
                      ·
                        rfl

theorem cell23_844978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_844978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844978 prefixEnd_844978 := by exact prefixLift 844978
  have htrace : WordTrace (prefixWord ++ tailWord_844978) baseStart_844978 baseEnd_844978 := by
    simpa [prefixWord, tailWord_844978, baseEnd_844978] using wordTrace_append hprefix tailTrace_844978
  have hstable : (prefixWord ++ tailWord_844978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844978).length < 2 ^ (prefixWord ++ tailWord_844978).sum := by decide
  have hdescent : baseEnd_844978 < baseStart_844978 := by decide
  rcases family_descends (prefixWord ++ tailWord_844978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844982 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_844982 : Nat := 118140960795 + 844982 * 2 ^ 59
def prefixEnd_844982 : Nat := 4983230072969 + 3 ^ 40 * 844982 * 2
def baseEnd_844982 : Nat := 433881910397518237739005

theorem tailTrace_844982 : CollatzResearch.WordTrace tailWord_844982 prefixEnd_844982 433881910397518237739005 := by
  unfold tailWord_844982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926189089048875017593075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20546016949854666854326133 1926189089048875017593075)
  ·
    refine ⟨2889283633573312526389613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926189089048875017593075 2889283633573312526389613)
    ·
      refine ⟨1083481362589992197396105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2889283633573312526389613 1083481362589992197396105)
      ·
        refine ⟨812611021942494148047079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083481362589992197396105 812611021942494148047079)
        ·
          refine ⟨1218916532913741222070619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812611021942494148047079 1218916532913741222070619)
          ·
            refine ⟨1828374799370611833105929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218916532913741222070619 1828374799370611833105929)
            ·
              refine ⟨1371281099527958874829447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828374799370611833105929 1371281099527958874829447)
              ·
                refine ⟨2056921649291938312244171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371281099527958874829447 2056921649291938312244171)
                ·
                  refine ⟨3085382473937907468366257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056921649291938312244171 3085382473937907468366257)
                  ·
                    refine ⟨2314036855453430601274693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3085382473937907468366257 2314036855453430601274693)
                    ·
                      refine ⟨433881910397518237739005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2314036855453430601274693 433881910397518237739005)
                      ·
                        rfl

theorem cell23_844982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_844982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_844982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_844982 prefixEnd_844982 := by exact prefixLift 844982
  have htrace : WordTrace (prefixWord ++ tailWord_844982) baseStart_844982 baseEnd_844982 := by
    simpa [prefixWord, tailWord_844982, baseEnd_844982] using wordTrace_append hprefix tailTrace_844982
  have hstable : (prefixWord ++ tailWord_844982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844982).length < 2 ^ (prefixWord ++ tailWord_844982).sum := by decide
  have hdescent : baseEnd_844982 < baseStart_844982 := by decide
  rcases family_descends (prefixWord ++ tailWord_844982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845025 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_845025 : Nat := 118140960795 + 845025 * 2 ^ 59
def prefixEnd_845025 : Nat := 4983230072969 + 3 ^ 40 * 845025 * 2
def baseEnd_845025 : Nat := 433903990065661569501307

theorem tailTrace_845025 : CollatzResearch.WordTrace tailWord_845025 prefixEnd_845025 433903990065661569501307 := by
  unfold tailWord_845025
  simp only [CollatzResearch.WordTrace]
  refine ⟨30820593763626218625304529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20547062509084145750203019 30820593763626218625304529)
  ·
    refine ⟨23115445322719663968978397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30820593763626218625304529 23115445322719663968978397)
    ·
      refine ⟨8668291996019873988366899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23115445322719663968978397 8668291996019873988366899)
      ·
        refine ⟨13002437994029810982550349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668291996019873988366899 13002437994029810982550349)
        ·
          refine ⟨4875914247761179118456381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13002437994029810982550349 4875914247761179118456381)
          ·
            refine ⟨1828467842910442169421143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4875914247761179118456381 1828467842910442169421143)
            ·
              refine ⟨2742701764365663254131715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828467842910442169421143 2742701764365663254131715)
              ·
                refine ⟨4114052646548494881197573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742701764365663254131715 4114052646548494881197573)
                ·
                  refine ⟨771384871227842790224545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4114052646548494881197573 771384871227842790224545)
                  ·
                    refine ⟨578538653420882092668409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 771384871227842790224545 578538653420882092668409)
                    ·
                      refine ⟨433903990065661569501307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578538653420882092668409 433903990065661569501307)
                      ·
                        rfl

theorem cell23_845025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_845025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845025 prefixEnd_845025 := by exact prefixLift 845025
  have htrace : WordTrace (prefixWord ++ tailWord_845025) baseStart_845025 baseEnd_845025 := by
    simpa [prefixWord, tailWord_845025, baseEnd_845025] using wordTrace_append hprefix tailTrace_845025
  have hstable : (prefixWord ++ tailWord_845025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845025).length < 2 ^ (prefixWord ++ tailWord_845025).sum := by decide
  have hdescent : baseEnd_845025 < baseStart_845025 := by decide
  rcases family_descends (prefixWord ++ tailWord_845025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845042 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_845042 : Nat := 118140960795 + 845042 * 2 ^ 59
def prefixEnd_845042 : Nat := 4983230072969 + 3 ^ 40 * 845042 * 2
def baseEnd_845042 : Nat := 433912719236788002988729

theorem tailTrace_845042 : CollatzResearch.WordTrace tailWord_845042 prefixEnd_845042 433912719236788002988729 := by
  unfold tailWord_845042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705303451141157632168345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20547475869709753685782253 7705303451141157632168345)
  ·
    refine ⟨5778977588355868224126259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7705303451141157632168345 5778977588355868224126259)
    ·
      refine ⟨8668466382533802336189389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778977588355868224126259 8668466382533802336189389)
      ·
        refine ⟨3250674893450175876071021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8668466382533802336189389 3250674893450175876071021)
        ·
          refine ⟨1219003085043815953526633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3250674893450175876071021 1219003085043815953526633)
          ·
            refine ⟨914252313782861965144975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219003085043815953526633 914252313782861965144975)
            ·
              refine ⟨1371378470674292947717463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914252313782861965144975 1371378470674292947717463)
              ·
                refine ⟨2057067706011439421576195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371378470674292947717463 2057067706011439421576195)
                ·
                  refine ⟨3085601559017159132364293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057067706011439421576195 3085601559017159132364293)
                  ·
                    refine ⟨578550292315717337318305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085601559017159132364293 578550292315717337318305)
                    ·
                      refine ⟨433912719236788002988729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 578550292315717337318305 433912719236788002988729)
                      ·
                        rfl

theorem cell23_845042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_845042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845042 prefixEnd_845042 := by exact prefixLift 845042
  have htrace : WordTrace (prefixWord ++ tailWord_845042) baseStart_845042 baseEnd_845042 := by
    simpa [prefixWord, tailWord_845042, baseEnd_845042] using wordTrace_append hprefix tailTrace_845042
  have hstable : (prefixWord ++ tailWord_845042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845042).length < 2 ^ (prefixWord ++ tailWord_845042).sum := by decide
  have hdescent : baseEnd_845042 < baseStart_845042 := by decide
  rcases family_descends (prefixWord ++ tailWord_845042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845061 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_845061 : Nat := 118140960795 + 845061 * 2 ^ 59
def prefixEnd_845061 : Nat := 4983230072969 + 3 ^ 40 * 845061 * 2
def baseEnd_845061 : Nat := 144640825123074476217047

theorem tailTrace_845061 : CollatzResearch.WordTrace tailWord_845061 prefixEnd_845061 144640825123074476217047 := by
  unfold tailWord_845061
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821906791495796773615037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20547937860997197849076691 30821906791495796773615037)
  ·
    refine ⟨11558215046810923790105639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30821906791495796773615037 11558215046810923790105639)
    ·
      refine ⟨17337322570216385685158459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11558215046810923790105639 17337322570216385685158459)
      ·
        refine ⟨26005983855324578527737689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17337322570216385685158459 26005983855324578527737689)
        ·
          refine ⟨19504487891493433895803267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26005983855324578527737689 19504487891493433895803267)
          ·
            refine ⟨29256731837240150843704901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504487891493433895803267 29256731837240150843704901)
            ·
              refine ⟨5485637219482528283194669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29256731837240150843704901 5485637219482528283194669)
              ·
                refine ⟨2057113957305948106198001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5485637219482528283194669 2057113957305948106198001)
                ·
                  refine ⟨1542835467979461079648501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2057113957305948106198001 1542835467979461079648501)
                  ·
                    refine ⟨144640825123074476217047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1542835467979461079648501 144640825123074476217047)
                    ·
                      rfl

theorem cell23_845061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_845061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845061 prefixEnd_845061 := by exact prefixLift 845061
  have htrace : WordTrace (prefixWord ++ tailWord_845061) baseStart_845061 baseEnd_845061 := by
    simpa [prefixWord, tailWord_845061, baseEnd_845061] using wordTrace_append hprefix tailTrace_845061
  have hstable : (prefixWord ++ tailWord_845061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845061).length < 2 ^ (prefixWord ++ tailWord_845061).sum := by decide
  have hdescent : baseEnd_845061 < baseStart_845061 := by decide
  rcases family_descends (prefixWord ++ tailWord_845061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845088 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_845088 : Nat := 118140960795 + 845088 * 2 ^ 59
def prefixEnd_845088 : Nat := 4983230072969 + 3 ^ 40 * 845088 * 2
def baseEnd_845088 : Nat := 433936339346894823013517

theorem tailTrace_845088 : CollatzResearch.WordTrace tailWord_845088 prefixEnd_845088 433936339346894823013517 := by
  unfold tailWord_845088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411445781198990192423959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20548594374931986923231945 15411445781198990192423959)
  ·
    refine ⟨23117168671798485288635939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15411445781198990192423959 23117168671798485288635939)
    ·
      refine ⟨34675753007697727932953909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23117168671798485288635939 34675753007697727932953909)
      ·
        refine ⟨3250851844471661993714429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34675753007697727932953909 3250851844471661993714429)
        ·
          refine ⟨1219069441676873247642911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3250851844471661993714429 1219069441676873247642911)
          ·
            refine ⟨1828604162515309871464367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219069441676873247642911 1828604162515309871464367)
            ·
              refine ⟨2742906243772964807196551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828604162515309871464367 2742906243772964807196551)
              ·
                refine ⟨4114359365659447210794827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742906243772964807196551 4114359365659447210794827)
                ·
                  refine ⟨6171539048489170816192241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114359365659447210794827 6171539048489170816192241)
                  ·
                    refine ⟨4628654286366878112144181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171539048489170816192241 4628654286366878112144181)
                    ·
                      refine ⟨433936339346894823013517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4628654286366878112144181 433936339346894823013517)
                      ·
                        rfl

theorem cell23_845088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_845088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845088 prefixEnd_845088 := by exact prefixLift 845088
  have htrace : WordTrace (prefixWord ++ tailWord_845088) baseStart_845088 baseEnd_845088 := by
    simpa [prefixWord, tailWord_845088, baseEnd_845088] using wordTrace_append hprefix tailTrace_845088
  have hstable : (prefixWord ++ tailWord_845088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845088).length < 2 ^ (prefixWord ++ tailWord_845088).sum := by decide
  have hdescent : baseEnd_845088 < baseStart_845088 := by decide
  rcases family_descends (prefixWord ++ tailWord_845088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845131 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3]
def baseStart_845131 : Nat := 118140960795 + 845131 * 2 ^ 59
def prefixEnd_845131 : Nat := 4983230072969 + 3 ^ 40 * 845131 * 2
def baseEnd_845131 : Nat := 433958419015038154775819

theorem tailTrace_845131 : CollatzResearch.WordTrace tailWord_845131 prefixEnd_845131 433958419015038154775819 := by
  unfold tailWord_845131
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824459901242198728663247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549639934161465819108831 30824459901242198728663247)
  ·
    refine ⟨46236689851863298092994871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30824459901242198728663247 46236689851863298092994871)
    ·
      refine ⟨69355034777794947139492307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46236689851863298092994871 69355034777794947139492307)
      ·
        refine ⟨104032552166692420709238461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69355034777794947139492307 104032552166692420709238461)
        ·
          refine ⟨39012207062509657765964423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104032552166692420709238461 39012207062509657765964423)
          ·
            refine ⟨58518310593764486648946635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39012207062509657765964423 58518310593764486648946635)
            ·
              refine ⟨87777465890646729973419953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58518310593764486648946635 87777465890646729973419953)
              ·
                refine ⟨65833099417985047480064965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87777465890646729973419953 65833099417985047480064965)
                ·
                  refine ⟨12343706140872196402512181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65833099417985047480064965 12343706140872196402512181)
                  ·
                    refine ⟨1157222450706768412735517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12343706140872196402512181 1157222450706768412735517)
                    ·
                      refine ⟨433958419015038154775819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157222450706768412735517 433958419015038154775819)
                      ·
                        rfl

theorem cell23_845131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].length) (baseStart_845131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845131 prefixEnd_845131 := by exact prefixLift 845131
  have htrace : WordTrace (prefixWord ++ tailWord_845131) baseStart_845131 baseEnd_845131 := by
    simpa [prefixWord, tailWord_845131, baseEnd_845131] using wordTrace_append hprefix tailTrace_845131
  have hstable : (prefixWord ++ tailWord_845131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845131).length < 2 ^ (prefixWord ++ tailWord_845131).sum := by decide
  have hdescent : baseEnd_845131 < baseStart_845131 := by decide
  rcases family_descends (prefixWord ++ tailWord_845131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845165 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_845165 : Nat := 118140960795 + 845165 * 2 ^ 59
def prefixEnd_845165 : Nat := 4983230072969 + 3 ^ 40 * 845165 * 2
def baseEnd_845165 : Nat := 433975877357291021750663

theorem tailTrace_845165 : CollatzResearch.WordTrace tailWord_845165 prefixEnd_845165 433975877357291021750663 := by
  unfold tailWord_845165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30825699983119022535400949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20550466655412681690267299 30825699983119022535400949)
  ·
    refine ⟨2889909373417408362693839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30825699983119022535400949 2889909373417408362693839)
    ·
      refine ⟨4334864060126112544040759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2889909373417408362693839 4334864060126112544040759)
      ·
        refine ⟨6502296090189168816061139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334864060126112544040759 6502296090189168816061139)
        ·
          refine ⟨9753444135283753224091709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502296090189168816061139 9753444135283753224091709)
          ·
            refine ⟨3657541550731407459034391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9753444135283753224091709 3657541550731407459034391)
            ·
              refine ⟨5486312326097111188551587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657541550731407459034391 5486312326097111188551587)
              ·
                refine ⟨8229468489145666782827381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486312326097111188551587 8229468489145666782827381)
                ·
                  refine ⟨771512670857406260890067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8229468489145666782827381 771512670857406260890067)
                  ·
                    refine ⟨1157269006286109391335101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771512670857406260890067 1157269006286109391335101)
                    ·
                      refine ⟨433975877357291021750663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157269006286109391335101 433975877357291021750663)
                      ·
                        rfl

theorem cell23_845165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_845165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845165 prefixEnd_845165 := by exact prefixLift 845165
  have htrace : WordTrace (prefixWord ++ tailWord_845165) baseStart_845165 baseEnd_845165 := by
    simpa [prefixWord, tailWord_845165, baseEnd_845165] using wordTrace_append hprefix tailTrace_845165
  have hstable : (prefixWord ++ tailWord_845165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845165).length < 2 ^ (prefixWord ++ tailWord_845165).sum := by decide
  have hdescent : baseEnd_845165 < baseStart_845165 := by decide
  rcases family_descends (prefixWord ++ tailWord_845165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845168 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_845168 : Nat := 118140960795 + 845168 * 2 ^ 59
def prefixEnd_845168 : Nat := 4983230072969 + 3 ^ 40 * 845168 * 2
def baseEnd_845168 : Nat := 144659139266418170004383

theorem tailTrace_845168 : CollatzResearch.WordTrace tailWord_845168 prefixEnd_845168 144659139266418170004383 := by
  unfold tailWord_845168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412904701054077023880079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20550539601405436031840105 15412904701054077023880079)
  ·
    refine ⟨23119357051581115535820119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412904701054077023880079 23119357051581115535820119)
    ·
      refine ⟨34679035577371673303730179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23119357051581115535820119 34679035577371673303730179)
      ·
        refine ⟨52018553366057509955595269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34679035577371673303730179 52018553366057509955595269)
        ·
          refine ⟨9753478756135783116674113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52018553366057509955595269 9753478756135783116674113)
          ·
            refine ⟨7315109067101837337505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9753478756135783116674113 7315109067101837337505585)
            ·
              refine ⟨5486331800326378003129189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7315109067101837337505585 5486331800326378003129189)
              ·
                refine ⟨1028687212561195875586723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5486331800326378003129189 1028687212561195875586723)
                ·
                  refine ⟨1543030818841793813380085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028687212561195875586723 1543030818841793813380085)
                  ·
                    refine ⟨144659139266418170004383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1543030818841793813380085 144659139266418170004383)
                    ·
                      rfl

theorem cell23_845168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_845168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845168 prefixEnd_845168 := by exact prefixLift 845168
  have htrace : WordTrace (prefixWord ++ tailWord_845168) baseStart_845168 baseEnd_845168 := by
    simpa [prefixWord, tailWord_845168, baseEnd_845168] using wordTrace_append hprefix tailTrace_845168
  have hstable : (prefixWord ++ tailWord_845168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845168).length < 2 ^ (prefixWord ++ tailWord_845168).sum := by decide
  have hdescent : baseEnd_845168 < baseStart_845168 := by decide
  rcases family_descends (prefixWord ++ tailWord_845168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845201 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_845201 : Nat := 118140960795 + 845201 * 2 ^ 59
def prefixEnd_845201 : Nat := 4983230072969 + 3 ^ 40 * 845201 * 2
def baseEnd_845201 : Nat := 433994362660852880900497

theorem tailTrace_845201 : CollatzResearch.WordTrace tailWord_845201 prefixEnd_845201 433994362660852880900497 := by
  unfold tailWord_845201
  simp only [CollatzResearch.WordTrace]
  refine ⟨30827013010988600683711457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20551342007325733789140971 30827013010988600683711457)
  ·
    refine ⟨23120259758241450512783593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30827013010988600683711457 23120259758241450512783593)
    ·
      refine ⟨17340194818681087884587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23120259758241450512783593 17340194818681087884587695)
      ·
        refine ⟨26010292228021631826881543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340194818681087884587695 26010292228021631826881543)
        ·
          refine ⟨39015438342032447740322315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010292228021631826881543 39015438342032447740322315)
          ·
            refine ⟨58523157513048671610483473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39015438342032447740322315 58523157513048671610483473)
            ·
              refine ⟨43892368134786503707862605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58523157513048671610483473 43892368134786503707862605)
              ·
                refine ⟨16459638050544938890448477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43892368134786503707862605 16459638050544938890448477)
                ·
                  refine ⟨6172364268954352083918179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16459638050544938890448477 6172364268954352083918179)
                  ·
                    refine ⟨9258546403431528125877269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172364268954352083918179 9258546403431528125877269)
                    ·
                      refine ⟨433994362660852880900497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9258546403431528125877269 433994362660852880900497)
                      ·
                        rfl

theorem cell23_845201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_845201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845201 prefixEnd_845201 := by exact prefixLift 845201
  have htrace : WordTrace (prefixWord ++ tailWord_845201) baseStart_845201 baseEnd_845201 := by
    simpa [prefixWord, tailWord_845201, baseEnd_845201] using wordTrace_append hprefix tailTrace_845201
  have hstable : (prefixWord ++ tailWord_845201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845201).length < 2 ^ (prefixWord ++ tailWord_845201).sum := by decide
  have hdescent : baseEnd_845201 < baseStart_845201 := by decide
  rcases family_descends (prefixWord ++ tailWord_845201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845215 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 6]
def baseStart_845215 : Nat := 118140960795 + 845215 * 2 ^ 59
def prefixEnd_845215 : Nat := 4983230072969 + 3 ^ 40 * 845215 * 2
def baseEnd_845215 : Nat := 144667183796671942041811

theorem tailTrace_845215 : CollatzResearch.WordTrace tailWord_845215 prefixEnd_845215 144667183796671942041811 := by
  unfold tailWord_845215
  simp only [CollatzResearch.WordTrace]
  refine ⟨30827523632937881074721099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20551682421958587383147399 30827523632937881074721099)
  ·
    refine ⟨46241285449406821612081649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30827523632937881074721099 46241285449406821612081649)
    ·
      refine ⟨34680964087055116209061237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46241285449406821612081649 34680964087055116209061237)
      ·
        refine ⟨3251340383161417144599491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34680964087055116209061237 3251340383161417144599491)
        ·
          refine ⟨4877010574742125716899237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251340383161417144599491 4877010574742125716899237)
          ·
            refine ⟨914439482764148571918607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4877010574742125716899237 914439482764148571918607)
            ·
              refine ⟨1371659224146222857877911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914439482764148571918607 1371659224146222857877911)
              ·
                refine ⟨2057488836219334286816867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371659224146222857877911 2057488836219334286816867)
                ·
                  refine ⟨3086233254329001430225301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057488836219334286816867 3086233254329001430225301)
                  ·
                    refine ⟨144667183796671942041811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3086233254329001430225301 144667183796671942041811)
                    ·
                      rfl

theorem cell23_845215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_845215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845215 prefixEnd_845215 := by exact prefixLift 845215
  have htrace : WordTrace (prefixWord ++ tailWord_845215) baseStart_845215 baseEnd_845215 := by
    simpa [prefixWord, tailWord_845215, baseEnd_845215] using wordTrace_append hprefix tailTrace_845215
  have hstable : (prefixWord ++ tailWord_845215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845215).length < 2 ^ (prefixWord ++ tailWord_845215).sum := by decide
  have hdescent : baseEnd_845215 < baseStart_845215 := by decide
  rcases family_descends (prefixWord ++ tailWord_845215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845228 : List Nat := [2, 2, 1, 1, 1, 1, 8, 7]
def baseStart_845228 : Nat := 118140960795 + 845228 * 2 ^ 59
def prefixEnd_845228 : Nat := 4983230072969 + 3 ^ 40 * 845228 * 2
def baseEnd_845228 : Nat := 16074378764389787972699

theorem tailTrace_845228 : CollatzResearch.WordTrace tailWord_845228 prefixEnd_845228 16074378764389787972699 := by
  unfold tailWord_845228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413998890945392147472169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20551998521260522863296225 15413998890945392147472169)
  ·
    refine ⟨11560499168209044110604127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15413998890945392147472169 11560499168209044110604127)
    ·
      refine ⟨17340748752313566165906191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11560499168209044110604127 17340748752313566165906191)
      ·
        refine ⟨26011123128470349248859287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340748752313566165906191 26011123128470349248859287)
        ·
          refine ⟨39016684692705523873288931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26011123128470349248859287 39016684692705523873288931)
          ·
            refine ⟨58525027039058285809933397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39016684692705523873288931 58525027039058285809933397)
            ·
              refine ⟨685840160613964286835157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58525027039058285809933397 685840160613964286835157)
              ·
                refine ⟨16074378764389787972699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 685840160613964286835157 16074378764389787972699)
                ·
                  rfl

theorem cell23_845228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 7].length) (baseStart_845228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845228 prefixEnd_845228 := by exact prefixLift 845228
  have htrace : WordTrace (prefixWord ++ tailWord_845228) baseStart_845228 baseEnd_845228 := by
    simpa [prefixWord, tailWord_845228, baseEnd_845228] using wordTrace_append hprefix tailTrace_845228
  have hstable : (prefixWord ++ tailWord_845228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845228).length < 2 ^ (prefixWord ++ tailWord_845228).sum := by decide
  have hdescent : baseEnd_845228 < baseStart_845228 := by decide
  rcases family_descends (prefixWord ++ tailWord_845228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845231 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_845231 : Nat := 118140960795 + 845231 * 2 ^ 59
def prefixEnd_845231 : Nat := 4983230072969 + 3 ^ 40 * 845231 * 2
def baseEnd_845231 : Nat := 434009767080487763525359

theorem tailTrace_845231 : CollatzResearch.WordTrace tailWord_845231 prefixEnd_845231 434009767080487763525359 := by
  unfold tailWord_845231
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828107200879915807303547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20552071467253277204869031 30828107200879915807303547)
  ·
    refine ⟨46242160801319873710955321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30828107200879915807303547 46242160801319873710955321)
    ·
      refine ⟨34681620600989905283216491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46242160801319873710955321 34681620600989905283216491)
      ·
        refine ⟨52022430901484857924824737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34681620600989905283216491 52022430901484857924824737)
        ·
          refine ⟨39016823176113643443618553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52022430901484857924824737 39016823176113643443618553)
          ·
            refine ⟨29262617382085232582713915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39016823176113643443618553 29262617382085232582713915)
            ·
              refine ⟨43893926073127848874070873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29262617382085232582713915 43893926073127848874070873)
              ·
                refine ⟨32920444554845886655553155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43893926073127848874070873 32920444554845886655553155)
                ·
                  refine ⟨49380666832268829983329733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32920444554845886655553155 49380666832268829983329733)
                  ·
                    refine ⟨9258875031050405621874325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49380666832268829983329733 9258875031050405621874325)
                    ·
                      refine ⟨434009767080487763525359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9258875031050405621874325 434009767080487763525359)
                      ·
                        rfl

theorem cell23_845231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_845231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845231 prefixEnd_845231 := by exact prefixLift 845231
  have htrace : WordTrace (prefixWord ++ tailWord_845231) baseStart_845231 baseEnd_845231 := by
    simpa [prefixWord, tailWord_845231, baseEnd_845231] using wordTrace_append hprefix tailTrace_845231
  have hstable : (prefixWord ++ tailWord_845231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845231).length < 2 ^ (prefixWord ++ tailWord_845231).sum := by decide
  have hdescent : baseEnd_845231 < baseStart_845231 := by decide
  rcases family_descends (prefixWord ++ tailWord_845231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845250 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_845250 : Nat := 118140960795 + 845250 * 2 ^ 59
def prefixEnd_845250 : Nat := 4983230072969 + 3 ^ 40 * 845250 * 2
def baseEnd_845250 : Nat := 434019523212923189187773

theorem tailTrace_845250 : CollatzResearch.WordTrace tailWord_845250 prefixEnd_845250 434019523212923189187773 := by
  unfold tailWord_845250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707200046952770513061301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20552533458540721368163469 7707200046952770513061301)
  ·
    refine ⟨722550004401822235599497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7707200046952770513061301 722550004401822235599497)
    ·
      refine ⟨541912503301366676699623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722550004401822235599497 541912503301366676699623)
      ·
        refine ⟨812868754952050015049435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541912503301366676699623 812868754952050015049435)
        ·
          refine ⟨1219303132428075022574153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812868754952050015049435 1219303132428075022574153)
          ·
            refine ⟨914477349321056266930615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219303132428075022574153 914477349321056266930615)
            ·
              refine ⟨1371716023981584400395923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914477349321056266930615 1371716023981584400395923)
              ·
                refine ⟨2057574035972376600593885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371716023981584400395923 2057574035972376600593885)
                ·
                  refine ⟨771590263489641225222707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2057574035972376600593885 771590263489641225222707)
                  ·
                    refine ⟨1157385395234461837834061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 771590263489641225222707 1157385395234461837834061)
                    ·
                      refine ⟨434019523212923189187773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1157385395234461837834061 434019523212923189187773)
                      ·
                        rfl

theorem cell23_845250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_845250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_845250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_845250 prefixEnd_845250 := by exact prefixLift 845250
  have htrace : WordTrace (prefixWord ++ tailWord_845250) baseStart_845250 baseEnd_845250 := by
    simpa [prefixWord, tailWord_845250, baseEnd_845250] using wordTrace_append hprefix tailTrace_845250
  have hstable : (prefixWord ++ tailWord_845250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845250).length < 2 ^ (prefixWord ++ tailWord_845250).sum := by decide
  have hdescent : baseEnd_845250 < baseStart_845250 := by decide
  rcases family_descends (prefixWord ++ tailWord_845250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
