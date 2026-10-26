import V185TrunkScan23Chunk0151

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_897598 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_897598 : Nat := 118140960795 + 897598 * 2 ^ 59
def prefixEnd_897598 : Nat := 4983230072969 + 3 ^ 40 * 897598 * 2
def baseEnd_897598 : Nat := 460899208514484377397029

theorem tailTrace_897598 : CollatzResearch.WordTrace tailWord_897598 prefixEnd_897598 460899208514484377397029 := by
  unfold tailWord_897598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092261075270402297358681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21825392401442145585912965 4092261075270402297358681)
  ·
    refine ⟨3069195806452801723019011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092261075270402297358681 3069195806452801723019011)
    ·
      refine ⟨4603793709679202584528517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069195806452801723019011 4603793709679202584528517)
      ·
        refine ⟨863211320564850484599097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4603793709679202584528517 863211320564850484599097)
        ·
          refine ⟨647408490423637863449323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863211320564850484599097 647408490423637863449323)
          ·
            refine ⟨971112735635456795173985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647408490423637863449323 971112735635456795173985)
            ·
              refine ⟨728334551726592596380489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971112735635456795173985 728334551726592596380489)
              ·
                refine ⟨546250913794944447285367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728334551726592596380489 546250913794944447285367)
                ·
                  refine ⟨819376370692416670928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546250913794944447285367 819376370692416670928051)
                  ·
                    refine ⟨1229064556038625006392077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819376370692416670928051 1229064556038625006392077)
                    ·
                      refine ⟨460899208514484377397029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229064556038625006392077 460899208514484377397029)
                      ·
                        rfl

theorem cell23_897598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_897598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897598 prefixEnd_897598 := by exact prefixLift 897598
  have htrace : WordTrace (prefixWord ++ tailWord_897598) baseStart_897598 baseEnd_897598 := by
    simpa [prefixWord, tailWord_897598, baseEnd_897598] using wordTrace_append hprefix tailTrace_897598
  have hstable : (prefixWord ++ tailWord_897598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897598).length < 2 ^ (prefixWord ++ tailWord_897598).sum := by decide
  have hdescent : baseEnd_897598 < baseStart_897598 := by decide
  rcases family_descends (prefixWord ++ tailWord_897598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897620 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_897620 : Nat := 118140960795 + 897620 * 2 ^ 59
def prefixEnd_897620 : Nat := 4983230072969 + 3 ^ 40 * 897620 * 2
def baseEnd_897620 : Nat := 460910505088883291321927

theorem tailTrace_897620 : CollatzResearch.WordTrace tailWord_897620 prefixEnd_897620 460910505088883291321927 := by
  unfold tailWord_897620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16369445504041758068085157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21825927338722344090780209 16369445504041758068085157)
  ·
    refine ⟨3069271032007829637765967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16369445504041758068085157 3069271032007829637765967)
    ·
      refine ⟨4603906548011744456648951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069271032007829637765967 4603906548011744456648951)
      ·
        refine ⟨6905859822017616684973427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4603906548011744456648951 6905859822017616684973427)
        ·
          refine ⟨10358789733026425027460141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905859822017616684973427 10358789733026425027460141)
          ·
            refine ⟨3884546149884909385297553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10358789733026425027460141 3884546149884909385297553)
            ·
              refine ⟨2913409612413682038973165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884546149884909385297553 2913409612413682038973165)
              ·
                refine ⟨1092528604655130764614937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2913409612413682038973165 1092528604655130764614937)
                ·
                  refine ⟨819396453491348073461203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092528604655130764614937 819396453491348073461203)
                  ·
                    refine ⟨1229094680237022110191805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819396453491348073461203 1229094680237022110191805)
                    ·
                      refine ⟨460910505088883291321927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229094680237022110191805 460910505088883291321927)
                      ·
                        rfl

theorem cell23_897620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_897620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897620 prefixEnd_897620 := by exact prefixLift 897620
  have htrace : WordTrace (prefixWord ++ tailWord_897620) baseStart_897620 baseEnd_897620 := by
    simpa [prefixWord, tailWord_897620, baseEnd_897620] using wordTrace_append hprefix tailTrace_897620
  have hstable : (prefixWord ++ tailWord_897620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897620).length < 2 ^ (prefixWord ++ tailWord_897620).sum := by decide
  have hdescent : baseEnd_897620 < baseStart_897620 := by decide
  rcases family_descends (prefixWord ++ tailWord_897620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897654 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_897654 : Nat := 118140960795 + 897654 * 2 ^ 59
def prefixEnd_897654 : Nat := 4983230072969 + 3 ^ 40 * 897654 * 2
def baseEnd_897654 : Nat := 460927963431136158296771

theorem tailTrace_897654 : CollatzResearch.WordTrace tailWord_897654 prefixEnd_897654 460927963431136158296771 := by
  unfold tailWord_897654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046258193122521246431751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21826754059973559961938677 2046258193122521246431751)
  ·
    refine ⟨3069387289683781869647627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046258193122521246431751 3069387289683781869647627)
    ·
      refine ⟨4604080934525672804471441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069387289683781869647627 4604080934525672804471441)
      ·
        refine ⟨3453060700894254603353581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4604080934525672804471441 3453060700894254603353581)
        ·
          refine ⟨1294897762835345476257593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453060700894254603353581 1294897762835345476257593)
          ·
            refine ⟨971173322126509107193195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294897762835345476257593 971173322126509107193195)
            ·
              refine ⟨1456759983189763660789793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971173322126509107193195 1456759983189763660789793)
              ·
                refine ⟨1092569987392322745592345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456759983189763660789793 1092569987392322745592345)
                ·
                  refine ⟨819427490544242059194259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092569987392322745592345 819427490544242059194259)
                  ·
                    refine ⟨1229141235816363088791389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819427490544242059194259 1229141235816363088791389)
                    ·
                      refine ⟨460927963431136158296771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229141235816363088791389 460927963431136158296771)
                      ·
                        rfl

theorem cell23_897654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_897654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897654 prefixEnd_897654 := by exact prefixLift 897654
  have htrace : WordTrace (prefixWord ++ tailWord_897654) baseStart_897654 baseEnd_897654 := by
    simpa [prefixWord, tailWord_897654, baseEnd_897654] using wordTrace_append hprefix tailTrace_897654
  have hstable : (prefixWord ++ tailWord_897654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897654).length < 2 ^ (prefixWord ++ tailWord_897654).sum := by decide
  have hdescent : baseEnd_897654 < baseStart_897654 := by decide
  rcases family_descends (prefixWord ++ tailWord_897654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897659 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_897659 : Nat := 118140960795 + 897659 * 2 ^ 59
def prefixEnd_897659 : Nat := 4983230072969 + 3 ^ 40 * 897659 * 2
def baseEnd_897659 : Nat := 460930530834408638734247

theorem tailTrace_897659 : CollatzResearch.WordTrace tailWord_897659 prefixEnd_897659 460930530834408638734247 := by
  unfold tailWord_897659
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740313454942225796840031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21826875636628150531226687 32740313454942225796840031)
  ·
    refine ⟨49110470182413338695260047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32740313454942225796840031 49110470182413338695260047)
    ·
      refine ⟨73665705273620008042890071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49110470182413338695260047 73665705273620008042890071)
      ·
        refine ⟨110498557910430012064335107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73665705273620008042890071 110498557910430012064335107)
        ·
          refine ⟨165747836865645018096502661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110498557910430012064335107 165747836865645018096502661)
          ·
            refine ⟨31077719412308440893094249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165747836865645018096502661 31077719412308440893094249)
            ·
              refine ⟨23308289559231330669820687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31077719412308440893094249 23308289559231330669820687)
              ·
                refine ⟨34962434338846996004731031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23308289559231330669820687 34962434338846996004731031)
                ·
                  refine ⟨52443651508270494007096547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34962434338846996004731031 52443651508270494007096547)
                  ·
                    refine ⟨78665477262405741010644821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52443651508270494007096547 78665477262405741010644821)
                    ·
                      refine ⟨460930530834408638734247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 78665477262405741010644821 460930530834408638734247)
                      ·
                        rfl

theorem cell23_897659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_897659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897659 prefixEnd_897659 := by exact prefixLift 897659
  have htrace : WordTrace (prefixWord ++ tailWord_897659) baseStart_897659 baseEnd_897659 := by
    simpa [prefixWord, tailWord_897659, baseEnd_897659] using wordTrace_append hprefix tailTrace_897659
  have hstable : (prefixWord ++ tailWord_897659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897659).length < 2 ^ (prefixWord ++ tailWord_897659).sum := by decide
  have hdescent : baseEnd_897659 < baseStart_897659 := by decide
  rcases family_descends (prefixWord ++ tailWord_897659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897676 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_897676 : Nat := 118140960795 + 897676 * 2 ^ 59
def prefixEnd_897676 : Nat := 4983230072969 + 3 ^ 40 * 897676 * 2
def baseEnd_897676 : Nat := 460939260005535072221669

theorem tailTrace_897676 : CollatzResearch.WordTrace tailWord_897676 prefixEnd_897676 460939260005535072221669 := by
  unfold tailWord_897676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370466747940318850104441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21827288997253758466805921 16370466747940318850104441)
  ·
    refine ⟨12277850060955239137578331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16370466747940318850104441 12277850060955239137578331)
    ·
      refine ⟨18416775091432858706367497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277850060955239137578331 18416775091432858706367497)
      ·
        refine ⟨13812581318574644029775623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18416775091432858706367497 13812581318574644029775623)
        ·
          refine ⟨20718871977861966044663435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812581318574644029775623 20718871977861966044663435)
          ·
            refine ⟨31078307966792949066995153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20718871977861966044663435 31078307966792949066995153)
            ·
              refine ⟨23308730975094711800246365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31078307966792949066995153 23308730975094711800246365)
              ·
                refine ⟨8740774115660516925092387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23308730975094711800246365 8740774115660516925092387)
                ·
                  refine ⟨13111161173490775387638581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740774115660516925092387 13111161173490775387638581)
                  ·
                    refine ⟨1229171360014760192591117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13111161173490775387638581 1229171360014760192591117)
                    ·
                      refine ⟨460939260005535072221669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229171360014760192591117 460939260005535072221669)
                      ·
                        rfl

theorem cell23_897676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_897676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897676 prefixEnd_897676 := by exact prefixLift 897676
  have htrace : WordTrace (prefixWord ++ tailWord_897676) baseStart_897676 baseEnd_897676 := by
    simpa [prefixWord, tailWord_897676, baseEnd_897676] using wordTrace_append hprefix tailTrace_897676
  have hstable : (prefixWord ++ tailWord_897676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897676).length < 2 ^ (prefixWord ++ tailWord_897676).sum := by decide
  have hdescent : baseEnd_897676 < baseStart_897676 := by decide
  rcases family_descends (prefixWord ++ tailWord_897676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897717 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 5]
def baseStart_897717 : Nat := 118140960795 + 897717 * 2 ^ 59
def prefixEnd_897717 : Nat := 4983230072969 + 3 ^ 40 * 897717 * 2
def baseEnd_897717 : Nat := 51217812523596601312109

theorem tailTrace_897717 : CollatzResearch.WordTrace tailWord_897717 prefixEnd_897717 51217812523596601312109 := by
  unfold tailWord_897717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742428888732101702451405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21828285925821401134967603 32742428888732101702451405)
  ·
    refine ⟨12278410833274538138419277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32742428888732101702451405 12278410833274538138419277)
    ·
      refine ⟨4604404062477951801907229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12278410833274538138419277 4604404062477951801907229)
      ·
        refine ⟨1726651523429231925715211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4604404062477951801907229 1726651523429231925715211)
        ·
          refine ⟨2589977285143847888572817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726651523429231925715211 2589977285143847888572817)
          ·
            refine ⟨1942482963857885916429613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589977285143847888572817 1942482963857885916429613)
            ·
              refine ⟨728431111446707218661105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942482963857885916429613 728431111446707218661105)
              ·
                refine ⟨546323333585030413995829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728431111446707218661105 546323333585030413995829)
                ·
                  refine ⟨51217812523596601312109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546323333585030413995829 51217812523596601312109)
                  ·
                    rfl

theorem cell23_897717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_897717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897717 prefixEnd_897717 := by exact prefixLift 897717
  have htrace : WordTrace (prefixWord ++ tailWord_897717) baseStart_897717 baseEnd_897717 := by
    simpa [prefixWord, tailWord_897717, baseEnd_897717] using wordTrace_append hprefix tailTrace_897717
  have hstable : (prefixWord ++ tailWord_897717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897717).length < 2 ^ (prefixWord ++ tailWord_897717).sum := by decide
  have hdescent : baseEnd_897717 < baseStart_897717 := by decide
  rcases family_descends (prefixWord ++ tailWord_897717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897760 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 1, 4]
def baseStart_897760 : Nat := 118140960795 + 897760 * 2 ^ 59
def prefixEnd_897760 : Nat := 4983230072969 + 3 ^ 40 * 897760 * 2
def baseEnd_897760 : Nat := 153660797460170914523761

theorem tailTrace_897760 : CollatzResearch.WordTrace tailWord_897760 prefixEnd_897760 153660797460170914523761 := by
  unfold tailWord_897760
  simp only [CollatzResearch.WordTrace]
  refine ⟨16371998613788160023133367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21829331485050880030844489 16371998613788160023133367)
  ·
    refine ⟨24557997920682240034700051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16371998613788160023133367 24557997920682240034700051)
    ·
      refine ⟨36836996881023360052050077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24557997920682240034700051 36836996881023360052050077)
      ·
        refine ⟨13813873830383760019518779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36836996881023360052050077 13813873830383760019518779)
        ·
          refine ⟨20720810745575640029278169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13813873830383760019518779 20720810745575640029278169)
          ·
            refine ⟨15540608059181730021958627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20720810745575640029278169 15540608059181730021958627)
            ·
              refine ⟨23310912088772595032937941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540608059181730021958627 23310912088772595032937941)
              ·
                refine ⟨546349502080607696084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23310912088772595032937941 546349502080607696084483)
                ·
                  refine ⟨819524253120911544126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546349502080607696084483 819524253120911544126725)
                  ·
                    refine ⟨153660797460170914523761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819524253120911544126725 153660797460170914523761)
                    ·
                      rfl

theorem cell23_897760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_897760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897760 prefixEnd_897760 := by exact prefixLift 897760
  have htrace : WordTrace (prefixWord ++ tailWord_897760) baseStart_897760 baseEnd_897760 := by
    simpa [prefixWord, tailWord_897760, baseEnd_897760] using wordTrace_append hprefix tailTrace_897760
  have hstable : (prefixWord ++ tailWord_897760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897760).length < 2 ^ (prefixWord ++ tailWord_897760).sum := by decide
  have hdescent : baseEnd_897760 < baseStart_897760 := by decide
  rcases family_descends (prefixWord ++ tailWord_897760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897776 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_897776 : Nat := 118140960795 + 897776 * 2 ^ 59
def prefixEnd_897776 : Nat := 4983230072969 + 3 ^ 40 * 897776 * 2
def baseEnd_897776 : Nat := 460990608070984680971209

theorem tailTrace_897776 : CollatzResearch.WordTrace tailWord_897776 prefixEnd_897776 460990608070984680971209 := by
  unfold tailWord_897776
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372290397759177389424591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21829720530345569852566121 16372290397759177389424591)
  ·
    refine ⟨24558435596638766084136887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372290397759177389424591 24558435596638766084136887)
    ·
      refine ⟨36837653394958149126205331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24558435596638766084136887 36837653394958149126205331)
      ·
        refine ⟨55256480092437223689307997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36837653394958149126205331 55256480092437223689307997)
        ·
          refine ⟨20721180034663958883490499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55256480092437223689307997 20721180034663958883490499)
          ·
            refine ⟨31081770051995938325235749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20721180034663958883490499 31081770051995938325235749)
            ·
              refine ⟨5827831884749238435981703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31081770051995938325235749 5827831884749238435981703)
              ·
                refine ⟨8741747827123857653972555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827831884749238435981703 8741747827123857653972555)
                ·
                  refine ⟨13112621740685786480958833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741747827123857653972555 13112621740685786480958833)
                  ·
                    refine ⟨9834466305514339860719125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13112621740685786480958833 9834466305514339860719125)
                    ·
                      refine ⟨460990608070984680971209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9834466305514339860719125 460990608070984680971209)
                      ·
                        rfl

theorem cell23_897776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_897776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897776 prefixEnd_897776 := by exact prefixLift 897776
  have htrace : WordTrace (prefixWord ++ tailWord_897776) baseStart_897776 baseEnd_897776 := by
    simpa [prefixWord, tailWord_897776, baseEnd_897776] using wordTrace_append hprefix tailTrace_897776
  have hstable : (prefixWord ++ tailWord_897776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897776).length < 2 ^ (prefixWord ++ tailWord_897776).sum := by decide
  have hdescent : baseEnd_897776 < baseStart_897776 := by decide
  rcases family_descends (prefixWord ++ tailWord_897776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897790 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_897790 : Nat := 118140960795 + 897790 * 2 ^ 59
def prefixEnd_897790 : Nat := 4983230072969 + 3 ^ 40 * 897790 * 2
def baseEnd_897790 : Nat := 51221977422238625132905

theorem tailTrace_897790 : CollatzResearch.WordTrace tailWord_897790 prefixEnd_897790 51221977422238625132905 := by
  unfold tailWord_897790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093136427183454396232353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21830060944978423446572549 4093136427183454396232353)
  ·
    refine ⟨3069852320387590797174265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4093136427183454396232353 3069852320387590797174265)
    ·
      refine ⟨2302389240290693097880699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069852320387590797174265 2302389240290693097880699)
      ·
        refine ⟨3453583860436039646821049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302389240290693097880699 3453583860436039646821049)
        ·
          refine ⟨2590187895327029735115787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3453583860436039646821049 2590187895327029735115787)
          ·
            refine ⟨3885281842990544602673681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590187895327029735115787 3885281842990544602673681)
            ·
              refine ⟨2913961382242908452005261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885281842990544602673681 2913961382242908452005261)
              ·
                refine ⟨1092735518341090669501973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2913961382242908452005261 1092735518341090669501973)
                ·
                  refine ⟨51221977422238625132905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1092735518341090669501973 51221977422238625132905)
                  ·
                    rfl

theorem cell23_897790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_897790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897790 prefixEnd_897790 := by exact prefixLift 897790
  have htrace : WordTrace (prefixWord ++ tailWord_897790) baseStart_897790 baseEnd_897790 := by
    simpa [prefixWord, tailWord_897790, baseEnd_897790] using wordTrace_append hprefix tailTrace_897790
  have hstable : (prefixWord ++ tailWord_897790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897790).length < 2 ^ (prefixWord ++ tailWord_897790).sum := by decide
  have hdescent : baseEnd_897790 < baseStart_897790 := by decide
  rcases family_descends (prefixWord ++ tailWord_897790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897800 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_897800 : Nat := 118140960795 + 897800 * 2 ^ 59
def prefixEnd_897800 : Nat := 4983230072969 + 3 ^ 40 * 897800 * 2
def baseEnd_897800 : Nat := 461002931606692587071099

theorem tailTrace_897800 : CollatzResearch.WordTrace tailWord_897800 prefixEnd_897800 461002931606692587071099 := by
  unfold tailWord_897800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372728073715703438861427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21830304098287604585148569 16372728073715703438861427)
  ·
    refine ⟨24559092110573555158292141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372728073715703438861427 24559092110573555158292141)
    ·
      refine ⟨9209659541465083184359553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24559092110573555158292141 9209659541465083184359553)
      ·
        refine ⟨6907244656098812388269665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9209659541465083184359553 6907244656098812388269665)
        ·
          refine ⟨5180433492074109291202249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6907244656098812388269665 5180433492074109291202249)
          ·
            refine ⟨3885325119055581968401687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5180433492074109291202249 3885325119055581968401687)
            ·
              refine ⟨5827987678583372952602531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885325119055581968401687 5827987678583372952602531)
              ·
                refine ⟨8741981517875059428903797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827987678583372952602531 8741981517875059428903797)
                ·
                  refine ⟨819560767300786821459731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8741981517875059428903797 819560767300786821459731)
                  ·
                    refine ⟨1229341150951180232189597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819560767300786821459731 1229341150951180232189597)
                    ·
                      refine ⟨461002931606692587071099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1229341150951180232189597 461002931606692587071099)
                      ·
                        rfl

theorem cell23_897800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_897800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897800 prefixEnd_897800 := by exact prefixLift 897800
  have htrace : WordTrace (prefixWord ++ tailWord_897800) baseStart_897800 baseEnd_897800 := by
    simpa [prefixWord, tailWord_897800, baseEnd_897800] using wordTrace_append hprefix tailTrace_897800
  have hstable : (prefixWord ++ tailWord_897800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897800).length < 2 ^ (prefixWord ++ tailWord_897800).sum := by decide
  have hdescent : baseEnd_897800 < baseStart_897800 := by decide
  rcases family_descends (prefixWord ++ tailWord_897800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897803 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 1, 5]
def baseStart_897803 : Nat := 118140960795 + 897803 * 2 ^ 59
def prefixEnd_897803 : Nat := 4983230072969 + 3 ^ 40 * 897803 * 2
def baseEnd_897803 : Nat := 153668157349552025111195

theorem tailTrace_897803 : CollatzResearch.WordTrace tailWord_897803 prefixEnd_897803 153668157349552025111195 := by
  unfold tailWord_897803
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745565566420538390082063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21830377044280358926721375 32745565566420538390082063)
  ·
    refine ⟨49118348349630807585123095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32745565566420538390082063 49118348349630807585123095)
    ·
      refine ⟨73677522524446211377684643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49118348349630807585123095 73677522524446211377684643)
      ·
        refine ⟨110516283786669317066526965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73677522524446211377684643 110516283786669317066526965)
        ·
          refine ⟨10360901605000248474986903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110516283786669317066526965 10360901605000248474986903)
          ·
            refine ⟨15541352407500372712480355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360901605000248474986903 15541352407500372712480355)
            ·
              refine ⟨23312028611250559068720533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541352407500372712480355 23312028611250559068720533)
              ·
                refine ⟨1092751341152369956346275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23312028611250559068720533 1092751341152369956346275)
                ·
                  refine ⟨1639127011728554934519413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092751341152369956346275 1639127011728554934519413)
                  ·
                    refine ⟨153668157349552025111195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1639127011728554934519413 153668157349552025111195)
                    ·
                      rfl

theorem cell23_897803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 5].length) (baseStart_897803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897803 prefixEnd_897803 := by exact prefixLift 897803
  have htrace : WordTrace (prefixWord ++ tailWord_897803) baseStart_897803 baseEnd_897803 := by
    simpa [prefixWord, tailWord_897803, baseEnd_897803] using wordTrace_append hprefix tailTrace_897803
  have hstable : (prefixWord ++ tailWord_897803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897803).length < 2 ^ (prefixWord ++ tailWord_897803).sum := by decide
  have hdescent : baseEnd_897803 < baseStart_897803 := by decide
  rcases family_descends (prefixWord ++ tailWord_897803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897820 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_897820 : Nat := 118140960795 + 897820 * 2 ^ 59
def prefixEnd_897820 : Nat := 4983230072969 + 3 ^ 40 * 897820 * 2
def baseEnd_897820 : Nat := 153671067073260836273669

theorem tailTrace_897820 : CollatzResearch.WordTrace tailWord_897820 prefixEnd_897820 153671067073260836273669 := by
  unfold tailWord_897820
  simp only [CollatzResearch.WordTrace]
  refine ⟨16373092803679475146725457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21830790404905966862300609 16373092803679475146725457)
  ·
    refine ⟨12279819602759606360044093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16373092803679475146725457 12279819602759606360044093)
    ·
      refine ⟨4604932351034852385016535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12279819602759606360044093 4604932351034852385016535)
      ·
        refine ⟨6907398526552278577524803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604932351034852385016535 6907398526552278577524803)
        ·
          refine ⟨10361097789828417866287205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907398526552278577524803 10361097789828417866287205)
          ·
            refine ⟨1942705835592828349928851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10361097789828417866287205 1942705835592828349928851)
            ·
              refine ⟨2914058753389242524893277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942705835592828349928851 2914058753389242524893277)
              ·
                refine ⟨1092772032520965946834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2914058753389242524893277 1092772032520965946834979)
                ·
                  refine ⟨1639158048781448920252469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092772032520965946834979 1639158048781448920252469)
                  ·
                    refine ⟨153671067073260836273669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1639158048781448920252469 153671067073260836273669)
                    ·
                      rfl

theorem cell23_897820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_897820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897820 prefixEnd_897820 := by exact prefixLift 897820
  have htrace : WordTrace (prefixWord ++ tailWord_897820) baseStart_897820 baseEnd_897820 := by
    simpa [prefixWord, tailWord_897820, baseEnd_897820] using wordTrace_append hprefix tailTrace_897820
  have hstable : (prefixWord ++ tailWord_897820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897820).length < 2 ^ (prefixWord ++ tailWord_897820).sum := by decide
  have hdescent : baseEnd_897820 < baseStart_897820 := by decide
  rcases family_descends (prefixWord ++ tailWord_897820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_897833 : Nat := 118140960795 + 897833 * 2 ^ 59
def prefixEnd_897833 : Nat := 4983230072969 + 3 ^ 40 * 897833 * 2
def baseEnd_897833 : Nat := 153673292156096985986149

theorem tailTrace_897833 : CollatzResearch.WordTrace tailWord_897833 prefixEnd_897833 153673292156096985986149 := by
  unfold tailWord_897833
  simp only [CollatzResearch.WordTrace]
  refine ⟨32746659756311853513674153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21831106504207902342449435 32746659756311853513674153)
  ·
    refine ⟨24559994817233890135255615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32746659756311853513674153 24559994817233890135255615)
    ·
      refine ⟨36839992225850835202883423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24559994817233890135255615 36839992225850835202883423)
      ·
        refine ⟨55259988338776252804325135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36839992225850835202883423 55259988338776252804325135)
        ·
          refine ⟨82889982508164379206487703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55259988338776252804325135 82889982508164379206487703)
          ·
            refine ⟨124334973762246568809731555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82889982508164379206487703 124334973762246568809731555)
            ·
              refine ⟨186502460643369853214597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124334973762246568809731555 186502460643369853214597333)
              ·
                refine ⟨4371151421328980934717125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186502460643369853214597333 4371151421328980934717125)
                ·
                  refine ⟨819590891499183925259461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4371151421328980934717125 819590891499183925259461)
                  ·
                    refine ⟨153673292156096985986149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 819590891499183925259461 153673292156096985986149)
                    ·
                      rfl

theorem cell23_897833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_897833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897833 prefixEnd_897833 := by exact prefixLift 897833
  have htrace : WordTrace (prefixWord ++ tailWord_897833) baseStart_897833 baseEnd_897833 := by
    simpa [prefixWord, tailWord_897833, baseEnd_897833] using wordTrace_append hprefix tailTrace_897833
  have hstable : (prefixWord ++ tailWord_897833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897833).length < 2 ^ (prefixWord ++ tailWord_897833).sum := by decide
  have hdescent : baseEnd_897833 < baseStart_897833 := by decide
  rcases family_descends (prefixWord ++ tailWord_897833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897843 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_897843 : Nat := 118140960795 + 897843 * 2 ^ 59
def prefixEnd_897843 : Nat := 4983230072969 + 3 ^ 40 * 897843 * 2
def baseEnd_897843 : Nat := 461025011274835918833401

theorem tailTrace_897843 : CollatzResearch.WordTrace tailWord_897843 prefixEnd_897843 461025011274835918833401 := by
  unfold tailWord_897843
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747024486275625221538183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21831349657517083481025455 32747024486275625221538183)
  ·
    refine ⟨49120536729413437832307275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747024486275625221538183 49120536729413437832307275)
    ·
      refine ⟨73680805094120156748460913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49120536729413437832307275 73680805094120156748460913)
      ·
        refine ⟨55260603820590117561345685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73680805094120156748460913 55260603820590117561345685)
        ·
          refine ⟨2590340804090161760688079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55260603820590117561345685 2590340804090161760688079)
          ·
            refine ⟨3885511206135242641032119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590340804090161760688079 3885511206135242641032119)
            ·
              refine ⟨5828266809202863961548179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885511206135242641032119 5828266809202863961548179)
              ·
                refine ⟨8742400213804295942322269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828266809202863961548179 8742400213804295942322269)
                ·
                  refine ⟨3278400080176610978370851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8742400213804295942322269 3278400080176610978370851)
                  ·
                    refine ⟨4917600120264916467556277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278400080176610978370851 4917600120264916467556277)
                    ·
                      refine ⟨461025011274835918833401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4917600120264916467556277 461025011274835918833401)
                      ·
                        rfl

theorem cell23_897843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_897843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897843 prefixEnd_897843 := by exact prefixLift 897843
  have htrace : WordTrace (prefixWord ++ tailWord_897843) baseStart_897843 baseEnd_897843 := by
    simpa [prefixWord, tailWord_897843, baseEnd_897843] using wordTrace_append hprefix tailTrace_897843
  have hstable : (prefixWord ++ tailWord_897843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897843).length < 2 ^ (prefixWord ++ tailWord_897843).sum := by decide
  have hdescent : baseEnd_897843 < baseStart_897843 := by decide
  rcases family_descends (prefixWord ++ tailWord_897843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897940 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_897940 : Nat := 118140960795 + 897940 * 2 ^ 59
def prefixEnd_897940 : Nat := 4983230072969 + 3 ^ 40 * 897940 * 2
def baseEnd_897940 : Nat := 153691606299440679773485

theorem tailTrace_897940 : CollatzResearch.WordTrace tailWord_897940 prefixEnd_897940 153691606299440679773485 := by
  unfold tailWord_897940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16375281183462105393909637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21833708244616140525212849 16375281183462105393909637)
  ·
    refine ⟨3070365221899144761358057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16375281183462105393909637 3070365221899144761358057)
    ·
      refine ⟨2302773916424358571018543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070365221899144761358057 2302773916424358571018543)
      ·
        refine ⟨3454160874636537856527815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302773916424358571018543 3454160874636537856527815)
        ·
          refine ⟨5181241311954806784791723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454160874636537856527815 5181241311954806784791723)
          ·
            refine ⟨7771861967932210177187585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181241311954806784791723 7771861967932210177187585)
            ·
              refine ⟨5828896475949157632890689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771861967932210177187585 5828896475949157632890689)
              ·
                refine ⟨4371672356961868224668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828896475949157632890689 4371672356961868224668017)
                ·
                  refine ⟨3278754267721401168501013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371672356961868224668017 3278754267721401168501013)
                  ·
                    refine ⟨153691606299440679773485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3278754267721401168501013 153691606299440679773485)
                    ·
                      rfl

theorem cell23_897940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_897940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897940 prefixEnd_897940 := by exact prefixLift 897940
  have htrace : WordTrace (prefixWord ++ tailWord_897940) baseStart_897940 baseEnd_897940 := by
    simpa [prefixWord, tailWord_897940, baseEnd_897940] using wordTrace_append hprefix tailTrace_897940
  have hstable : (prefixWord ++ tailWord_897940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897940).length < 2 ^ (prefixWord ++ tailWord_897940).sum := by decide
  have hdescent : baseEnd_897940 < baseStart_897940 := by decide
  rcases family_descends (prefixWord ++ tailWord_897940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897942 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_897942 : Nat := 118140960795 + 897942 * 2 ^ 59
def prefixEnd_897942 : Nat := 4983230072969 + 3 ^ 40 * 897942 * 2
def baseEnd_897942 : Nat := 461075845859631031495447

theorem tailTrace_897942 : CollatzResearch.WordTrace tailWord_897942 prefixEnd_897942 461075845859631031495447 := by
  unfold tailWord_897942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046914707057310320587005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21833756875277976752928053 2046914707057310320587005)
  ·
    refine ⟨767593015146491370220127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2046914707057310320587005 767593015146491370220127)
    ·
      refine ⟨1151389522719737055330191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767593015146491370220127 1151389522719737055330191)
      ·
        refine ⟨1727084284079605582995287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151389522719737055330191 1727084284079605582995287)
        ·
          refine ⟨2590626426119408374492931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727084284079605582995287 2590626426119408374492931)
          ·
            refine ⟨3885939639179112561739397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590626426119408374492931 3885939639179112561739397)
            ·
              refine ⟨728613682346083605326137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3885939639179112561739397 728613682346083605326137)
              ·
                refine ⟨546460261759562703994603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728613682346083605326137 546460261759562703994603)
                ·
                  refine ⟨819690392639344055991905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546460261759562703994603 819690392639344055991905)
                  ·
                    refine ⟨614767794479508041993929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 819690392639344055991905 614767794479508041993929)
                    ·
                      refine ⟨461075845859631031495447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 614767794479508041993929 461075845859631031495447)
                      ·
                        rfl

theorem cell23_897942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_897942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_897942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_897942 prefixEnd_897942 := by exact prefixLift 897942
  have htrace : WordTrace (prefixWord ++ tailWord_897942) baseStart_897942 baseEnd_897942 := by
    simpa [prefixWord, tailWord_897942, baseEnd_897942] using wordTrace_append hprefix tailTrace_897942
  have hstable : (prefixWord ++ tailWord_897942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897942).length < 2 ^ (prefixWord ++ tailWord_897942).sum := by decide
  have hdescent : baseEnd_897942 < baseStart_897942 := by decide
  rcases family_descends (prefixWord ++ tailWord_897942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898020 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_898020 : Nat := 118140960795 + 898020 * 2 ^ 59
def prefixEnd_898020 : Nat := 4983230072969 + 3 ^ 40 * 898020 * 2
def baseEnd_898020 : Nat := 461115897350681726320087

theorem tailTrace_898020 : CollatzResearch.WordTrace tailWord_898020 prefixEnd_898020 461115897350681726320087 := by
  unfold tailWord_898020
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376740103317192225365757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21835653471089589633821009 16376740103317192225365757)
  ·
    refine ⟨6141277538743947084512159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16376740103317192225365757 6141277538743947084512159)
    ·
      refine ⟨9211916308115920626768239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6141277538743947084512159 9211916308115920626768239)
      ·
        refine ⟨13817874462173880940152359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211916308115920626768239 13817874462173880940152359)
        ·
          refine ⟨20726811693260821410228539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817874462173880940152359 20726811693260821410228539)
          ·
            refine ⟨31090217539891232115342809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726811693260821410228539 31090217539891232115342809)
            ·
              refine ⟨23317663154918424086507107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31090217539891232115342809 23317663154918424086507107)
              ·
                refine ⟨34976494732377636129760661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23317663154918424086507107 34976494732377636129760661)
                ·
                  refine ⟨1639523190580201693582531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34976494732377636129760661 1639523190580201693582531)
                  ·
                    refine ⟨2459284785870302540373797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1639523190580201693582531 2459284785870302540373797)
                    ·
                      refine ⟨461115897350681726320087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2459284785870302540373797 461115897350681726320087)
                      ·
                        rfl

theorem cell23_898020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_898020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898020 prefixEnd_898020 := by exact prefixLift 898020
  have htrace : WordTrace (prefixWord ++ tailWord_898020) baseStart_898020 baseEnd_898020 := by
    simpa [prefixWord, tailWord_898020, baseEnd_898020] using wordTrace_append hprefix tailTrace_898020
  have hstable : (prefixWord ++ tailWord_898020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898020).length < 2 ^ (prefixWord ++ tailWord_898020).sum := by decide
  have hdescent : baseEnd_898020 < baseStart_898020 := by decide
  rcases family_descends (prefixWord ++ tailWord_898020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898060 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 8]
def baseStart_898060 : Nat := 118140960795 + 898060 * 2 ^ 59
def prefixEnd_898060 : Nat := 4983230072969 + 3 ^ 40 * 898060 * 2
def baseEnd_898060 : Nat := 51237381841873507757767

theorem tailTrace_898060 : CollatzResearch.WordTrace tailWord_898060 prefixEnd_898060 51237381841873507757767 := by
  unfold tailWord_898060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377469563244735641093817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21836626084326314188125089 16377469563244735641093817)
  ·
    refine ⟨12283102172433551730820363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16377469563244735641093817 12283102172433551730820363)
    ·
      refine ⟨18424653258650327596230545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283102172433551730820363 18424653258650327596230545)
      ·
        refine ⟨13818489943987745697172909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18424653258650327596230545 13818489943987745697172909)
        ·
          refine ⟨5181933728995404636439841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13818489943987745697172909 5181933728995404636439841)
          ·
            refine ⟨3886450296746553477329881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181933728995404636439841 3886450296746553477329881)
            ·
              refine ⟨2914837722559915107997411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886450296746553477329881 2914837722559915107997411)
              ·
                refine ⟨4372256583839872661996117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914837722559915107997411 4372256583839872661996117)
                ·
                  refine ⟨51237381841873507757767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4372256583839872661996117 51237381841873507757767)
                  ·
                    rfl

theorem cell23_898060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_898060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898060 prefixEnd_898060 := by exact prefixLift 898060
  have htrace : WordTrace (prefixWord ++ tailWord_898060) baseStart_898060 baseEnd_898060 := by
    simpa [prefixWord, tailWord_898060, baseEnd_898060] using wordTrace_append hprefix tailTrace_898060
  have hstable : (prefixWord ++ tailWord_898060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898060).length < 2 ^ (prefixWord ++ tailWord_898060).sum := by decide
  have hdescent : baseEnd_898060 < baseStart_898060 := by decide
  rcases family_descends (prefixWord ++ tailWord_898060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898120 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_898120 : Nat := 118140960795 + 898120 * 2 ^ 59
def prefixEnd_898120 : Nat := 4983230072969 + 3 ^ 40 * 898120 * 2
def baseEnd_898120 : Nat := 153722415138710445023209

theorem tailTrace_898120 : CollatzResearch.WordTrace tailWord_898120 prefixEnd_898120 153722415138710445023209 := by
  unfold tailWord_898120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378563753136050764685907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21838085004181401019581209 16378563753136050764685907)
  ·
    refine ⟨24567845629704076147028861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378563753136050764685907 24567845629704076147028861)
    ·
      refine ⟨9212942111139028555135823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24567845629704076147028861 9212942111139028555135823)
      ·
        refine ⟨13819413166708542832703735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212942111139028555135823 13819413166708542832703735)
        ·
          refine ⟨20729119750062814249055603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819413166708542832703735 20729119750062814249055603)
          ·
            refine ⟨31093679625094221373583405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20729119750062814249055603 31093679625094221373583405)
            ·
              refine ⟨11660129859410333015093777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31093679625094221373583405 11660129859410333015093777)
              ·
                refine ⟨8745097394557749761320333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11660129859410333015093777 8745097394557749761320333)
                ·
                  refine ⟨3279411522959156160495125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8745097394557749761320333 3279411522959156160495125)
                  ·
                    refine ⟨153722415138710445023209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3279411522959156160495125 153722415138710445023209)
                    ·
                      rfl

theorem cell23_898120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_898120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898120 prefixEnd_898120 := by exact prefixLift 898120
  have htrace : WordTrace (prefixWord ++ tailWord_898120) baseStart_898120 baseEnd_898120 := by
    simpa [prefixWord, tailWord_898120, baseEnd_898120] using wordTrace_append hprefix tailTrace_898120
  have hstable : (prefixWord ++ tailWord_898120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898120).length < 2 ^ (prefixWord ++ tailWord_898120).sum := by decide
  have hdescent : baseEnd_898120 < baseStart_898120 := by decide
  rcases family_descends (prefixWord ++ tailWord_898120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898247 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_898247 : Nat := 118140960795 + 898247 * 2 ^ 59
def prefixEnd_898247 : Nat := 4983230072969 + 3 ^ 40 * 898247 * 2
def baseEnd_898247 : Nat := 461232457459252338181543

theorem tailTrace_898247 : CollatzResearch.WordTrace tailWord_898247 prefixEnd_898247 461232457459252338181543 := by
  unfold tailWord_898247
  simp only [CollatzResearch.WordTrace]
  refine ⟨32761759576812002219244995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21841173051208001479496663 32761759576812002219244995)
  ·
    refine ⟨49142639365218003328867493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32761759576812002219244995 49142639365218003328867493)
    ·
      refine ⟨9214244880978375624162655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49142639365218003328867493 9214244880978375624162655)
      ·
        refine ⟨13821367321467563436243983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214244880978375624162655 13821367321467563436243983)
        ·
          refine ⟨20732050982201345154365975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13821367321467563436243983 20732050982201345154365975)
          ·
            refine ⟨31098076473302017731548963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20732050982201345154365975 31098076473302017731548963)
            ·
              refine ⟨46647114709953026597323445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31098076473302017731548963 46647114709953026597323445)
              ·
                refine ⟨4373167004058096243499073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46647114709953026597323445 4373167004058096243499073)
                ·
                  refine ⟨3279875253043572182624305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373167004058096243499073 3279875253043572182624305)
                  ·
                    refine ⟨2459906439782679136968229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3279875253043572182624305 2459906439782679136968229)
                    ·
                      refine ⟨461232457459252338181543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2459906439782679136968229 461232457459252338181543)
                      ·
                        rfl

theorem cell23_898247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_898247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898247 prefixEnd_898247 := by exact prefixLift 898247
  have htrace : WordTrace (prefixWord ++ tailWord_898247) baseStart_898247 baseEnd_898247 := by
    simpa [prefixWord, tailWord_898247, baseEnd_898247] using wordTrace_append hprefix tailTrace_898247
  have hstable : (prefixWord ++ tailWord_898247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898247).length < 2 ^ (prefixWord ++ tailWord_898247).sum := by decide
  have hdescent : baseEnd_898247 < baseStart_898247 := by decide
  rcases family_descends (prefixWord ++ tailWord_898247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898285 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_898285 : Nat := 118140960795 + 898285 * 2 ^ 59
def prefixEnd_898285 : Nat := 4983230072969 + 3 ^ 40 * 898285 * 2
def baseEnd_898285 : Nat := 461251969724123189506369

theorem tailTrace_898285 : CollatzResearch.WordTrace tailWord_898285 prefixEnd_898285 461251969724123189506369 := by
  unfold tailWord_898285
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763145550674334709128309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842097033782889806085539 32763145550674334709128309)
  ·
    refine ⟨3071544895375718878980779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32763145550674334709128309 3071544895375718878980779)
    ·
      refine ⟨4607317343063578318471169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071544895375718878980779 4607317343063578318471169)
      ·
        refine ⟨3455488007297683738853377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4607317343063578318471169 3455488007297683738853377)
        ·
          refine ⟨2591616005473262804140033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455488007297683738853377 2591616005473262804140033)
          ·
            refine ⟨1943712004104947103105025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2591616005473262804140033 1943712004104947103105025)
            ·
              refine ⟨1457784003078710327328769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943712004104947103105025 1457784003078710327328769)
              ·
                refine ⟨1093338002309032745496577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457784003078710327328769 1093338002309032745496577)
                ·
                  refine ⟨820003501731774559122433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1093338002309032745496577 820003501731774559122433)
                  ·
                    refine ⟨615002626298830919341825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 820003501731774559122433 615002626298830919341825)
                    ·
                      refine ⟨461251969724123189506369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615002626298830919341825 461251969724123189506369)
                      ·
                        rfl

theorem cell23_898285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_898285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898285 prefixEnd_898285 := by exact prefixLift 898285
  have htrace : WordTrace (prefixWord ++ tailWord_898285) baseStart_898285 baseEnd_898285 := by
    simpa [prefixWord, tailWord_898285, baseEnd_898285] using wordTrace_append hprefix tailTrace_898285
  have hstable : (prefixWord ++ tailWord_898285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898285).length < 2 ^ (prefixWord ++ tailWord_898285).sum := by decide
  have hdescent : baseEnd_898285 < baseStart_898285 := by decide
  rcases family_descends (prefixWord ++ tailWord_898285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898291 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 5]
def baseStart_898291 : Nat := 118140960795 + 898291 * 2 ^ 59
def prefixEnd_898291 : Nat := 4983230072969 + 3 ^ 40 * 898291 * 2
def baseEnd_898291 : Nat := 51250561178672240670149

theorem tailTrace_898291 : CollatzResearch.WordTrace tailWord_898291 prefixEnd_898291 51250561178672240670149 := by
  unfold tailWord_898291
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763364388652597733846727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842242925768398489231151 32763364388652597733846727)
  ·
    refine ⟨49145046582978896600770091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763364388652597733846727 49145046582978896600770091)
    ·
      refine ⟨73717569874468344901155137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49145046582978896600770091 73717569874468344901155137)
      ·
        refine ⟨55288177405851258675866353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73717569874468344901155137 55288177405851258675866353)
        ·
          refine ⟨41466133054388444006899765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55288177405851258675866353 41466133054388444006899765)
          ·
            refine ⟨3887449973848916625646853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41466133054388444006899765 3887449973848916625646853)
            ·
              refine ⟨728896870096671867308785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3887449973848916625646853 728896870096671867308785)
              ·
                refine ⟨546672652572503900481589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728896870096671867308785 546672652572503900481589)
                ·
                  refine ⟨51250561178672240670149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 546672652572503900481589 51250561178672240670149)
                  ·
                    rfl

theorem cell23_898291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 5].length) (baseStart_898291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898291 prefixEnd_898291 := by exact prefixLift 898291
  have htrace : WordTrace (prefixWord ++ tailWord_898291) baseStart_898291 baseEnd_898291 := by
    simpa [prefixWord, tailWord_898291, baseEnd_898291] using wordTrace_append hprefix tailTrace_898291
  have hstable : (prefixWord ++ tailWord_898291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898291).length < 2 ^ (prefixWord ++ tailWord_898291).sum := by decide
  have hdescent : baseEnd_898291 < baseStart_898291 := by decide
  rcases family_descends (prefixWord ++ tailWord_898291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898297 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_898297 : Nat := 118140960795 + 898297 * 2 ^ 59
def prefixEnd_898297 : Nat := 4983230072969 + 3 ^ 40 * 898297 * 2
def baseEnd_898297 : Nat := 461258131491977142556313

theorem tailTrace_898297 : CollatzResearch.WordTrace tailWord_898297 prefixEnd_898297 461258131491977142556313 := by
  unfold tailWord_898297
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763583226630860758565145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842388817753907172376763 32763583226630860758565145)
  ·
    refine ⟨24572687419973145568923859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32763583226630860758565145 24572687419973145568923859)
    ·
      refine ⟨36859031129959718353385789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24572687419973145568923859 36859031129959718353385789)
      ·
        refine ⟨13822136673734894382519671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36859031129959718353385789 13822136673734894382519671)
        ·
          refine ⟨20733205010602341573779507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13822136673734894382519671 20733205010602341573779507)
          ·
            refine ⟨31099807515903512360669261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20733205010602341573779507 31099807515903512360669261)
            ·
              refine ⟨11662427818463817135250973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31099807515903512360669261 11662427818463817135250973)
              ·
                refine ⟨4373410431923931425719115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11662427818463817135250973 4373410431923931425719115)
                ·
                  refine ⟨6560115647885897138578673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373410431923931425719115 6560115647885897138578673)
                  ·
                    refine ⟨4920086735914422853934005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6560115647885897138578673 4920086735914422853934005)
                    ·
                      refine ⟨461258131491977142556313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4920086735914422853934005 461258131491977142556313)
                      ·
                        rfl

theorem cell23_898297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_898297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898297 prefixEnd_898297 := by exact prefixLift 898297
  have htrace : WordTrace (prefixWord ++ tailWord_898297) baseStart_898297 baseEnd_898297 := by
    simpa [prefixWord, tailWord_898297, baseEnd_898297] using wordTrace_append hprefix tailTrace_898297
  have hstable : (prefixWord ++ tailWord_898297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898297).length < 2 ^ (prefixWord ++ tailWord_898297).sum := by decide
  have hdescent : baseEnd_898297 < baseStart_898297 := by decide
  rcases family_descends (prefixWord ++ tailWord_898297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898341 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_898341 : Nat := 118140960795 + 898341 * 2 ^ 59
def prefixEnd_898341 : Nat := 4983230072969 + 3 ^ 40 * 898341 * 2
def baseEnd_898341 : Nat := 461280724640774970406111

theorem tailTrace_898341 : CollatzResearch.WordTrace tailWord_898341 prefixEnd_898341 461280724640774970406111 := by
  unfold tailWord_898341
  simp only [CollatzResearch.WordTrace]
  refine ⟨32765188038471456273166877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21843458692314304182111251 32765188038471456273166877)
  ·
    refine ⟨12286945514426796102437579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32765188038471456273166877 12286945514426796102437579)
    ·
      refine ⟨18430418271640194153656369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12286945514426796102437579 18430418271640194153656369)
      ·
        refine ⟨13822813703730145615242277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18430418271640194153656369 13822813703730145615242277)
        ·
          refine ⟨2591777569449402302857927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13822813703730145615242277 2591777569449402302857927)
          ·
            refine ⟨3887666354174103454286891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591777569449402302857927 3887666354174103454286891)
            ·
              refine ⟨5831499531261155181430337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887666354174103454286891 5831499531261155181430337)
              ·
                refine ⟨4373624648445866386072753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831499531261155181430337 4373624648445866386072753)
                ·
                  refine ⟨3280218486334399789554565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373624648445866386072753 3280218486334399789554565)
                  ·
                    refine ⟨615040966187699960541481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3280218486334399789554565 615040966187699960541481)
                    ·
                      refine ⟨461280724640774970406111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615040966187699960541481 461280724640774970406111)
                      ·
                        rfl

theorem cell23_898341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_898341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898341 prefixEnd_898341 := by exact prefixLift 898341
  have htrace : WordTrace (prefixWord ++ tailWord_898341) baseStart_898341 baseEnd_898341 := by
    simpa [prefixWord, tailWord_898341, baseEnd_898341] using wordTrace_append hprefix tailTrace_898341
  have hstable : (prefixWord ++ tailWord_898341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898341).length < 2 ^ (prefixWord ++ tailWord_898341).sum := by decide
  have hdescent : baseEnd_898341 < baseStart_898341 := by decide
  rcases family_descends (prefixWord ++ tailWord_898341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898441 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_898441 : Nat := 118140960795 + 898441 * 2 ^ 59
def prefixEnd_898441 : Nat := 4983230072969 + 3 ^ 40 * 898441 * 2
def baseEnd_898441 : Nat := 153777357568741526385217

theorem tailTrace_898441 : CollatzResearch.WordTrace tailWord_898441 prefixEnd_898441 153777357568741526385217 := by
  unfold tailWord_898441
  simp only [CollatzResearch.WordTrace]
  refine ⟨32768835338109173351807177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21845890225406115567871451 32768835338109173351807177)
  ·
    refine ⟨24576626503581880013855383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32768835338109173351807177 24576626503581880013855383)
    ·
      refine ⟨36864939755372820020783075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24576626503581880013855383 36864939755372820020783075)
      ·
        refine ⟨55297409633059230031174613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36864939755372820020783075 55297409633059230031174613)
        ·
          refine ⟨1296033038274825703855655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 55297409633059230031174613 1296033038274825703855655)
          ·
            refine ⟨1944049557412238555783483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296033038274825703855655 1944049557412238555783483)
            ·
              refine ⟨2916074336118357833675225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944049557412238555783483 2916074336118357833675225)
              ·
                refine ⟨2187055752088768375256419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2916074336118357833675225 2187055752088768375256419)
                ·
                  refine ⟨3280583628133152562884629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187055752088768375256419 3280583628133152562884629)
                  ·
                    refine ⟨153777357568741526385217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3280583628133152562884629 153777357568741526385217)
                    ·
                      rfl

theorem cell23_898441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_898441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898441 prefixEnd_898441 := by exact prefixLift 898441
  have htrace : WordTrace (prefixWord ++ tailWord_898441) baseStart_898441 baseEnd_898441 := by
    simpa [prefixWord, tailWord_898441, baseEnd_898441] using wordTrace_append hprefix tailTrace_898441
  have hstable : (prefixWord ++ tailWord_898441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898441).length < 2 ^ (prefixWord ++ tailWord_898441).sum := by decide
  have hdescent : baseEnd_898441 < baseStart_898441 := by decide
  rcases family_descends (prefixWord ++ tailWord_898441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898458 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_898458 : Nat := 118140960795 + 898458 * 2 ^ 59
def prefixEnd_898458 : Nat := 4983230072969 + 3 ^ 40 * 898458 * 2
def baseEnd_898458 : Nat := 153780267292450337547691

theorem tailTrace_898458 : CollatzResearch.WordTrace tailWord_898458 prefixEnd_898458 153780267292450337547691 := by
  unfold tailWord_898458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192363844761896313794007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21846303586031723503450685 8192363844761896313794007)
  ·
    refine ⟨12288545767142844470691011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192363844761896313794007 12288545767142844470691011)
    ·
      refine ⟨18432818650714266706036517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288545767142844470691011 18432818650714266706036517)
      ·
        refine ⟨3456153497008925007381847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18432818650714266706036517 3456153497008925007381847)
        ·
          refine ⟨5184230245513387511072771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456153497008925007381847 5184230245513387511072771)
          ·
            refine ⟨7776345368270081266609157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5184230245513387511072771 7776345368270081266609157)
            ·
              refine ⟨1458064756550640237489217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7776345368270081266609157 1458064756550640237489217)
              ·
                refine ⟨1093548567412980178116913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458064756550640237489217 1093548567412980178116913)
                ·
                  refine ⟨820161425559735133587685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1093548567412980178116913 820161425559735133587685)
                  ·
                    refine ⟨153780267292450337547691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820161425559735133587685 153780267292450337547691)
                    ·
                      rfl

theorem cell23_898458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_898458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898458 prefixEnd_898458 := by exact prefixLift 898458
  have htrace : WordTrace (prefixWord ++ tailWord_898458) baseStart_898458 baseEnd_898458 := by
    simpa [prefixWord, tailWord_898458, baseEnd_898458] using wordTrace_append hprefix tailTrace_898458
  have hstable : (prefixWord ++ tailWord_898458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898458).length < 2 ^ (prefixWord ++ tailWord_898458).sum := by decide
  have hdescent : baseEnd_898458 < baseStart_898458 := by decide
  rcases family_descends (prefixWord ++ tailWord_898458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898531 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 6]
def baseStart_898531 : Nat := 118140960795 + 898531 * 2 ^ 59
def prefixEnd_898531 : Nat := 4983230072969 + 3 ^ 40 * 898531 * 2
def baseEnd_898531 : Nat := 153792761988376409010079

theorem tailTrace_898531 : CollatzResearch.WordTrace tailWord_898531 prefixEnd_898531 153792761988376409010079 := by
  unfold tailWord_898531
  simp only [CollatzResearch.WordTrace]
  refine ⟨32772117907783118722583447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21848078605188745815055631 32772117907783118722583447)
  ·
    refine ⟨49158176861674678083875171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32772117907783118722583447 49158176861674678083875171)
    ·
      refine ⟨73737265292512017125812757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49158176861674678083875171 73737265292512017125812757)
      ·
        refine ⟨3456434310586500802772473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73737265292512017125812757 3456434310586500802772473)
        ·
          refine ⟨2592325732939875602079355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456434310586500802772473 2592325732939875602079355)
          ·
            refine ⟨3888488599409813403119033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592325732939875602079355 3888488599409813403119033)
            ·
              refine ⟨2916366449557360052339275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888488599409813403119033 2916366449557360052339275)
              ·
                refine ⟨4374549674336040078508913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916366449557360052339275 4374549674336040078508913)
                ·
                  refine ⟨3280912255752030058881685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374549674336040078508913 3280912255752030058881685)
                  ·
                    refine ⟨153792761988376409010079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3280912255752030058881685 153792761988376409010079)
                    ·
                      rfl

theorem cell23_898531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_898531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898531 prefixEnd_898531 := by exact prefixLift 898531
  have htrace : WordTrace (prefixWord ++ tailWord_898531) baseStart_898531 baseEnd_898531 := by
    simpa [prefixWord, tailWord_898531, baseEnd_898531] using wordTrace_append hprefix tailTrace_898531
  have hstable : (prefixWord ++ tailWord_898531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898531).length < 2 ^ (prefixWord ++ tailWord_898531).sum := by decide
  have hdescent : baseEnd_898531 < baseStart_898531 := by decide
  rcases family_descends (prefixWord ++ tailWord_898531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898638 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_898638 : Nat := 118140960795 + 898638 * 2 ^ 59
def prefixEnd_898638 : Nat := 4983230072969 + 3 ^ 40 * 898638 * 2
def baseEnd_898638 : Nat := 153811076131720102797415

theorem tailTrace_898638 : CollatzResearch.WordTrace tailWord_898638 prefixEnd_898638 153811076131720102797415 := by
  unfold tailWord_898638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097002564799434499591071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21850680345596983997819045 4097002564799434499591071)
  ·
    refine ⟨6145503847199151749386607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097002564799434499591071 6145503847199151749386607)
    ·
      refine ⟨9218255770798727624079911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145503847199151749386607 9218255770798727624079911)
      ·
        refine ⟨13827383656198091436119867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218255770798727624079911 13827383656198091436119867)
        ·
          refine ⟨20741075484297137154179801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13827383656198091436119867 20741075484297137154179801)
          ·
            refine ⟨15555806613222852865634851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20741075484297137154179801 15555806613222852865634851)
            ·
              refine ⟨23333709919834279298452277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555806613222852865634851 23333709919834279298452277)
              ·
                refine ⟨2187535304984463684229901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23333709919834279298452277 2187535304984463684229901)
                ·
                  refine ⟨820325739369173881586213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2187535304984463684229901 820325739369173881586213)
                  ·
                    refine ⟨153811076131720102797415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820325739369173881586213 153811076131720102797415)
                    ·
                      rfl

theorem cell23_898638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_898638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898638 prefixEnd_898638 := by exact prefixLift 898638
  have htrace : WordTrace (prefixWord ++ tailWord_898638) baseStart_898638 baseEnd_898638 := by
    simpa [prefixWord, tailWord_898638, baseEnd_898638] using wordTrace_append hprefix tailTrace_898638
  have hstable : (prefixWord ++ tailWord_898638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898638).length < 2 ^ (prefixWord ++ tailWord_898638).sum := by decide
  have hdescent : baseEnd_898638 < baseStart_898638 := by decide
  rcases family_descends (prefixWord ++ tailWord_898638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898672 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 1, 4]
def baseStart_898672 : Nat := 118140960795 + 898672 * 2 ^ 59
def prefixEnd_898672 : Nat := 4983230072969 + 3 ^ 40 * 898672 * 2
def baseEnd_898672 : Nat := 153816895579137725122363

theorem tailTrace_898672 : CollatzResearch.WordTrace tailWord_898672 prefixEnd_898672 153816895579137725122363 := by
  unfold tailWord_898672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388630300136149901733135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21851507066848199868977513 16388630300136149901733135)
  ·
    refine ⟨24582945450204224852599703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16388630300136149901733135 24582945450204224852599703)
    ·
      refine ⟨36874418175306337278899555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24582945450204224852599703 36874418175306337278899555)
      ·
        refine ⟨55311627262959505918349333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36874418175306337278899555 55311627262959505918349333)
        ·
          refine ⟨2592732527951226839922625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55311627262959505918349333 2592732527951226839922625)
          ·
            refine ⟨1944549395963420129941969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592732527951226839922625 1944549395963420129941969)
            ·
              refine ⟨1458412046972565097456477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944549395963420129941969 1458412046972565097456477)
              ·
                refine ⟨546904517614711911546179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458412046972565097456477 546904517614711911546179)
                ·
                  refine ⟨820356776422067867319269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546904517614711911546179 820356776422067867319269)
                  ·
                    refine ⟨153816895579137725122363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820356776422067867319269 153816895579137725122363)
                    ·
                      rfl

theorem cell23_898672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_898672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898672 prefixEnd_898672 := by exact prefixLift 898672
  have htrace : WordTrace (prefixWord ++ tailWord_898672) baseStart_898672 baseEnd_898672 := by
    simpa [prefixWord, tailWord_898672, baseEnd_898672] using wordTrace_append hprefix tailTrace_898672
  have hstable : (prefixWord ++ tailWord_898672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898672).length < 2 ^ (prefixWord ++ tailWord_898672).sum := by decide
  have hdescent : baseEnd_898672 < baseStart_898672 := by decide
  rcases family_descends (prefixWord ++ tailWord_898672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898685 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 6]
def baseStart_898685 : Nat := 118140960795 + 898685 * 2 ^ 59
def prefixEnd_898685 : Nat := 4983230072969 + 3 ^ 40 * 898685 * 2
def baseEnd_898685 : Nat := 51273040220657958278281

theorem tailTrace_898685 : CollatzResearch.WordTrace tailWord_898685 prefixEnd_898685 51273040220657958278281 := by
  unfold tailWord_898685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32777734749225203023689509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21851823166150135349126339 32777734749225203023689509)
  ·
    refine ⟨6145825265479725566941783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32777734749225203023689509 6145825265479725566941783)
    ·
      refine ⟨9218737898219588350412675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145825265479725566941783 9218737898219588350412675)
      ·
        refine ⟨13828106847329382525619013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9218737898219588350412675 13828106847329382525619013)
        ·
          refine ⟨2592770033874259223553565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13828106847329382525619013 2592770033874259223553565)
          ·
            refine ⟨972288762702847208832587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2592770033874259223553565 972288762702847208832587)
            ·
              refine ⟨1458433144054270813248881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972288762702847208832587 1458433144054270813248881)
              ·
                refine ⟨1093824858040703109936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458433144054270813248881 1093824858040703109936661)
                ·
                  refine ⟨51273040220657958278281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1093824858040703109936661 51273040220657958278281)
                  ·
                    rfl

theorem cell23_898685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_898685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898685 prefixEnd_898685 := by exact prefixLift 898685
  have htrace : WordTrace (prefixWord ++ tailWord_898685) baseStart_898685 baseEnd_898685 := by
    simpa [prefixWord, tailWord_898685, baseEnd_898685] using wordTrace_append hprefix tailTrace_898685
  have hstable : (prefixWord ++ tailWord_898685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898685).length < 2 ^ (prefixWord ++ tailWord_898685).sum := by decide
  have hdescent : baseEnd_898685 < baseStart_898685 := by decide
  rcases family_descends (prefixWord ++ tailWord_898685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898695 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_898695 : Nat := 118140960795 + 898695 * 2 ^ 59
def prefixEnd_898695 : Nat := 4983230072969 + 3 ^ 40 * 898695 * 2
def baseEnd_898695 : Nat := 461462496792466585379483

theorem tailTrace_898695 : CollatzResearch.WordTrace tailWord_898695 prefixEnd_898695 461462496792466585379483 := by
  unfold tailWord_898695
  simp only [CollatzResearch.WordTrace]
  refine ⟨32778099479188974731553539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21852066319459316487702359 32778099479188974731553539)
  ·
    refine ⟨49167149218783462097330309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32778099479188974731553539 49167149218783462097330309)
    ·
      refine ⟨9218840478521899143249433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49167149218783462097330309 9218840478521899143249433)
      ·
        refine ⟨6914130358891424357437075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9218840478521899143249433 6914130358891424357437075)
        ·
          refine ⟨10371195538337136536155613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914130358891424357437075 10371195538337136536155613)
          ·
            refine ⟨3889198326876426201058355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10371195538337136536155613 3889198326876426201058355)
            ·
              refine ⟨5833797490314639301587533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889198326876426201058355 5833797490314639301587533)
              ·
                refine ⟨2187674058867989738095325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5833797490314639301587533 2187674058867989738095325)
                ·
                  refine ⟨820377772075496151785747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2187674058867989738095325 820377772075496151785747)
                  ·
                    refine ⟨1230566658113244227678621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820377772075496151785747 1230566658113244227678621)
                    ·
                      refine ⟨461462496792466585379483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1230566658113244227678621 461462496792466585379483)
                      ·
                        rfl

theorem cell23_898695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_898695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898695 prefixEnd_898695 := by exact prefixLift 898695
  have htrace : WordTrace (prefixWord ++ tailWord_898695) baseStart_898695 baseEnd_898695 := by
    simpa [prefixWord, tailWord_898695, baseEnd_898695] using wordTrace_append hprefix tailTrace_898695
  have hstable : (prefixWord ++ tailWord_898695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898695).length < 2 ^ (prefixWord ++ tailWord_898695).sum := by decide
  have hdescent : baseEnd_898695 < baseStart_898695 := by decide
  rcases family_descends (prefixWord ++ tailWord_898695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898738 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_898738 : Nat := 118140960795 + 898738 * 2 ^ 59
def prefixEnd_898738 : Nat := 4983230072969 + 3 ^ 40 * 898738 * 2
def baseEnd_898738 : Nat := 461484576460609917141785

theorem tailTrace_898738 : CollatzResearch.WordTrace tailWord_898738 prefixEnd_898738 461484576460609917141785 := by
  unfold tailWord_898738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8194916954508298268842217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21853111878688795383579245 8194916954508298268842217)
  ·
    refine ⟨6146187715881223701631663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8194916954508298268842217 6146187715881223701631663)
    ·
      refine ⟨9219281573821835552447495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146187715881223701631663 9219281573821835552447495)
      ·
        refine ⟨13828922360732753328671243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219281573821835552447495 13828922360732753328671243)
        ·
          refine ⟨20743383541099129993006865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13828922360732753328671243 20743383541099129993006865)
          ·
            refine ⟨15557537655824347494755149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20743383541099129993006865 15557537655824347494755149)
            ·
              refine ⟨5834076620934130310533181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15557537655824347494755149 5834076620934130310533181)
              ·
                refine ⟨2187778732850298866449943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5834076620934130310533181 2187778732850298866449943)
                ·
                  refine ⟨3281668099275448299674915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187778732850298866449943 3281668099275448299674915)
                  ·
                    refine ⟨4922502148913172449512373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281668099275448299674915 4922502148913172449512373)
                    ·
                      refine ⟨461484576460609917141785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4922502148913172449512373 461484576460609917141785)
                      ·
                        rfl

theorem cell23_898738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_898738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898738 prefixEnd_898738 := by exact prefixLift 898738
  have htrace : WordTrace (prefixWord ++ tailWord_898738) baseStart_898738 baseEnd_898738 := by
    simpa [prefixWord, tailWord_898738, baseEnd_898738] using wordTrace_append hprefix tailTrace_898738
  have hstable : (prefixWord ++ tailWord_898738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898738).length < 2 ^ (prefixWord ++ tailWord_898738).sum := by decide
  have hdescent : baseEnd_898738 < baseStart_898738 := by decide
  rcases family_descends (prefixWord ++ tailWord_898738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898748 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_898748 : Nat := 118140960795 + 898748 * 2 ^ 59
def prefixEnd_898748 : Nat := 4983230072969 + 3 ^ 40 * 898748 * 2
def baseEnd_898748 : Nat := 461489711267154878016739

theorem tailTrace_898748 : CollatzResearch.WordTrace tailWord_898748 prefixEnd_898748 461489711267154878016739 := by
  unfold tailWord_898748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390016273998482391616449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21853355031997976522155265 16390016273998482391616449)
  ·
    refine ⟨12292512205498861793712337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16390016273998482391616449 12292512205498861793712337)
    ·
      refine ⟨9219384154124146345284253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292512205498861793712337 9219384154124146345284253)
      ·
        refine ⟨3457269057796554879481595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9219384154124146345284253 3457269057796554879481595)
        ·
          refine ⟨5185903586694832319222393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457269057796554879481595 5185903586694832319222393)
          ·
            refine ⟨3889427690021124239416795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185903586694832319222393 3889427690021124239416795)
            ·
              refine ⟨5834141535031686359125193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889427690021124239416795 5834141535031686359125193)
              ·
                refine ⟨4375606151273764769343895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5834141535031686359125193 4375606151273764769343895)
                ·
                  refine ⟨6563409226910647154015843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375606151273764769343895 6563409226910647154015843)
                  ·
                    refine ⟨9845113840365970731023765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6563409226910647154015843 9845113840365970731023765)
                    ·
                      refine ⟨461489711267154878016739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9845113840365970731023765 461489711267154878016739)
                      ·
                        rfl

theorem cell23_898748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_898748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898748 prefixEnd_898748 := by exact prefixLift 898748
  have htrace : WordTrace (prefixWord ++ tailWord_898748) baseStart_898748 baseEnd_898748 := by
    simpa [prefixWord, tailWord_898748, baseEnd_898748] using wordTrace_append hprefix tailTrace_898748
  have hstable : (prefixWord ++ tailWord_898748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898748).length < 2 ^ (prefixWord ++ tailWord_898748).sum := by decide
  have hdescent : baseEnd_898748 < baseStart_898748 := by decide
  rcases family_descends (prefixWord ++ tailWord_898748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898762 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_898762 : Nat := 118140960795 + 898762 * 2 ^ 59
def prefixEnd_898762 : Nat := 4983230072969 + 3 ^ 40 * 898762 * 2
def baseEnd_898762 : Nat := 153832299998772607747225

theorem tailTrace_898762 : CollatzResearch.WordTrace tailWord_898762 prefixEnd_898762 153832299998772607747225 := by
  unfold tailWord_898762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195135792486561293560635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21853695446630830116161693 8195135792486561293560635)
  ·
    refine ⟨12292703688729841940340953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195135792486561293560635 12292703688729841940340953)
    ·
      refine ⟨9219527766547381455255715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12292703688729841940340953 9219527766547381455255715)
      ·
        refine ⟨13829291649821072182883573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9219527766547381455255715 13829291649821072182883573)
        ·
          refine ⟨1296496092170725517145335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13829291649821072182883573 1296496092170725517145335)
          ·
            refine ⟨1944744138256088275718003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296496092170725517145335 1944744138256088275718003)
            ·
              refine ⟨2917116207384132413577005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944744138256088275718003 2917116207384132413577005)
              ·
                refine ⟨1093918577769049655091377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2917116207384132413577005 1093918577769049655091377)
                ·
                  refine ⟨820438933326787241318533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1093918577769049655091377 820438933326787241318533)
                  ·
                    refine ⟨153832299998772607747225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820438933326787241318533 153832299998772607747225)
                    ·
                      rfl

theorem cell23_898762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_898762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898762 prefixEnd_898762 := by exact prefixLift 898762
  have htrace : WordTrace (prefixWord ++ tailWord_898762) baseStart_898762 baseEnd_898762 := by
    simpa [prefixWord, tailWord_898762, baseEnd_898762] using wordTrace_append hprefix tailTrace_898762
  have hstable : (prefixWord ++ tailWord_898762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898762).length < 2 ^ (prefixWord ++ tailWord_898762).sum := by decide
  have hdescent : baseEnd_898762 < baseStart_898762 := by decide
  rcases family_descends (prefixWord ++ tailWord_898762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898772 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_898772 : Nat := 118140960795 + 898772 * 2 ^ 59
def prefixEnd_898772 : Nat := 4983230072969 + 3 ^ 40 * 898772 * 2
def baseEnd_898772 : Nat := 461502034802862784116629

theorem tailTrace_898772 : CollatzResearch.WordTrace tailWord_898772 prefixEnd_898772 461502034802862784116629 := by
  unfold tailWord_898772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390453949955008441053285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21853938599940011254737713 16390453949955008441053285)
  ·
    refine ⟨3073210115616564082697491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16390453949955008441053285 3073210115616564082697491)
    ·
      refine ⟨4609815173424846124046237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073210115616564082697491 4609815173424846124046237)
      ·
        refine ⟨1728680690034317296517339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4609815173424846124046237 1728680690034317296517339)
        ·
          refine ⟨2593021035051475944776009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728680690034317296517339 2593021035051475944776009)
          ·
            refine ⟨1944765776288606958582007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593021035051475944776009 1944765776288606958582007)
            ·
              refine ⟨2917148664432910437873011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944765776288606958582007 2917148664432910437873011)
              ·
                refine ⟨4375722996649365656809517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917148664432910437873011 4375722996649365656809517)
                ·
                  refine ⟨1640896123743512121303569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4375722996649365656809517 1640896123743512121303569)
                  ·
                    refine ⟨1230672092807634090977677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1640896123743512121303569 1230672092807634090977677)
                    ·
                      refine ⟨461502034802862784116629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1230672092807634090977677 461502034802862784116629)
                      ·
                        rfl

theorem cell23_898772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_898772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898772 prefixEnd_898772 := by exact prefixLift 898772
  have htrace : WordTrace (prefixWord ++ tailWord_898772) baseStart_898772 baseEnd_898772 := by
    simpa [prefixWord, tailWord_898772, baseEnd_898772] using wordTrace_append hprefix tailTrace_898772
  have hstable : (prefixWord ++ tailWord_898772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898772).length < 2 ^ (prefixWord ++ tailWord_898772).sum := by decide
  have hdescent : baseEnd_898772 < baseStart_898772 := by decide
  rcases family_descends (prefixWord ++ tailWord_898772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898828 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_898828 : Nat := 118140960795 + 898828 * 2 ^ 59
def prefixEnd_898828 : Nat := 4983230072969 + 3 ^ 40 * 898828 * 2
def baseEnd_898828 : Nat := 461530789719514565016371

theorem tailTrace_898828 : CollatzResearch.WordTrace tailWord_898828 prefixEnd_898828 461530789719514565016371 := by
  unfold tailWord_898828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391475193853569223072569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21855300258471425630763425 16391475193853569223072569)
  ·
    refine ⟨12293606395390176917304427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16391475193853569223072569 12293606395390176917304427)
    ·
      refine ⟨18440409593085265375956641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12293606395390176917304427 18440409593085265375956641)
      ·
        refine ⟨13830307194813949031967481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18440409593085265375956641 13830307194813949031967481)
        ·
          refine ⟨10372730396110461773975611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13830307194813949031967481 10372730396110461773975611)
          ·
            refine ⟨15559095594165692660963417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10372730396110461773975611 15559095594165692660963417)
            ·
              refine ⟨11669321695624269495722563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15559095594165692660963417 11669321695624269495722563)
              ·
                refine ⟨17503982543436404243583845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11669321695624269495722563 17503982543436404243583845)
                ·
                  refine ⟨3281996726894325795671971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17503982543436404243583845 3281996726894325795671971)
                  ·
                    refine ⟨4922995090341488693507957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281996726894325795671971 4922995090341488693507957)
                    ·
                      refine ⟨461530789719514565016371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4922995090341488693507957 461530789719514565016371)
                      ·
                        rfl

theorem cell23_898828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_898828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898828 prefixEnd_898828 := by exact prefixLift 898828
  have htrace : WordTrace (prefixWord ++ tailWord_898828) baseStart_898828 baseEnd_898828 := by
    simpa [prefixWord, tailWord_898828, baseEnd_898828] using wordTrace_append hprefix tailTrace_898828
  have hstable : (prefixWord ++ tailWord_898828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898828).length < 2 ^ (prefixWord ++ tailWord_898828).sum := by decide
  have hdescent : baseEnd_898828 < baseStart_898828 := by decide
  rcases family_descends (prefixWord ++ tailWord_898828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898842 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_898842 : Nat := 118140960795 + 898842 * 2 ^ 59
def prefixEnd_898842 : Nat := 4983230072969 + 3 ^ 40 * 898842 * 2
def baseEnd_898842 : Nat := 461537978448677510241307

theorem tailTrace_898842 : CollatzResearch.WordTrace tailWord_898842 prefixEnd_898842 461537978448677510241307 := by
  unfold tailWord_898842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195865252414104709288695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21855640673104279224769853 8195865252414104709288695)
  ·
    refine ⟨12293797878621157063933043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195865252414104709288695 12293797878621157063933043)
    ·
      refine ⟨18440696817931735595899565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12293797878621157063933043 18440696817931735595899565)
      ·
        refine ⟨6915261306724400848462337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18440696817931735595899565 6915261306724400848462337)
        ·
          refine ⟨5186445980043300636346753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915261306724400848462337 5186445980043300636346753)
          ·
            refine ⟨3889834485032475477260065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5186445980043300636346753 3889834485032475477260065)
            ·
              refine ⟨2917375863774356607945049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889834485032475477260065 2917375863774356607945049)
              ·
                refine ⟨2188031897830767455958787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917375863774356607945049 2188031897830767455958787)
                ·
                  refine ⟨3282047846746151183938181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188031897830767455958787 3282047846746151183938181)
                  ·
                    refine ⟨615383971264903346988409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3282047846746151183938181 615383971264903346988409)
                    ·
                      refine ⟨461537978448677510241307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615383971264903346988409 461537978448677510241307)
                      ·
                        rfl

theorem cell23_898842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_898842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898842 prefixEnd_898842 := by exact prefixLift 898842
  have htrace : WordTrace (prefixWord ++ tailWord_898842) baseStart_898842 baseEnd_898842 := by
    simpa [prefixWord, tailWord_898842, baseEnd_898842] using wordTrace_append hprefix tailTrace_898842
  have hstable : (prefixWord ++ tailWord_898842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898842).length < 2 ^ (prefixWord ++ tailWord_898842).sum := by decide
  have hdescent : baseEnd_898842 < baseStart_898842 := by decide
  rcases family_descends (prefixWord ++ tailWord_898842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898848 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 9]
def baseStart_898848 : Nat := 118140960795 + 898848 * 2 ^ 59
def prefixEnd_898848 : Nat := 4983230072969 + 3 ^ 40 * 898848 * 2
def baseEnd_898848 : Nat := 51282339925844942974031

theorem tailTrace_898848 : CollatzResearch.WordTrace tailWord_898848 prefixEnd_898848 51282339925844942974031 := by
  unfold tailWord_898848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391839923817340930936599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21855786565089787907915465 16391839923817340930936599)
  ·
    refine ⟨24587759885726011396404899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16391839923817340930936599 24587759885726011396404899)
    ·
      refine ⟨36881639828589017094607349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24587759885726011396404899 36881639828589017094607349)
      ·
        refine ⟨3457653733930220352619439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36881639828589017094607349 3457653733930220352619439)
        ·
          refine ⟨5186480600895330528929159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457653733930220352619439 5186480600895330528929159)
          ·
            refine ⟨7779720901342995793393739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186480600895330528929159 7779720901342995793393739)
            ·
              refine ⟨11669581352014493690090609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7779720901342995793393739 11669581352014493690090609)
              ·
                refine ⟨8752186014010870267567957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11669581352014493690090609 8752186014010870267567957)
                ·
                  refine ⟨51282339925844942974031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8752186014010870267567957 51282339925844942974031)
                  ·
                    rfl

theorem cell23_898848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_898848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898848 prefixEnd_898848 := by exact prefixLift 898848
  have htrace : WordTrace (prefixWord ++ tailWord_898848) baseStart_898848 baseEnd_898848 := by
    simpa [prefixWord, tailWord_898848, baseEnd_898848] using wordTrace_append hprefix tailTrace_898848
  have hstable : (prefixWord ++ tailWord_898848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898848).length < 2 ^ (prefixWord ++ tailWord_898848).sum := by decide
  have hdescent : baseEnd_898848 < baseStart_898848 := by decide
  rcases family_descends (prefixWord ++ tailWord_898848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898865 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 7]
def baseStart_898865 : Nat := 118140960795 + 898865 * 2 ^ 59
def prefixEnd_898865 : Nat := 4983230072969 + 3 ^ 40 * 898865 * 2
def baseEnd_898865 : Nat := 51283309833747880028189

theorem tailTrace_898865 : CollatzResearch.WordTrace tailWord_898865 prefixEnd_898865 51283309833747880028189 := by
  unfold tailWord_898865
  simp only [CollatzResearch.WordTrace]
  refine ⟨32784299888573093765242049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21856199925715395843494699 32784299888573093765242049)
  ·
    refine ⟨24588224916429820323931537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32784299888573093765242049 24588224916429820323931537)
    ·
      refine ⟨18441168687322365242948653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24588224916429820323931537 18441168687322365242948653)
      ·
        refine ⟨6915438257745886966105745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18441168687322365242948653 6915438257745886966105745)
        ·
          refine ⟨5186578693309415224579309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6915438257745886966105745 5186578693309415224579309)
          ·
            refine ⟨1944967009991030709217241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5186578693309415224579309 1944967009991030709217241)
            ·
              refine ⟨1458725257493273031912931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944967009991030709217241 1458725257493273031912931)
              ·
                refine ⟨2188087886239909547869397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458725257493273031912931 2188087886239909547869397)
                ·
                  refine ⟨51283309833747880028189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2188087886239909547869397 51283309833747880028189)
                  ·
                    rfl

theorem cell23_898865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_898865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898865 prefixEnd_898865 := by exact prefixLift 898865
  have htrace : WordTrace (prefixWord ++ tailWord_898865) baseStart_898865 baseEnd_898865 := by
    simpa [prefixWord, tailWord_898865, baseEnd_898865] using wordTrace_append hprefix tailTrace_898865
  have hstable : (prefixWord ++ tailWord_898865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898865).length < 2 ^ (prefixWord ++ tailWord_898865).sum := by decide
  have hdescent : baseEnd_898865 < baseStart_898865 := by decide
  rcases family_descends (prefixWord ++ tailWord_898865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898972 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 6]
def baseStart_898972 : Nat := 118140960795 + 898972 * 2 ^ 59
def prefixEnd_898972 : Nat := 4983230072969 + 3 ^ 40 * 898972 * 2
def baseEnd_898972 : Nat := 51289414548195777957301

theorem tailTrace_898972 : CollatzResearch.WordTrace tailWord_898972 prefixEnd_898972 51289414548195777957301 := by
  unfold tailWord_898972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394101249592725519693585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21858801666123634026258113 16394101249592725519693585)
  ·
    refine ⟨12295575937194544139770189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16394101249592725519693585 12295575937194544139770189)
    ·
      refine ⟨4610840976447954052413821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12295575937194544139770189 4610840976447954052413821)
      ·
        refine ⟨1729065366167982769655183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4610840976447954052413821 1729065366167982769655183)
        ·
          refine ⟨2593598049251974154482775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729065366167982769655183 2593598049251974154482775)
          ·
            refine ⟨3890397073877961231724163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593598049251974154482775 3890397073877961231724163)
            ·
              refine ⟨5835595610816941847586245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890397073877961231724163 5835595610816941847586245)
              ·
                refine ⟨1094174177028176596422421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5835595610816941847586245 1094174177028176596422421)
                ·
                  refine ⟨51289414548195777957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1094174177028176596422421 51289414548195777957301)
                  ·
                    rfl

theorem cell23_898972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_898972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_898972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_898972 prefixEnd_898972 := by exact prefixLift 898972
  have htrace : WordTrace (prefixWord ++ tailWord_898972) baseStart_898972 baseEnd_898972 := by
    simpa [prefixWord, tailWord_898972, baseEnd_898972] using wordTrace_append hprefix tailTrace_898972
  have hstable : (prefixWord ++ tailWord_898972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898972).length < 2 ^ (prefixWord ++ tailWord_898972).sum := by decide
  have hdescent : baseEnd_898972 < baseStart_898972 := by decide
  rcases family_descends (prefixWord ++ tailWord_898972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899016 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_899016 : Nat := 118140960795 + 899016 * 2 ^ 59
def prefixEnd_899016 : Nat := 4983230072969 + 3 ^ 40 * 899016 * 2
def baseEnd_899016 : Nat := 461627324082559829465507

theorem tailTrace_899016 : CollatzResearch.WordTrace tailWord_899016 prefixEnd_899016 461627324082559829465507 := by
  unfold tailWord_899016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16394903655513023276994451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21859871540684031035992601 16394903655513023276994451)
  ·
    refine ⟨24592355483269534915491677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16394903655513023276994451 24592355483269534915491677)
    ·
      refine ⟨9222133306226075593309379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24592355483269534915491677 9222133306226075593309379)
      ·
        refine ⟨13833199959339113389964069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222133306226075593309379 13833199959339113389964069)
        ·
          refine ⟨2593724992376083760618263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13833199959339113389964069 2593724992376083760618263)
          ·
            refine ⟨3890587488564125640927395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593724992376083760618263 3890587488564125640927395)
            ·
              refine ⟨5835881232846188461391093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3890587488564125640927395 5835881232846188461391093)
              ·
                refine ⟨547113865579330168255415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5835881232846188461391093 547113865579330168255415)
                ·
                  refine ⟨820670798368995252383123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547113865579330168255415 820670798368995252383123)
                  ·
                    refine ⟨1231006197553492878574685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820670798368995252383123 1231006197553492878574685)
                    ·
                      refine ⟨461627324082559829465507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1231006197553492878574685 461627324082559829465507)
                      ·
                        rfl

theorem cell23_899016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_899016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899016 prefixEnd_899016 := by exact prefixLift 899016
  have htrace : WordTrace (prefixWord ++ tailWord_899016) baseStart_899016 baseEnd_899016 := by
    simpa [prefixWord, tailWord_899016, baseEnd_899016] using wordTrace_append hprefix tailTrace_899016
  have hstable : (prefixWord ++ tailWord_899016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899016).length < 2 ^ (prefixWord ++ tailWord_899016).sum := by decide
  have hdescent : baseEnd_899016 < baseStart_899016 := by decide
  rcases family_descends (prefixWord ++ tailWord_899016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899032 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_899032 : Nat := 118140960795 + 899032 * 2 ^ 59
def prefixEnd_899032 : Nat := 4983230072969 + 3 ^ 40 * 899032 * 2
def baseEnd_899032 : Nat := 153878513257677255621811

theorem tailTrace_899032 : CollatzResearch.WordTrace tailWord_899032 prefixEnd_899032 153878513257677255621811 := by
  unfold tailWord_899032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16395195439484040643285675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21860260585978720857714233 16395195439484040643285675)
  ·
    refine ⟨24592793159226060964928513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16395195439484040643285675 24592793159226060964928513)
    ·
      refine ⟨18444594869419545723696385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24592793159226060964928513 18444594869419545723696385)
      ·
        refine ⟨13833446152064659292772289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18444594869419545723696385 13833446152064659292772289)
        ·
          refine ⟨10375084614048494469579217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13833446152064659292772289 10375084614048494469579217)
          ·
            refine ⟨7781313460536370852184413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10375084614048494469579217 7781313460536370852184413)
            ·
              refine ⟨2917992547701139069569155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7781313460536370852184413 2917992547701139069569155)
              ·
                refine ⟨4376988821551708604353733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917992547701139069569155 4376988821551708604353733)
                ·
                  refine ⟨820685404040945363316325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4376988821551708604353733 820685404040945363316325)
                  ·
                    refine ⟨153878513257677255621811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 820685404040945363316325 153878513257677255621811)
                    ·
                      rfl

theorem cell23_899032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_899032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899032 prefixEnd_899032 := by exact prefixLift 899032
  have htrace : WordTrace (prefixWord ++ tailWord_899032) baseStart_899032 baseEnd_899032 := by
    simpa [prefixWord, tailWord_899032, baseEnd_899032] using wordTrace_append hprefix tailTrace_899032
  have hstable : (prefixWord ++ tailWord_899032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899032).length < 2 ^ (prefixWord ++ tailWord_899032).sum := by decide
  have hdescent : baseEnd_899032 < baseStart_899032 := by decide
  rcases family_descends (prefixWord ++ tailWord_899032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899076 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_899076 : Nat := 118140960795 + 899076 * 2 ^ 59
def prefixEnd_899076 : Nat := 4983230072969 + 3 ^ 40 * 899076 * 2
def baseEnd_899076 : Nat := 461658132921829594715231

theorem tailTrace_899076 : CollatzResearch.WordTrace tailWord_899076 prefixEnd_899076 461658132921829594715231 := by
  unfold tailWord_899076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16395997845404338400586541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21861330460539117867448721 16395997845404338400586541)
  ·
    refine ⟨6148499192026626900219953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16395997845404338400586541 6148499192026626900219953)
    ·
      refine ⟨4611374394019970175164965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6148499192026626900219953 4611374394019970175164965)
      ·
        refine ⟨864632698878744407843431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4611374394019970175164965 864632698878744407843431)
        ·
          refine ⟨1296949048318116611765147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864632698878744407843431 1296949048318116611765147)
          ·
            refine ⟨1945423572477174917647721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296949048318116611765147 1945423572477174917647721)
            ·
              refine ⟨1459067679357881188235791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945423572477174917647721 1459067679357881188235791)
              ·
                refine ⟨2188601519036821782353687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459067679357881188235791 2188601519036821782353687)
                ·
                  refine ⟨3282902278555232673530531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2188601519036821782353687 3282902278555232673530531)
                  ·
                    refine ⟨4924353417832849010295797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3282902278555232673530531 4924353417832849010295797)
                    ·
                      refine ⟨461658132921829594715231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4924353417832849010295797 461658132921829594715231)
                      ·
                        rfl

theorem cell23_899076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_899076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899076 prefixEnd_899076 := by exact prefixLift 899076
  have htrace : WordTrace (prefixWord ++ tailWord_899076) baseStart_899076 baseEnd_899076 := by
    simpa [prefixWord, tailWord_899076, baseEnd_899076] using wordTrace_append hprefix tailTrace_899076
  have hstable : (prefixWord ++ tailWord_899076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899076).length < 2 ^ (prefixWord ++ tailWord_899076).sum := by decide
  have hdescent : baseEnd_899076 < baseStart_899076 := by decide
  rcases family_descends (prefixWord ++ tailWord_899076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899106 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_899106 : Nat := 118140960795 + 899106 * 2 ^ 59
def prefixEnd_899106 : Nat := 4983230072969 + 3 ^ 40 * 899106 * 2
def baseEnd_899106 : Nat := 461673537341464477340093

theorem tailTrace_899106 : CollatzResearch.WordTrace tailWord_899106 prefixEnd_899106 461673537341464477340093 := by
  unfold tailWord_899106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8198272470174997981191293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21862059920466661283176781 8198272470174997981191293)
  ·
    refine ⟨3074352176315624242946735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8198272470174997981191293 3074352176315624242946735)
    ·
      refine ⟨4611528264473436364420103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3074352176315624242946735 4611528264473436364420103)
      ·
        refine ⟨6917292396710154546630155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611528264473436364420103 6917292396710154546630155)
        ·
          refine ⟨10375938595065231819945233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917292396710154546630155 10375938595065231819945233)
          ·
            refine ⟨7781953946298923864958925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10375938595065231819945233 7781953946298923864958925)
            ·
              refine ⟨2918232729862096449359597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7781953946298923864958925 2918232729862096449359597)
              ·
                refine ⟨1094337273698286168509849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2918232729862096449359597 1094337273698286168509849)
                ·
                  refine ⟨820752955273714626382387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1094337273698286168509849 820752955273714626382387)
                  ·
                    refine ⟨1231129432910571939573581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820752955273714626382387 1231129432910571939573581)
                    ·
                      refine ⟨461673537341464477340093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1231129432910571939573581 461673537341464477340093)
                      ·
                        rfl

theorem cell23_899106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_899106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899106 prefixEnd_899106 := by exact prefixLift 899106
  have htrace : WordTrace (prefixWord ++ tailWord_899106) baseStart_899106 baseEnd_899106 := by
    simpa [prefixWord, tailWord_899106, baseEnd_899106] using wordTrace_append hprefix tailTrace_899106
  have hstable : (prefixWord ++ tailWord_899106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899106).length < 2 ^ (prefixWord ++ tailWord_899106).sum := by decide
  have hdescent : baseEnd_899106 < baseStart_899106 := by decide
  rcases family_descends (prefixWord ++ tailWord_899106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899132 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_899132 : Nat := 118140960795 + 899132 * 2 ^ 59
def prefixEnd_899132 : Nat := 4983230072969 + 3 ^ 40 * 899132 * 2
def baseEnd_899132 : Nat := 461686887838481375614973

theorem tailTrace_899132 : CollatzResearch.WordTrace tailWord_899132 prefixEnd_899132 461686887838481375614973 := by
  unfold tailWord_899132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397019089302899182605825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21862692119070532243474433 16397019089302899182605825)
  ·
    refine ⟨12297764316977174386954369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16397019089302899182605825 12297764316977174386954369)
    ·
      refine ⟨9223323237732880790215777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12297764316977174386954369 9223323237732880790215777)
      ·
        refine ⟨6917492428299660592661833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223323237732880790215777 6917492428299660592661833)
        ·
          refine ⟨5188119321224745444496375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6917492428299660592661833 5188119321224745444496375)
          ·
            refine ⟨7782178981837118166744563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188119321224745444496375 7782178981837118166744563)
            ·
              refine ⟨11673268472755677250116845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782178981837118166744563 11673268472755677250116845)
              ·
                refine ⟨4377475677283378968793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11673268472755677250116845 4377475677283378968793817)
                ·
                  refine ⟨3283106757962534226595363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4377475677283378968793817 3283106757962534226595363)
                  ·
                    refine ⟨4924660136943801339893045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283106757962534226595363 4924660136943801339893045)
                    ·
                      refine ⟨461686887838481375614973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4924660136943801339893045 461686887838481375614973)
                      ·
                        rfl

theorem cell23_899132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_899132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899132 prefixEnd_899132 := by exact prefixLift 899132
  have htrace : WordTrace (prefixWord ++ tailWord_899132) baseStart_899132 baseEnd_899132 := by
    simpa [prefixWord, tailWord_899132, baseEnd_899132] using wordTrace_append hprefix tailTrace_899132
  have hstable : (prefixWord ++ tailWord_899132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899132).length < 2 ^ (prefixWord ++ tailWord_899132).sum := by decide
  have hdescent : baseEnd_899132 < baseStart_899132 := by decide
  rcases family_descends (prefixWord ++ tailWord_899132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899133 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_899133 : Nat := 118140960795 + 899133 * 2 ^ 59
def prefixEnd_899133 : Nat := 4983230072969 + 3 ^ 40 * 899133 * 2
def baseEnd_899133 : Nat := 461687401319135871702469

theorem tailTrace_899133 : CollatzResearch.WordTrace tailWord_899133 prefixEnd_899133 461687401319135871702469 := by
  unfold tailWord_899133
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794074651602175535998053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21862716434401450357332035 32794074651602175535998053)
  ·
    refine ⟨6148888997175407912999635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32794074651602175535998053 6148888997175407912999635)
    ·
      refine ⟨9223333495763111869499453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148888997175407912999635 9223333495763111869499453)
      ·
        refine ⟨3458750060911166951062295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9223333495763111869499453 3458750060911166951062295)
        ·
          refine ⟨5188125091366750426593443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458750060911166951062295 5188125091366750426593443)
          ·
            refine ⟨7782187637050125639890165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188125091366750426593443 7782187637050125639890165)
            ·
              refine ⟨729580090973449278739703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7782187637050125639890165 729580090973449278739703)
              ·
                refine ⟨1094370136460173918109555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729580090973449278739703 1094370136460173918109555)
                ·
                  refine ⟨1641555204690260877164333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094370136460173918109555 1641555204690260877164333)
                  ·
                    refine ⟨615583201758847828936625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1641555204690260877164333 615583201758847828936625)
                    ·
                      refine ⟨461687401319135871702469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615583201758847828936625 461687401319135871702469)
                      ·
                        rfl

theorem cell23_899133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_899133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899133 prefixEnd_899133 := by exact prefixLift 899133
  have htrace : WordTrace (prefixWord ++ tailWord_899133) baseStart_899133 baseEnd_899133 := by
    simpa [prefixWord, tailWord_899133, baseEnd_899133] using wordTrace_append hprefix tailTrace_899133
  have hstable : (prefixWord ++ tailWord_899133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899133).length < 2 ^ (prefixWord ++ tailWord_899133).sum := by decide
  have hdescent : baseEnd_899133 < baseStart_899133 := by decide
  rcases family_descends (prefixWord ++ tailWord_899133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899149 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_899149 : Nat := 118140960795 + 899149 * 2 ^ 59
def prefixEnd_899149 : Nat := 4983230072969 + 3 ^ 40 * 899149 * 2
def baseEnd_899149 : Nat := 461695617009607809102395

theorem tailTrace_899149 : CollatzResearch.WordTrace tailWord_899149 prefixEnd_899149 461695617009607809102395 := by
  unfold tailWord_899149
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794658219544210268580501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863105479696140179053667 32794658219544210268580501)
  ·
    refine ⟨1537249604041134856339711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32794658219544210268580501 1537249604041134856339711)
    ·
      refine ⟨2305874406061702284509567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537249604041134856339711 2305874406061702284509567)
      ·
        refine ⟨3458811609092553426764351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2305874406061702284509567 3458811609092553426764351)
        ·
          refine ⟨5188217413638830140146527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3458811609092553426764351 5188217413638830140146527)
          ·
            refine ⟨7782326120458245210219791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5188217413638830140146527 7782326120458245210219791)
            ·
              refine ⟨11673489180687367815329687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7782326120458245210219791 11673489180687367815329687)
              ·
                refine ⟨17510233771031051722994531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11673489180687367815329687 17510233771031051722994531)
                ·
                  refine ⟨26265350656546577584491797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17510233771031051722994531 26265350656546577584491797)
                  ·
                    refine ⟨1231188312025620824273053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26265350656546577584491797 1231188312025620824273053)
                    ·
                      refine ⟨461695617009607809102395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1231188312025620824273053 461695617009607809102395)
                      ·
                        rfl

theorem cell23_899149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_899149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899149 prefixEnd_899149 := by exact prefixLift 899149
  have htrace : WordTrace (prefixWord ++ tailWord_899149) baseStart_899149 baseEnd_899149 := by
    simpa [prefixWord, tailWord_899149, baseEnd_899149] using wordTrace_append hprefix tailTrace_899149
  have hstable : (prefixWord ++ tailWord_899149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899149).length < 2 ^ (prefixWord ++ tailWord_899149).sum := by decide
  have hdescent : baseEnd_899149 < baseStart_899149 := by decide
  rcases family_descends (prefixWord ++ tailWord_899149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899186 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_899186 : Nat := 118140960795 + 899186 * 2 ^ 59
def prefixEnd_899186 : Nat := 4983230072969 + 3 ^ 40 * 899186 * 2
def baseEnd_899186 : Nat := 51301623977091573815525

theorem tailTrace_899186 : CollatzResearch.WordTrace tailWord_899186 prefixEnd_899186 51301623977091573815525 := by
  unfold tailWord_899186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8199001930102541396919353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21864005146940110391784941 8199001930102541396919353)
  ·
    refine ⟨6149251447576906047689515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8199001930102541396919353 6149251447576906047689515)
    ·
      refine ⟨9223877171365359071534273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149251447576906047689515 9223877171365359071534273)
      ·
        refine ⟨6917907878524019303650705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9223877171365359071534273 6917907878524019303650705)
        ·
          refine ⟨5188430908893014477738029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6917907878524019303650705 5188430908893014477738029)
          ·
            refine ⟨1945661590834880429151761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5188430908893014477738029 1945661590834880429151761)
            ·
              refine ⟨1459246193126160321863821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945661590834880429151761 1459246193126160321863821)
              ·
                refine ⟨547217322422310120698933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459246193126160321863821 547217322422310120698933)
                ·
                  refine ⟨51301623977091573815525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 547217322422310120698933 51301623977091573815525)
                  ·
                    rfl

theorem cell23_899186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_899186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899186 prefixEnd_899186 := by exact prefixLift 899186
  have htrace : WordTrace (prefixWord ++ tailWord_899186) baseStart_899186 baseEnd_899186 := by
    simpa [prefixWord, tailWord_899186, baseEnd_899186] using wordTrace_append hprefix tailTrace_899186
  have hstable : (prefixWord ++ tailWord_899186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899186).length < 2 ^ (prefixWord ++ tailWord_899186).sum := by decide
  have hdescent : baseEnd_899186 < baseStart_899186 := by decide
  rcases family_descends (prefixWord ++ tailWord_899186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899253 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_899253 : Nat := 118140960795 + 899253 * 2 ^ 59
def prefixEnd_899253 : Nat := 4983230072969 + 3 ^ 40 * 899253 * 2
def baseEnd_899253 : Nat := 461749018997675402201917

theorem tailTrace_899253 : CollatzResearch.WordTrace tailWord_899253 prefixEnd_899253 461749018997675402201917 := by
  unfold tailWord_899253
  simp only [CollatzResearch.WordTrace]
  refine ⟨32798451411167436030366413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21865634274111624020244275 32798451411167436030366413)
  ·
    refine ⟨12299419279187788511387405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32798451411167436030366413 12299419279187788511387405)
    ·
      refine ⟨4612282229695420691770277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12299419279187788511387405 4612282229695420691770277)
      ·
        refine ⟨864802918067891379706927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4612282229695420691770277 864802918067891379706927)
        ·
          refine ⟨1297204377101837069560391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864802918067891379706927 1297204377101837069560391)
          ·
            refine ⟨1945806565652755604340587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297204377101837069560391 1945806565652755604340587)
            ·
              refine ⟨2918709848479133406510881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1945806565652755604340587 2918709848479133406510881)
              ·
                refine ⟨2189032386359350054883161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918709848479133406510881 2189032386359350054883161)
                ·
                  refine ⟨1641774289769512541162371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189032386359350054883161 1641774289769512541162371)
                  ·
                    refine ⟨2462661434654268811743557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641774289769512541162371 2462661434654268811743557)
                    ·
                      refine ⟨461749018997675402201917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2462661434654268811743557 461749018997675402201917)
                      ·
                        rfl

theorem cell23_899253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_899253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899253 prefixEnd_899253 := by exact prefixLift 899253
  have htrace : WordTrace (prefixWord ++ tailWord_899253) baseStart_899253 baseEnd_899253 := by
    simpa [prefixWord, tailWord_899253, baseEnd_899253] using wordTrace_append hprefix tailTrace_899253
  have hstable : (prefixWord ++ tailWord_899253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899253).length < 2 ^ (prefixWord ++ tailWord_899253).sum := by decide
  have hdescent : baseEnd_899253 < baseStart_899253 := by decide
  rcases family_descends (prefixWord ++ tailWord_899253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899272 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_899272 : Nat := 118140960795 + 899272 * 2 ^ 59
def prefixEnd_899272 : Nat := 4983230072969 + 3 ^ 40 * 899272 * 2
def baseEnd_899272 : Nat := 153919591710036942621443

theorem tailTrace_899272 : CollatzResearch.WordTrace tailWord_899272 prefixEnd_899272 153919591710036942621443 := by
  unfold tailWord_899272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399572199049301137654035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21866096265399068183538713 16399572199049301137654035)
  ·
    refine ⟨24599358298573951706481053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16399572199049301137654035 24599358298573951706481053)
    ·
      refine ⟨9224759361965231889930395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24599358298573951706481053 9224759361965231889930395)
      ·
        refine ⟨13837139042947847834895593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9224759361965231889930395 13837139042947847834895593)
        ·
          refine ⟨10377854282210885876171695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13837139042947847834895593 10377854282210885876171695)
          ·
            refine ⟨15566781423316328814257543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377854282210885876171695 15566781423316328814257543)
            ·
              refine ⟨23350172134974493221386315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15566781423316328814257543 23350172134974493221386315)
              ·
                refine ⟨35025258202461739832079473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23350172134974493221386315 35025258202461739832079473)
                ·
                  refine ⟨26268943651846304874059605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35025258202461739832079473 26268943651846304874059605)
                  ·
                    refine ⟨153919591710036942621443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26268943651846304874059605 153919591710036942621443)
                    ·
                      rfl

theorem cell23_899272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_899272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899272 prefixEnd_899272 := by exact prefixLift 899272
  have htrace : WordTrace (prefixWord ++ tailWord_899272) baseStart_899272 baseEnd_899272 := by
    simpa [prefixWord, tailWord_899272, baseEnd_899272] using wordTrace_append hprefix tailTrace_899272
  have hstable : (prefixWord ++ tailWord_899272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899272).length < 2 ^ (prefixWord ++ tailWord_899272).sum := by decide
  have hdescent : baseEnd_899272 < baseStart_899272 := by decide
  rcases family_descends (prefixWord ++ tailWord_899272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899326 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_899326 : Nat := 118140960795 + 899326 * 2 ^ 59
def prefixEnd_899326 : Nat := 4983230072969 + 3 ^ 40 * 899326 * 2
def baseEnd_899326 : Nat := 461786503085453616589081

theorem tailTrace_899326 : CollatzResearch.WordTrace tailWord_899326 prefixEnd_899326 461786503085453616589081 := by
  unfold tailWord_899326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100139242487871187221729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21867409293268646331849221 4100139242487871187221729)
  ·
    refine ⟨3075104431865903390416297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4100139242487871187221729 3075104431865903390416297)
    ·
      refine ⟨2306328323899427542812223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3075104431865903390416297 2306328323899427542812223)
      ·
        refine ⟨3459492485849141314218335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306328323899427542812223 3459492485849141314218335)
        ·
          refine ⟨5189238728773711971327503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3459492485849141314218335 5189238728773711971327503)
          ·
            refine ⟨7783858093160567956991255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5189238728773711971327503 7783858093160567956991255)
            ·
              refine ⟨11675787139740851935486883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7783858093160567956991255 11675787139740851935486883)
              ·
                refine ⟨17513680709611277903230325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11675787139740851935486883 17513680709611277903230325)
                ·
                  refine ⟨1641907566526057303427843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17513680709611277903230325 1641907566526057303427843)
                  ·
                    refine ⟨2462861349789085955141765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641907566526057303427843 2462861349789085955141765)
                    ·
                      refine ⟨461786503085453616589081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2462861349789085955141765 461786503085453616589081)
                      ·
                        rfl

theorem cell23_899326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_899326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899326 prefixEnd_899326 := by exact prefixLift 899326
  have htrace : WordTrace (prefixWord ++ tailWord_899326) baseStart_899326 baseEnd_899326 := by
    simpa [prefixWord, tailWord_899326, baseEnd_899326] using wordTrace_append hprefix tailTrace_899326
  have hstable : (prefixWord ++ tailWord_899326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899326).length < 2 ^ (prefixWord ++ tailWord_899326).sum := by decide
  have hdescent : baseEnd_899326 < baseStart_899326 := by decide
  rcases family_descends (prefixWord ++ tailWord_899326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899329 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_899329 : Nat := 118140960795 + 899329 * 2 ^ 59
def prefixEnd_899329 : Nat := 4983230072969 + 3 ^ 40 * 899329 * 2
def baseEnd_899329 : Nat := 461788043527417104851567

theorem tailTrace_899329 : CollatzResearch.WordTrace tailWord_899329 prefixEnd_899329 461788043527417104851567 := by
  unfold tailWord_899329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32801223358892101010133041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21867482239261400673422027 32801223358892101010133041)
  ·
    refine ⟨24600917519169075757599781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32801223358892101010133041 24600917519169075757599781)
    ·
      refine ⟨4612672034844201704549959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24600917519169075757599781 4612672034844201704549959)
      ·
        refine ⟨6919008052266302556824939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612672034844201704549959 6919008052266302556824939)
        ·
          refine ⟨10378512078399453835237409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919008052266302556824939 10378512078399453835237409)
          ·
            refine ⟨7783884058799590376428057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10378512078399453835237409 7783884058799590376428057)
            ·
              refine ⟨5837913044099692782321043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7783884058799590376428057 5837913044099692782321043)
              ·
                refine ⟨8756869566149539173481565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5837913044099692782321043 8756869566149539173481565)
                ·
                  refine ⟨3283826087306077190055587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8756869566149539173481565 3283826087306077190055587)
                  ·
                    refine ⟨4925739130959115785083381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283826087306077190055587 4925739130959115785083381)
                    ·
                      refine ⟨461788043527417104851567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4925739130959115785083381 461788043527417104851567)
                      ·
                        rfl

theorem cell23_899329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_899329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899329 prefixEnd_899329 := by exact prefixLift 899329
  have htrace : WordTrace (prefixWord ++ tailWord_899329) baseStart_899329 baseEnd_899329 := by
    simpa [prefixWord, tailWord_899329, baseEnd_899329] using wordTrace_append hprefix tailTrace_899329
  have hstable : (prefixWord ++ tailWord_899329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899329).length < 2 ^ (prefixWord ++ tailWord_899329).sum := by decide
  have hdescent : baseEnd_899329 < baseStart_899329 := by decide
  rcases family_descends (prefixWord ++ tailWord_899329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899336 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_899336 : Nat := 118140960795 + 899336 * 2 ^ 59
def prefixEnd_899336 : Nat := 4983230072969 + 3 ^ 40 * 899336 * 2
def baseEnd_899336 : Nat := 153930545963999525821345

theorem tailTrace_899336 : CollatzResearch.WordTrace tailWord_899336 prefixEnd_899336 153930545963999525821345 := by
  unfold tailWord_899336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400739334933370602818931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21867652446577827470425241 16400739334933370602818931)
  ·
    refine ⟨24601109002400055904228397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16400739334933370602818931 24601109002400055904228397)
    ·
      refine ⟨9225415875900020964085649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24601109002400055904228397 9225415875900020964085649)
      ·
        refine ⟨6919061906925015723064237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9225415875900020964085649 6919061906925015723064237)
        ·
          refine ⟨2594648215096880896149089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6919061906925015723064237 2594648215096880896149089)
          ·
            refine ⟨1945986161322660672111817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594648215096880896149089 1945986161322660672111817)
            ·
              refine ⟨1459489620991995504083863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945986161322660672111817 1459489620991995504083863)
              ·
                refine ⟨2189234431487993256125795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459489620991995504083863 2189234431487993256125795)
                ·
                  refine ⟨3283851647231989884188693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189234431487993256125795 3283851647231989884188693)
                  ·
                    refine ⟨153930545963999525821345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3283851647231989884188693 153930545963999525821345)
                    ·
                      rfl

theorem cell23_899336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_899336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899336 prefixEnd_899336 := by exact prefixLift 899336
  have htrace : WordTrace (prefixWord ++ tailWord_899336) baseStart_899336 baseEnd_899336 := by
    simpa [prefixWord, tailWord_899336, baseEnd_899336] using wordTrace_append hprefix tailTrace_899336
  have hstable : (prefixWord ++ tailWord_899336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899336).length < 2 ^ (prefixWord ++ tailWord_899336).sum := by decide
  have hdescent : baseEnd_899336 < baseStart_899336 := by decide
  rcases family_descends (prefixWord ++ tailWord_899336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899357 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_899357 : Nat := 118140960795 + 899357 * 2 ^ 59
def prefixEnd_899357 : Nat := 4983230072969 + 3 ^ 40 * 899357 * 2
def baseEnd_899357 : Nat := 153934140328580998433813

theorem tailTrace_899357 : CollatzResearch.WordTrace tailWord_899357 prefixEnd_899357 153934140328580998433813 := by
  unfold tailWord_899357
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802244602790661792152325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21868163068527107861434883 32802244602790661792152325)
  ·
    refine ⟨6150420863023249086028561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32802244602790661792152325 6150420863023249086028561)
    ·
      refine ⟨4612815647267436814521421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6150420863023249086028561 4612815647267436814521421)
      ·
        refine ⟨1729805867725288805445533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4612815647267436814521421 1729805867725288805445533)
        ·
          refine ⟨648677200396983302042075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1729805867725288805445533 648677200396983302042075)
          ·
            refine ⟨973015800595474953063113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648677200396983302042075 973015800595474953063113)
            ·
              refine ⟨729761850446606214797335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973015800595474953063113 729761850446606214797335)
              ·
                refine ⟨1094642775669909322196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729761850446606214797335 1094642775669909322196003)
                ·
                  refine ⟨1641964163504863983294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094642775669909322196003 1641964163504863983294005)
                  ·
                    refine ⟨153934140328580998433813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1641964163504863983294005 153934140328580998433813)
                    ·
                      rfl

theorem cell23_899357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_899357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899357 prefixEnd_899357 := by exact prefixLift 899357
  have htrace : WordTrace (prefixWord ++ tailWord_899357) baseStart_899357 baseEnd_899357 := by
    simpa [prefixWord, tailWord_899357, baseEnd_899357] using wordTrace_append hprefix tailTrace_899357
  have hstable : (prefixWord ++ tailWord_899357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899357).length < 2 ^ (prefixWord ++ tailWord_899357).sum := by decide
  have hdescent : baseEnd_899357 < baseStart_899357 := by decide
  rcases family_descends (prefixWord ++ tailWord_899357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899360 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4]
def baseStart_899360 : Nat := 118140960795 + 899360 * 2 ^ 59
def prefixEnd_899360 : Nat := 4983230072969 + 3 ^ 40 * 899360 * 2
def baseEnd_899360 : Nat := 461803961427706483563925

theorem tailTrace_899360 : CollatzResearch.WordTrace tailWord_899360 prefixEnd_899360 461803961427706483563925 := by
  unfold tailWord_899360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401177010889896652255767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21868236014519862203007689 16401177010889896652255767)
  ·
    refine ⟨24601765516334844978383651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16401177010889896652255767 24601765516334844978383651)
    ·
      refine ⟨36902648274502267467575477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24601765516334844978383651 36902648274502267467575477)
      ·
        refine ⟨3459623275734587575085201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36902648274502267467575477 3459623275734587575085201)
        ·
          refine ⟨2594717456800940681313901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459623275734587575085201 2594717456800940681313901)
          ·
            refine ⟨973019046300352755492713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2594717456800940681313901 973019046300352755492713)
            ·
              refine ⟨729764284725264566619535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973019046300352755492713 729764284725264566619535)
              ·
                refine ⟨1094646427087896849929303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729764284725264566619535 1094646427087896849929303)
                ·
                  refine ⟨1641969640631845274893955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094646427087896849929303 1641969640631845274893955)
                  ·
                    refine ⟨2462954460947767912340933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641969640631845274893955 2462954460947767912340933)
                    ·
                      refine ⟨461803961427706483563925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2462954460947767912340933 461803961427706483563925)
                      ·
                        rfl

theorem cell23_899360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_899360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899360 prefixEnd_899360 := by exact prefixLift 899360
  have htrace : WordTrace (prefixWord ++ tailWord_899360) baseStart_899360 baseEnd_899360 := by
    simpa [prefixWord, tailWord_899360, baseEnd_899360] using wordTrace_append hprefix tailTrace_899360
  have hstable : (prefixWord ++ tailWord_899360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899360).length < 2 ^ (prefixWord ++ tailWord_899360).sum := by decide
  have hdescent : baseEnd_899360 < baseStart_899360 := by decide
  rcases family_descends (prefixWord ++ tailWord_899360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899433 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 4, 2, 2]
def baseStart_899433 : Nat := 118140960795 + 899433 * 2 ^ 59
def prefixEnd_899433 : Nat := 4983230072969 + 3 ^ 40 * 899433 * 2
def baseEnd_899433 : Nat := 461841445515484697951089

theorem tailTrace_899433 : CollatzResearch.WordTrace tailWord_899433 prefixEnd_899433 461841445515484697951089 := by
  unfold tailWord_899433
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805016550515326771918953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21870011033676884514612635 32805016550515326771918953)
  ·
    refine ⟨24603762412886495078939215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32805016550515326771918953 24603762412886495078939215)
    ·
      refine ⟨36905643619329742618408823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24603762412886495078939215 36905643619329742618408823)
      ·
        refine ⟨55358465428994613927613235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36905643619329742618408823 55358465428994613927613235)
        ·
          refine ⟨83037698143491920891419853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55358465428994613927613235 83037698143491920891419853)
          ·
            refine ⟨31139136803809470334282445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83037698143491920891419853 31139136803809470334282445)
            ·
              refine ⟨11677176301428551375355917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31139136803809470334282445 11677176301428551375355917)
              ·
                refine ⟨4378941113035706765758469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11677176301428551375355917 4378941113035706765758469)
                ·
                  refine ⟨821051458694195018579713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4378941113035706765758469 821051458694195018579713)
                  ·
                    refine ⟨615788594020646263934785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821051458694195018579713 615788594020646263934785)
                    ·
                      refine ⟨461841445515484697951089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615788594020646263934785 461841445515484697951089)
                      ·
                        rfl

theorem cell23_899433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 2, 2].length) (baseStart_899433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899433 prefixEnd_899433 := by exact prefixLift 899433
  have htrace : WordTrace (prefixWord ++ tailWord_899433) baseStart_899433 baseEnd_899433 := by
    simpa [prefixWord, tailWord_899433, baseEnd_899433] using wordTrace_append hprefix tailTrace_899433
  have hstable : (prefixWord ++ tailWord_899433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899433).length < 2 ^ (prefixWord ++ tailWord_899433).sum := by decide
  have hdescent : baseEnd_899433 < baseStart_899433 := by decide
  rcases family_descends (prefixWord ++ tailWord_899433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899439 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 7]
def baseStart_899439 : Nat := 118140960795 + 899439 * 2 ^ 59
def prefixEnd_899439 : Nat := 4983230072969 + 3 ^ 40 * 899439 * 2
def baseEnd_899439 : Nat := 51316058488823519386229

theorem tailTrace_899439 : CollatzResearch.WordTrace tailWord_899439 prefixEnd_899439 51316058488823519386229 := by
  unfold tailWord_899439
  simp only [CollatzResearch.WordTrace]
  refine ⟨32805235388493589796637371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21870156925662393197758247 32805235388493589796637371)
  ·
    refine ⟨49207853082740384694956057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32805235388493589796637371 49207853082740384694956057)
    ·
      refine ⟨36905889812055288521217043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49207853082740384694956057 36905889812055288521217043)
      ·
        refine ⟨55358834718082932781825565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36905889812055288521217043 55358834718082932781825565)
        ·
          refine ⟨20759563019281099793184587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55358834718082932781825565 20759563019281099793184587)
          ·
            refine ⟨31139344528921649689776881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20759563019281099793184587 31139344528921649689776881)
            ·
              refine ⟨23354508396691237267332661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31139344528921649689776881 23354508396691237267332661)
              ·
                refine ⟨2189485162189803493812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23354508396691237267332661 2189485162189803493812437)
                ·
                  refine ⟨51316058488823519386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2189485162189803493812437 51316058488823519386229)
                  ·
                    rfl

theorem cell23_899439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 7].length) (baseStart_899439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899439 prefixEnd_899439 := by exact prefixLift 899439
  have htrace : WordTrace (prefixWord ++ tailWord_899439) baseStart_899439 baseEnd_899439 := by
    simpa [prefixWord, tailWord_899439, baseEnd_899439] using wordTrace_append hprefix tailTrace_899439
  have hstable : (prefixWord ++ tailWord_899439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899439).length < 2 ^ (prefixWord ++ tailWord_899439).sum := by decide
  have hdescent : baseEnd_899439 < baseStart_899439 := by decide
  rcases family_descends (prefixWord ++ tailWord_899439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899506 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_899506 : Nat := 118140960795 + 899506 * 2 ^ 59
def prefixEnd_899506 : Nat := 4983230072969 + 3 ^ 40 * 899506 * 2
def baseEnd_899506 : Nat := 461878929603262912338253

theorem tailTrace_899506 : CollatzResearch.WordTrace tailWord_899506 prefixEnd_899506 461878929603262912338253 := by
  unfold tailWord_899506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8201919769812715059831593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21871786052833906826217581 8201919769812715059831593)
  ·
    refine ⟨6151439827359536294873695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8201919769812715059831593 6151439827359536294873695)
    ·
      refine ⟨9227159741039304442310543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6151439827359536294873695 9227159741039304442310543)
      ·
        refine ⟨13840739611558956663465815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9227159741039304442310543 13840739611558956663465815)
        ·
          refine ⟨20761109417338434995198723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13840739611558956663465815 20761109417338434995198723)
          ·
            refine ⟨31141664126007652492798085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20761109417338434995198723 31141664126007652492798085)
            ·
              refine ⟨5839062023626434842399641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31141664126007652492798085 5839062023626434842399641)
              ·
                refine ⟨4379296517719826131799731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839062023626434842399641 4379296517719826131799731)
                ·
                  refine ⟨6568944776579739197699597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379296517719826131799731 6568944776579739197699597)
                  ·
                    refine ⟨2463354291217402199137349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6568944776579739197699597 2463354291217402199137349)
                    ·
                      refine ⟨461878929603262912338253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2463354291217402199137349 461878929603262912338253)
                      ·
                        rfl

theorem cell23_899506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_899506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899506 prefixEnd_899506 := by exact prefixLift 899506
  have htrace : WordTrace (prefixWord ++ tailWord_899506) baseStart_899506 baseEnd_899506 := by
    simpa [prefixWord, tailWord_899506, baseEnd_899506] using wordTrace_append hprefix tailTrace_899506
  have hstable : (prefixWord ++ tailWord_899506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899506).length < 2 ^ (prefixWord ++ tailWord_899506).sum := by decide
  have hdescent : baseEnd_899506 < baseStart_899506 := by decide
  rcases family_descends (prefixWord ++ tailWord_899506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899540 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_899540 : Nat := 118140960795 + 899540 * 2 ^ 59
def prefixEnd_899540 : Nat := 4983230072969 + 3 ^ 40 * 899540 * 2
def baseEnd_899540 : Nat := 461896387945515779313097

theorem tailTrace_899540 : CollatzResearch.WordTrace tailWord_899540 prefixEnd_899540 461896387945515779313097 := by
  unfold tailWord_899540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404459580563842023032037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21872612774085122697376049 16404459580563842023032037)
  ·
    refine ⟨3075836171355720379318507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16404459580563842023032037 3075836171355720379318507)
    ·
      refine ⟨4613754257033580568977761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075836171355720379318507 4613754257033580568977761)
      ·
        refine ⟨3460315692775185426733321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4613754257033580568977761 3460315692775185426733321)
        ·
          refine ⟨2595236769581389070049991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460315692775185426733321 2595236769581389070049991)
          ·
            refine ⟨3892855154372083605074987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595236769581389070049991 3892855154372083605074987)
            ·
              refine ⟨5839282731558125407612481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892855154372083605074987 5839282731558125407612481)
              ·
                refine ⟨4379462048668594055709361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5839282731558125407612481 4379462048668594055709361)
                ·
                  refine ⟨3284596536501445541782021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379462048668594055709361 3284596536501445541782021)
                  ·
                    refine ⟨615861850594021039084129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3284596536501445541782021 615861850594021039084129)
                    ·
                      refine ⟨461896387945515779313097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615861850594021039084129 461896387945515779313097)
                      ·
                        rfl

theorem cell23_899540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_899540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899540 prefixEnd_899540 := by exact prefixLift 899540
  have htrace : WordTrace (prefixWord ++ tailWord_899540) baseStart_899540 baseEnd_899540 := by
    simpa [prefixWord, tailWord_899540, baseEnd_899540] using wordTrace_append hprefix tailTrace_899540
  have hstable : (prefixWord ++ tailWord_899540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899540).length < 2 ^ (prefixWord ++ tailWord_899540).sum := by decide
  have hdescent : baseEnd_899540 < baseStart_899540 := by decide
  rcases family_descends (prefixWord ++ tailWord_899540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899546 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_899546 : Nat := 118140960795 + 899546 * 2 ^ 59
def prefixEnd_899546 : Nat := 4983230072969 + 3 ^ 40 * 899546 * 2
def baseEnd_899546 : Nat := 51322163203271417315341

theorem tailTrace_899546 : CollatzResearch.WordTrace tailWord_899546 prefixEnd_899546 51322163203271417315341 := by
  unfold tailWord_899546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202284499776486767695623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21872758666070631380521661 8202284499776486767695623)
  ·
    refine ⟨12303426749664730151543435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202284499776486767695623 12303426749664730151543435)
    ·
      refine ⟨18455140124497095227315153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12303426749664730151543435 18455140124497095227315153)
      ·
        refine ⟨13841355093372821420486365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18455140124497095227315153 13841355093372821420486365)
        ·
          refine ⟨5190508160014808032682387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13841355093372821420486365 5190508160014808032682387)
          ·
            refine ⟨7785762240022212049023581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190508160014808032682387 7785762240022212049023581)
            ·
              refine ⟨2919660840008329518383843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7785762240022212049023581 2919660840008329518383843)
              ·
                refine ⟨4379491260012494277575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919660840008329518383843 4379491260012494277575765)
                ·
                  refine ⟨51322163203271417315341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4379491260012494277575765 51322163203271417315341)
                  ·
                    rfl

theorem cell23_899546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_899546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899546 prefixEnd_899546 := by exact prefixLift 899546
  have htrace : WordTrace (prefixWord ++ tailWord_899546) baseStart_899546 baseEnd_899546 := by
    simpa [prefixWord, tailWord_899546, baseEnd_899546] using wordTrace_append hprefix tailTrace_899546
  have hstable : (prefixWord ++ tailWord_899546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899546).length < 2 ^ (prefixWord ++ tailWord_899546).sum := by decide
  have hdescent : baseEnd_899546 < baseStart_899546 := by decide
  rcases family_descends (prefixWord ++ tailWord_899546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899563 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 6]
def baseStart_899563 : Nat := 118140960795 + 899563 * 2 ^ 59
def prefixEnd_899563 : Nat := 4983230072969 + 3 ^ 40 * 899563 * 2
def baseEnd_899563 : Nat := 51323133111174354369499

theorem tailTrace_899563 : CollatzResearch.WordTrace tailWord_899563 prefixEnd_899563 51323133111174354369499 := by
  unfold tailWord_899563
  simp only [CollatzResearch.WordTrace]
  refine ⟨32809758040044358974151343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21873172026696239316100895 32809758040044358974151343)
  ·
    refine ⟨49214637060066538461227015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32809758040044358974151343 49214637060066538461227015)
    ·
      refine ⟨73821955590099807691840523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49214637060066538461227015 73821955590099807691840523)
      ·
        refine ⟨110732933385149711537760785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73821955590099807691840523 110732933385149711537760785)
        ·
          refine ⟨83049700038862283653320589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110732933385149711537760785 83049700038862283653320589)
          ·
            refine ⟨31143637514573356369995221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83049700038862283653320589 31143637514573356369995221)
            ·
              refine ⟨729929004247813039921763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31143637514573356369995221 729929004247813039921763)
              ·
                refine ⟨1094893506371719559882645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729929004247813039921763 1094893506371719559882645)
                ·
                  refine ⟨51323133111174354369499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1094893506371719559882645 51323133111174354369499)
                  ·
                    rfl

theorem cell23_899563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 6].length) (baseStart_899563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899563 prefixEnd_899563 := by exact prefixLift 899563
  have htrace : WordTrace (prefixWord ++ tailWord_899563) baseStart_899563 baseEnd_899563 := by
    simpa [prefixWord, tailWord_899563, baseEnd_899563] using wordTrace_append hprefix tailTrace_899563
  have hstable : (prefixWord ++ tailWord_899563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899563).length < 2 ^ (prefixWord ++ tailWord_899563).sum := by decide
  have hdescent : baseEnd_899563 < baseStart_899563 := by decide
  rcases family_descends (prefixWord ++ tailWord_899563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899583 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 1, 5, 2]
def baseStart_899583 : Nat := 118140960795 + 899583 * 2 ^ 59
def prefixEnd_899583 : Nat := 4983230072969 + 3 ^ 40 * 899583 * 2
def baseEnd_899583 : Nat := 461918467613659111075399

theorem tailTrace_899583 : CollatzResearch.WordTrace tailWord_899583 prefixEnd_899583 461918467613659111075399 := by
  unfold tailWord_899583
  simp only [CollatzResearch.WordTrace]
  refine ⟨32810487499971902389879403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21873658333314601593252935 32810487499971902389879403)
  ·
    refine ⟨49215731249957853584819105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32810487499971902389879403 49215731249957853584819105)
    ·
      refine ⟨36911798437468390188614329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49215731249957853584819105 36911798437468390188614329)
      ·
        refine ⟨27683848828101292641460747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36911798437468390188614329 27683848828101292641460747)
        ·
          refine ⟨41525773242151938962191121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27683848828101292641460747 41525773242151938962191121)
          ·
            refine ⟨31144329931613954221643341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41525773242151938962191121 31144329931613954221643341)
            ·
              refine ⟨11679123724355232833116253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31144329931613954221643341 11679123724355232833116253)
              ·
                refine ⟨4379671396633212312418595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11679123724355232833116253 4379671396633212312418595)
                ·
                  refine ⟨6569507094949818468627893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4379671396633212312418595 6569507094949818468627893)
                  ·
                    refine ⟨615891290151545481433865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6569507094949818468627893 615891290151545481433865)
                    ·
                      refine ⟨461918467613659111075399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 615891290151545481433865 461918467613659111075399)
                      ·
                        rfl

theorem cell23_899583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_899583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899583 prefixEnd_899583 := by exact prefixLift 899583
  have htrace : WordTrace (prefixWord ++ tailWord_899583) baseStart_899583 baseEnd_899583 := by
    simpa [prefixWord, tailWord_899583, baseEnd_899583] using wordTrace_append hprefix tailTrace_899583
  have hstable : (prefixWord ++ tailWord_899583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899583).length < 2 ^ (prefixWord ++ tailWord_899583).sum := by decide
  have hdescent : baseEnd_899583 < baseStart_899583 := by decide
  rcases family_descends (prefixWord ++ tailWord_899583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899701 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_899701 : Nat := 118140960795 + 899701 * 2 ^ 59
def prefixEnd_899701 : Nat := 4983230072969 + 3 ^ 40 * 899701 * 2
def baseEnd_899701 : Nat := 461979058330889649399857

theorem tailTrace_899701 : CollatzResearch.WordTrace tailWord_899701 prefixEnd_899701 461979058330889649399857 := by
  unfold tailWord_899701
  simp only [CollatzResearch.WordTrace]
  refine ⟨32814791313544408542674957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21876527542362939028449971 32814791313544408542674957)
  ·
    refine ⟨12305546742579153203503109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32814791313544408542674957 12305546742579153203503109)
    ·
      refine ⟨2307290014233591225656833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12305546742579153203503109 2307290014233591225656833)
      ·
        refine ⟨1730467510675193419242625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307290014233591225656833 1730467510675193419242625)
        ·
          refine ⟨1297850633006395064431969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1730467510675193419242625 1297850633006395064431969)
          ·
            refine ⟨973387974754796298323977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297850633006395064431969 973387974754796298323977)
            ·
              refine ⟨730040981066097223742983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973387974754796298323977 730040981066097223742983)
              ·
                refine ⟨1095061471599145835614475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730040981066097223742983 1095061471599145835614475)
                ·
                  refine ⟨1642592207398718753421713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095061471599145835614475 1642592207398718753421713)
                  ·
                    refine ⟨1231944155549039065066285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642592207398718753421713 1231944155549039065066285)
                    ·
                      refine ⟨461979058330889649399857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1231944155549039065066285 461979058330889649399857)
                      ·
                        rfl

theorem cell23_899701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_899701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899701 prefixEnd_899701 := by exact prefixLift 899701
  have htrace : WordTrace (prefixWord ++ tailWord_899701) baseStart_899701 baseEnd_899701 := by
    simpa [prefixWord, tailWord_899701, baseEnd_899701] using wordTrace_append hprefix tailTrace_899701
  have hstable : (prefixWord ++ tailWord_899701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899701).length < 2 ^ (prefixWord ++ tailWord_899701).sum := by decide
  have hdescent : baseEnd_899701 < baseStart_899701 := by decide
  rcases family_descends (prefixWord ++ tailWord_899701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899713 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_899713 : Nat := 118140960795 + 899713 * 2 ^ 59
def prefixEnd_899713 : Nat := 4983230072969 + 3 ^ 40 * 899713 * 2
def baseEnd_899713 : Nat := 153995073366247867483267

theorem tailTrace_899713 : CollatzResearch.WordTrace tailWord_899713 prefixEnd_899713 153995073366247867483267 := by
  unfold tailWord_899713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32815228989500934592111793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21876819326333956394741195 32815228989500934592111793)
  ·
    refine ⟨24611421742125700944083845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32815228989500934592111793 24611421742125700944083845)
    ·
      refine ⟨4614641576648568927015721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24611421742125700944083845 4614641576648568927015721)
      ·
        refine ⟨3460981182486426695261791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4614641576648568927015721 3460981182486426695261791)
        ·
          refine ⟨5191471773729640042892687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3460981182486426695261791 5191471773729640042892687)
          ·
            refine ⟨7787207660594460064339031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5191471773729640042892687 7787207660594460064339031)
            ·
              refine ⟨11680811490891690096508547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7787207660594460064339031 11680811490891690096508547)
              ·
                refine ⟨17521217236337535144762821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11680811490891690096508547 17521217236337535144762821)
                ·
                  refine ⟨3285228231813287839643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17521217236337535144762821 3285228231813287839643029)
                  ·
                    refine ⟨153995073366247867483267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3285228231813287839643029 153995073366247867483267)
                    ·
                      rfl

theorem cell23_899713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_899713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899713 prefixEnd_899713 := by exact prefixLift 899713
  have htrace : WordTrace (prefixWord ++ tailWord_899713) baseStart_899713 baseEnd_899713 := by
    simpa [prefixWord, tailWord_899713, baseEnd_899713] using wordTrace_append hprefix tailTrace_899713
  have hstable : (prefixWord ++ tailWord_899713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899713).length < 2 ^ (prefixWord ++ tailWord_899713).sum := by decide
  have hdescent : baseEnd_899713 < baseStart_899713 := by decide
  rcases family_descends (prefixWord ++ tailWord_899713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899723 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3]
def baseStart_899723 : Nat := 118140960795 + 899723 * 2 ^ 59
def prefixEnd_899723 : Nat := 4983230072969 + 3 ^ 40 * 899723 * 2
def baseEnd_899723 : Nat := 461990354905288563324755

theorem tailTrace_899723 : CollatzResearch.WordTrace tailWord_899723 prefixEnd_899723 461990354905288563324755 := by
  unfold tailWord_899723
  simp only [CollatzResearch.WordTrace]
  refine ⟨32815593719464706299975823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21877062479643137533317215 32815593719464706299975823)
  ·
    refine ⟨49223390579197059449963735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32815593719464706299975823 49223390579197059449963735)
    ·
      refine ⟨73835085868795589174945603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49223390579197059449963735 73835085868795589174945603)
      ·
        refine ⟨110752628803193383762418405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73835085868795589174945603 110752628803193383762418405)
        ·
          refine ⟨20766117900598759455453451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110752628803193383762418405 20766117900598759455453451)
          ·
            refine ⟨31149176850898139183180177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20766117900598759455453451 31149176850898139183180177)
            ·
              refine ⟨23361882638173604387385133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31149176850898139183180177 23361882638173604387385133)
              ·
                refine ⟨8760705989315101645269425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23361882638173604387385133 8760705989315101645269425)
                ·
                  refine ⟨6570529491986326233952069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8760705989315101645269425 6570529491986326233952069)
                  ·
                    refine ⟨1231974279747436168866013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6570529491986326233952069 1231974279747436168866013)
                    ·
                      refine ⟨461990354905288563324755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1231974279747436168866013 461990354905288563324755)
                      ·
                        rfl

theorem cell23_899723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].length) (baseStart_899723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899723 prefixEnd_899723 := by exact prefixLift 899723
  have htrace : WordTrace (prefixWord ++ tailWord_899723) baseStart_899723 baseEnd_899723 := by
    simpa [prefixWord, tailWord_899723, baseEnd_899723] using wordTrace_append hprefix tailTrace_899723
  have hstable : (prefixWord ++ tailWord_899723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899723).length < 2 ^ (prefixWord ++ tailWord_899723).sum := by decide
  have hdescent : baseEnd_899723 < baseStart_899723 := by decide
  rcases family_descends (prefixWord ++ tailWord_899723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899730 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_899730 : Nat := 118140960795 + 899730 * 2 ^ 59
def prefixEnd_899730 : Nat := 4983230072969 + 3 ^ 40 * 899730 * 2
def baseEnd_899730 : Nat := 153997983089956678645741

theorem tailTrace_899730 : CollatzResearch.WordTrace tailWord_899730 prefixEnd_899730 153997983089956678645741 := by
  unfold tailWord_899730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203962257609836623870161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21877232686959564330320429 8203962257609836623870161)
  ·
    refine ⟨6152971693207377467902621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8203962257609836623870161 6152971693207377467902621)
    ·
      refine ⟨2307364384952766550463483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6152971693207377467902621 2307364384952766550463483)
      ·
        refine ⟨3461046577429149825695225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307364384952766550463483 3461046577429149825695225)
        ·
          refine ⟨2595784933071862369271419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461046577429149825695225 2595784933071862369271419)
          ·
            refine ⟨3893677399607793553907129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595784933071862369271419 3893677399607793553907129)
            ·
              refine ⟨2920258049705845165430347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893677399607793553907129 2920258049705845165430347)
              ·
                refine ⟨4380387074558767748145521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920258049705845165430347 4380387074558767748145521)
                ·
                  refine ⟨3285290305919075811109141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4380387074558767748145521 3285290305919075811109141)
                  ·
                    refine ⟨153997983089956678645741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3285290305919075811109141 153997983089956678645741)
                    ·
                      rfl

theorem cell23_899730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_899730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899730 prefixEnd_899730 := by exact prefixLift 899730
  have htrace : WordTrace (prefixWord ++ tailWord_899730) baseStart_899730 baseEnd_899730 := by
    simpa [prefixWord, tailWord_899730, baseEnd_899730] using wordTrace_append hprefix tailTrace_899730
  have hstable : (prefixWord ++ tailWord_899730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899730).length < 2 ^ (prefixWord ++ tailWord_899730).sum := by decide
  have hdescent : baseEnd_899730 < baseStart_899730 := by decide
  rcases family_descends (prefixWord ++ tailWord_899730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899753 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_899753 : Nat := 118140960795 + 899753 * 2 ^ 59
def prefixEnd_899753 : Nat := 4983230072969 + 3 ^ 40 * 899753 * 2
def baseEnd_899753 : Nat := 462005759324923445949617

theorem tailTrace_899753 : CollatzResearch.WordTrace tailWord_899753 prefixEnd_899753 462005759324923445949617 := by
  unfold tailWord_899753
  simp only [CollatzResearch.WordTrace]
  refine ⟨32816687909356021423567913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21877791939570680949045275 32816687909356021423567913)
  ·
    refine ⟨24612515932017016067675935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32816687909356021423567913 24612515932017016067675935)
    ·
      refine ⟨36918773898025524101513903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24612515932017016067675935 36918773898025524101513903)
      ·
        refine ⟨55378160847038286152270855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36918773898025524101513903 55378160847038286152270855)
        ·
          refine ⟨83067241270557429228406283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55378160847038286152270855 83067241270557429228406283)
          ·
            refine ⟨124600861905836143842609425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83067241270557429228406283 124600861905836143842609425)
            ·
              refine ⟨93450646429377107881957069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124600861905836143842609425 93450646429377107881957069)
              ·
                refine ⟨35043992411016415455733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93450646429377107881957069 35043992411016415455733901)
                ·
                  refine ⟨13141497154131155795900213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35043992411016415455733901 13141497154131155795900213)
                  ·
                    refine ⟨1232015358199795855865645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13141497154131155795900213 1232015358199795855865645)
                    ·
                      refine ⟨462005759324923445949617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232015358199795855865645 462005759324923445949617)
                      ·
                        rfl

theorem cell23_899753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_899753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899753 prefixEnd_899753 := by exact prefixLift 899753
  have htrace : WordTrace (prefixWord ++ tailWord_899753) baseStart_899753 baseEnd_899753 := by
    simpa [prefixWord, tailWord_899753, baseEnd_899753] using wordTrace_append hprefix tailTrace_899753
  have hstable : (prefixWord ++ tailWord_899753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899753).length < 2 ^ (prefixWord ++ tailWord_899753).sum := by decide
  have hdescent : baseEnd_899753 < baseStart_899753 := by decide
  rcases family_descends (prefixWord ++ tailWord_899753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899782 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_899782 : Nat := 118140960795 + 899782 * 2 ^ 59
def prefixEnd_899782 : Nat := 4983230072969 + 3 ^ 40 * 899782 * 2
def baseEnd_899782 : Nat := 462020650263903832486985

theorem tailTrace_899782 : CollatzResearch.WordTrace tailWord_899782 prefixEnd_899782 462020650263903832486985 := by
  unfold tailWord_899782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025554550820342480511675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21878497084167306250915733 1025554550820342480511675)
  ·
    refine ⟨1538331826230513720767513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025554550820342480511675 1538331826230513720767513)
    ·
      refine ⟨1153748869672885290575635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1538331826230513720767513 1153748869672885290575635)
      ·
        refine ⟨1730623304509327935863453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153748869672885290575635 1730623304509327935863453)
        ·
          refine ⟨648983739190997975948795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1730623304509327935863453 648983739190997975948795)
          ·
            refine ⟨973475608786496963923193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648983739190997975948795 973475608786496963923193)
            ·
              refine ⟨730106706589872722942395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973475608786496963923193 730106706589872722942395)
              ·
                refine ⟨1095160059884809084413593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730106706589872722942395 1095160059884809084413593)
                ·
                  refine ⟨821370044913606813310195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095160059884809084413593 821370044913606813310195)
                  ·
                    refine ⟨1232055067370410219965293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821370044913606813310195 1232055067370410219965293)
                    ·
                      refine ⟨462020650263903832486985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232055067370410219965293 462020650263903832486985)
                      ·
                        rfl

theorem cell23_899782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_899782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899782 prefixEnd_899782 := by exact prefixLift 899782
  have htrace : WordTrace (prefixWord ++ tailWord_899782) baseStart_899782 baseEnd_899782 := by
    simpa [prefixWord, tailWord_899782, baseEnd_899782] using wordTrace_append hprefix tailTrace_899782
  have hstable : (prefixWord ++ tailWord_899782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899782).length < 2 ^ (prefixWord ++ tailWord_899782).sum := by decide
  have hdescent : baseEnd_899782 < baseStart_899782 := by decide
  rcases family_descends (prefixWord ++ tailWord_899782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899788 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_899788 : Nat := 118140960795 + 899788 * 2 ^ 59
def prefixEnd_899788 : Nat := 4983230072969 + 3 ^ 40 * 899788 * 2
def baseEnd_899788 : Nat := 462023731147830809011957

theorem tailTrace_899788 : CollatzResearch.WordTrace tailWord_899788 prefixEnd_899788 462023731147830809011957 := by
  unfold tailWord_899788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408982232114611200546009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21878642976152814934061345 16408982232114611200546009)
  ·
    refine ⟨12306736674085958400409507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16408982232114611200546009 12306736674085958400409507)
    ·
      refine ⟨18460105011128937600614261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12306736674085958400409507 18460105011128937600614261)
      ·
        refine ⟨1730634844793337900057587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18460105011128937600614261 1730634844793337900057587)
        ·
          refine ⟨2595952267190006850086381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730634844793337900057587 2595952267190006850086381)
          ·
            refine ⟨973482100196252568782393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595952267190006850086381 973482100196252568782393)
            ·
              refine ⟨730111575147189426586795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973482100196252568782393 730111575147189426586795)
              ·
                refine ⟨1095167362720784139880193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730111575147189426586795 1095167362720784139880193)
                ·
                  refine ⟨821375522040588104910145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095167362720784139880193 821375522040588104910145)
                  ·
                    refine ⟨616031641530441078682609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821375522040588104910145 616031641530441078682609)
                    ·
                      refine ⟨462023731147830809011957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616031641530441078682609 462023731147830809011957)
                      ·
                        rfl

theorem cell23_899788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_899788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899788 prefixEnd_899788 := by exact prefixLift 899788
  have htrace : WordTrace (prefixWord ++ tailWord_899788) baseStart_899788 baseEnd_899788 := by
    simpa [prefixWord, tailWord_899788, baseEnd_899788] using wordTrace_append hprefix tailTrace_899788
  have hstable : (prefixWord ++ tailWord_899788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899788).length < 2 ^ (prefixWord ++ tailWord_899788).sum := by decide
  have hdescent : baseEnd_899788 < baseStart_899788 := by decide
  rcases family_descends (prefixWord ++ tailWord_899788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899830 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_899830 : Nat := 118140960795 + 899830 * 2 ^ 59
def prefixEnd_899830 : Nat := 4983230072969 + 3 ^ 40 * 899830 * 2
def baseEnd_899830 : Nat := 462045297335319644686763

theorem tailTrace_899830 : CollatzResearch.WordTrace tailWord_899830 prefixEnd_899830 462045297335319644686763 := by
  unfold tailWord_899830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051218520629816473382559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21879664220051375716080629 2051218520629816473382559)
  ·
    refine ⟨3076827780944724710073839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2051218520629816473382559 3076827780944724710073839)
    ·
      refine ⟨4615241671417087065110759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076827780944724710073839 4615241671417087065110759)
      ·
        refine ⟨6922862507125630597666139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4615241671417087065110759 6922862507125630597666139)
        ·
          refine ⟨10384293760688445896499209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6922862507125630597666139 10384293760688445896499209)
          ·
            refine ⟨7788220320516334422374407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384293760688445896499209 7788220320516334422374407)
            ·
              refine ⟨11682330480774501633561611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788220320516334422374407 11682330480774501633561611)
              ·
                refine ⟨17523495721161752450342417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11682330480774501633561611 17523495721161752450342417)
                ·
                  refine ⟨13142621790871314337756813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17523495721161752450342417 13142621790871314337756813)
                  ·
                    refine ⟨4928483171576742876658805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13142621790871314337756813 4928483171576742876658805)
                    ·
                      refine ⟨462045297335319644686763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4928483171576742876658805 462045297335319644686763)
                      ·
                        rfl

theorem cell23_899830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_899830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899830 prefixEnd_899830 := by exact prefixLift 899830
  have htrace : WordTrace (prefixWord ++ tailWord_899830) baseStart_899830 baseEnd_899830 := by
    simpa [prefixWord, tailWord_899830, baseEnd_899830] using wordTrace_append hprefix tailTrace_899830
  have hstable : (prefixWord ++ tailWord_899830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899830).length < 2 ^ (prefixWord ++ tailWord_899830).sum := by decide
  have hdescent : baseEnd_899830 < baseStart_899830 := by decide
  rcases family_descends (prefixWord ++ tailWord_899830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899833 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 8]
def baseStart_899833 : Nat := 118140960795 + 899833 * 2 ^ 59
def prefixEnd_899833 : Nat := 4983230072969 + 3 ^ 40 * 899833 * 2
def baseEnd_899833 : Nat := 51338537530809236994361

theorem tailTrace_899833 : CollatzResearch.WordTrace tailWord_899833 prefixEnd_899833 51338537530809236994361 := by
  unfold tailWord_899833
  simp only [CollatzResearch.WordTrace]
  refine ⟨32819605749066195086480153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21879737166044130057653435 32819605749066195086480153)
  ·
    refine ⟨24614704311799646314860115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32819605749066195086480153 24614704311799646314860115)
    ·
      refine ⟨36922056467699469472290173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24614704311799646314860115 36922056467699469472290173)
      ·
        refine ⟨13845771175387301052108815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36922056467699469472290173 13845771175387301052108815)
        ·
          refine ⟨20768656763080951578163223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13845771175387301052108815 20768656763080951578163223)
          ·
            refine ⟨31152985144621427367244835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20768656763080951578163223 31152985144621427367244835)
            ·
              refine ⟨46729477716932141050867253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31152985144621427367244835 46729477716932141050867253)
              ·
                refine ⟨4380888535962388223518805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46729477716932141050867253 4380888535962388223518805)
                ·
                  refine ⟨51338537530809236994361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4380888535962388223518805 51338537530809236994361)
                  ·
                    rfl

theorem cell23_899833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_899833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899833 prefixEnd_899833 := by exact prefixLift 899833
  have htrace : WordTrace (prefixWord ++ tailWord_899833) baseStart_899833 baseEnd_899833 := by
    simpa [prefixWord, tailWord_899833, baseEnd_899833] using wordTrace_append hprefix tailTrace_899833
  have hstable : (prefixWord ++ tailWord_899833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899833).length < 2 ^ (prefixWord ++ tailWord_899833).sum := by decide
  have hdescent : baseEnd_899833 < baseStart_899833 := by decide
  rcases family_descends (prefixWord ++ tailWord_899833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899850 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_899850 : Nat := 118140960795 + 899850 * 2 ^ 59
def prefixEnd_899850 : Nat := 4983230072969 + 3 ^ 40 * 899850 * 2
def baseEnd_899850 : Nat := 51339507438712174048519

theorem tailTrace_899850 : CollatzResearch.WordTrace tailWord_899850 prefixEnd_899850 51339507438712174048519 := by
  unfold tailWord_899850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205056447501151747462251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21880150526669737993232669 8205056447501151747462251)
  ·
    refine ⟨12307584671251727621193377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8205056447501151747462251 12307584671251727621193377)
    ·
      refine ⟨9230688503438795715895033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12307584671251727621193377 9230688503438795715895033)
      ·
        refine ⟨6923016377579096786921275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9230688503438795715895033 6923016377579096786921275)
        ·
          refine ⟨10384524566368645180381913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6923016377579096786921275 10384524566368645180381913)
          ·
            refine ⟨7788393424776483885286435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10384524566368645180381913 7788393424776483885286435)
            ·
              refine ⟨11682590137164725827929653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788393424776483885286435 11682590137164725827929653)
              ·
                refine ⟨1095242825359193046368405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11682590137164725827929653 1095242825359193046368405)
                ·
                  refine ⟨51339507438712174048519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1095242825359193046368405 51339507438712174048519)
                  ·
                    rfl

theorem cell23_899850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_899850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899850 prefixEnd_899850 := by exact prefixLift 899850
  have htrace : WordTrace (prefixWord ++ tailWord_899850) baseStart_899850 baseEnd_899850 := by
    simpa [prefixWord, tailWord_899850, baseEnd_899850] using wordTrace_append hprefix tailTrace_899850
  have hstable : (prefixWord ++ tailWord_899850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899850).length < 2 ^ (prefixWord ++ tailWord_899850).sum := by decide
  have hdescent : baseEnd_899850 < baseStart_899850 := by decide
  rcases family_descends (prefixWord ++ tailWord_899850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899877 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_899877 : Nat := 118140960795 + 899877 * 2 ^ 59
def prefixEnd_899877 : Nat := 4983230072969 + 3 ^ 40 * 899877 * 2
def baseEnd_899877 : Nat := 462069430926080960799047

theorem tailTrace_899877 : CollatzResearch.WordTrace tailWord_899877 prefixEnd_899877 462069430926080960799047 := by
  unfold tailWord_899877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32821210560906790601081885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21880807040604527067387923 32821210560906790601081885)
  ·
    refine ⟨12307953960340046475405707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32821210560906790601081885 12307953960340046475405707)
    ·
      refine ⟨18461930940510069713108561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12307953960340046475405707 18461930940510069713108561)
      ·
        refine ⟨13846448205382552284831421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18461930940510069713108561 13846448205382552284831421)
        ·
          refine ⟨5192418077018457106811783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13846448205382552284831421 5192418077018457106811783)
          ·
            refine ⟨7788627115527685660217675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5192418077018457106811783 7788627115527685660217675)
            ·
              refine ⟨11682940673291528490326513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7788627115527685660217675 11682940673291528490326513)
              ·
                refine ⟨8762205504968646367744885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11682940673291528490326513 8762205504968646367744885)
                ·
                  refine ⟨821456766090810596976083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8762205504968646367744885 821456766090810596976083)
                  ·
                    refine ⟨1232185149136215895464125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821456766090810596976083 1232185149136215895464125)
                    ·
                      refine ⟨462069430926080960799047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232185149136215895464125 462069430926080960799047)
                      ·
                        rfl

theorem cell23_899877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_899877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899877 prefixEnd_899877 := by exact prefixLift 899877
  have htrace : WordTrace (prefixWord ++ tailWord_899877) baseStart_899877 baseEnd_899877 := by
    simpa [prefixWord, tailWord_899877, baseEnd_899877] using wordTrace_append hprefix tailTrace_899877
  have hstable : (prefixWord ++ tailWord_899877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899877).length < 2 ^ (prefixWord ++ tailWord_899877).sum := by decide
  have hdescent : baseEnd_899877 < baseStart_899877 := by decide
  rcases family_descends (prefixWord ++ tailWord_899877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899927 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 4, 4]
def baseStart_899927 : Nat := 118140960795 + 899927 * 2 ^ 59
def prefixEnd_899927 : Nat := 4983230072969 + 3 ^ 40 * 899927 * 2
def baseEnd_899927 : Nat := 154031701652935255057939

theorem tailTrace_899927 : CollatzResearch.WordTrace tailWord_899927 prefixEnd_899927 154031701652935255057939 := by
  unfold tailWord_899927
  simp only [CollatzResearch.WordTrace]
  refine ⟨32823034210725649140402035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21882022807150432760268023 32823034210725649140402035)
  ·
    refine ⟨49234551316088473710603053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32823034210725649140402035 49234551316088473710603053)
    ·
      refine ⟨18462956743533177641476145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49234551316088473710603053 18462956743533177641476145)
      ·
        refine ⟨13847217557649883231107109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18462956743533177641476145 13847217557649883231107109)
        ·
          refine ⟨2596353292059353105832583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13847217557649883231107109 2596353292059353105832583)
          ·
            refine ⟨3894529938089029658748875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596353292059353105832583 3894529938089029658748875)
            ·
              refine ⟨5841794907133544488123313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894529938089029658748875 5841794907133544488123313)
              ·
                refine ⟨4381346180350158366092485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5841794907133544488123313 4381346180350158366092485)
                ·
                  refine ⟨821502408815654693642341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4381346180350158366092485 821502408815654693642341)
                  ·
                    refine ⟨154031701652935255057939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 821502408815654693642341 154031701652935255057939)
                    ·
                      rfl

theorem cell23_899927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_899927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899927 prefixEnd_899927 := by exact prefixLift 899927
  have htrace : WordTrace (prefixWord ++ tailWord_899927) baseStart_899927 baseEnd_899927 := by
    simpa [prefixWord, tailWord_899927, baseEnd_899927] using wordTrace_append hprefix tailTrace_899927
  have hstable : (prefixWord ++ tailWord_899927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899927).length < 2 ^ (prefixWord ++ tailWord_899927).sum := by decide
  have hdescent : baseEnd_899927 < baseStart_899927 := by decide
  rcases family_descends (prefixWord ++ tailWord_899927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899940 : List Nat := [2, 3, 1, 1, 4, 1, 11]
def baseStart_899940 : Nat := 118140960795 + 899940 * 2 ^ 59
def prefixEnd_899940 : Nat := 4983230072969 + 3 ^ 40 * 899940 * 2
def baseEnd_899940 : Nat := 5704960249473014991497

theorem tailTrace_899940 : CollatzResearch.WordTrace tailWord_899940 prefixEnd_899940 5704960249473014991497 := by
  unfold tailWord_899940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16411754179839276180312637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21882338906452368240416849 16411754179839276180312637)
  ·
    refine ⟨6154407817439728567617239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16411754179839276180312637 6154407817439728567617239)
    ·
      refine ⟨9231611726159592851425859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6154407817439728567617239 9231611726159592851425859)
      ·
        refine ⟨13847417589239389277138789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9231611726159592851425859 13847417589239389277138789)
        ·
          refine ⟨2596390797982385489463523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13847417589239389277138789 2596390797982385489463523)
          ·
            refine ⟨3894586196973578234195285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596390797982385489463523 3894586196973578234195285)
            ·
              refine ⟨5704960249473014991497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3894586196973578234195285 5704960249473014991497)
              ·
                rfl

theorem cell23_899940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 11].length) (baseStart_899940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899940 prefixEnd_899940 := by exact prefixLift 899940
  have htrace : WordTrace (prefixWord ++ tailWord_899940) baseStart_899940 baseEnd_899940 := by
    simpa [prefixWord, tailWord_899940, baseEnd_899940] using wordTrace_append hprefix tailTrace_899940
  have hstable : (prefixWord ++ tailWord_899940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899940).length < 2 ^ (prefixWord ++ tailWord_899940).sum := by decide
  have hdescent : baseEnd_899940 < baseStart_899940 := by decide
  rcases family_descends (prefixWord ++ tailWord_899940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899951 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 1, 2, 2]
def baseStart_899951 : Nat := 118140960795 + 899951 * 2 ^ 59
def prefixEnd_899951 : Nat := 4983230072969 + 3 ^ 40 * 899951 * 2
def baseEnd_899951 : Nat := 462107428494513671273707

theorem tailTrace_899951 : CollatzResearch.WordTrace tailWord_899951 prefixEnd_899951 462107428494513671273707 := by
  unfold tailWord_899951
  simp only [CollatzResearch.WordTrace]
  refine ⟨32823909562638701239275707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21882606375092467492850471 32823909562638701239275707)
  ·
    refine ⟨49235864343958051858913561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32823909562638701239275707 49235864343958051858913561)
    ·
      refine ⟨36926898257968538894185171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49235864343958051858913561 36926898257968538894185171)
      ·
        refine ⟨55390347386952808341277757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36926898257968538894185171 55390347386952808341277757)
        ·
          refine ⟨20771380270107303127979159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55390347386952808341277757 20771380270107303127979159)
          ·
            refine ⟨31157070405160954691968739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20771380270107303127979159 31157070405160954691968739)
            ·
              refine ⟨46735605607741432037953109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31157070405160954691968739 46735605607741432037953109)
              ·
                refine ⟨547682878215719906694763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46735605607741432037953109 547682878215719906694763)
                ·
                  refine ⟨821524317323579860042145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547682878215719906694763 821524317323579860042145)
                  ·
                    refine ⟨616143237992684895031609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821524317323579860042145 616143237992684895031609)
                    ·
                      refine ⟨462107428494513671273707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616143237992684895031609 462107428494513671273707)
                      ·
                        rfl

theorem cell23_899951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 1, 2, 2].length) (baseStart_899951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899951 prefixEnd_899951 := by exact prefixLift 899951
  have htrace : WordTrace (prefixWord ++ tailWord_899951) baseStart_899951 baseEnd_899951 := by
    simpa [prefixWord, tailWord_899951, baseEnd_899951] using wordTrace_append hprefix tailTrace_899951
  have hstable : (prefixWord ++ tailWord_899951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899951).length < 2 ^ (prefixWord ++ tailWord_899951).sum := by decide
  have hdescent : baseEnd_899951 < baseStart_899951 := by decide
  rcases family_descends (prefixWord ++ tailWord_899951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899957 : List Nat := [1, 3, 4, 1, 1, 3, 2, 8]
def baseStart_899957 : Nat := 118140960795 + 899957 * 2 ^ 59
def prefixEnd_899957 : Nat := 4983230072969 + 3 ^ 40 * 899957 * 2
def baseEnd_899957 : Nat := 17115204051053357325877

theorem tailTrace_899957 : CollatzResearch.WordTrace tailWord_899957 prefixEnd_899957 17115204051053357325877 := by
  unfold tailWord_899957
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824128400616964263994125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21882752267077976175996083 32824128400616964263994125)
  ·
    refine ⟨12309048150231361598997797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32824128400616964263994125 12309048150231361598997797)
    ·
      refine ⟨2307946528168380299812087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12309048150231361598997797 2307946528168380299812087)
      ·
        refine ⟨3461919792252570449718131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2307946528168380299812087 3461919792252570449718131)
        ·
          refine ⟨5192879688378855674577197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461919792252570449718131 5192879688378855674577197)
          ·
            refine ⟨1947329883142070877966449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5192879688378855674577197 1947329883142070877966449)
            ·
              refine ⟨1460497412356553158474837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947329883142070877966449 1460497412356553158474837)
              ·
                refine ⟨17115204051053357325877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1460497412356553158474837 17115204051053357325877)
                ·
                  rfl

theorem cell23_899957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 8].length) (baseStart_899957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899957 prefixEnd_899957 := by exact prefixLift 899957
  have htrace : WordTrace (prefixWord ++ tailWord_899957) baseStart_899957 baseEnd_899957 := by
    simpa [prefixWord, tailWord_899957, baseEnd_899957] using wordTrace_append hprefix tailTrace_899957
  have hstable : (prefixWord ++ tailWord_899957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899957).length < 2 ^ (prefixWord ++ tailWord_899957).sum := by decide
  have hdescent : baseEnd_899957 < baseStart_899957 := by decide
  rcases family_descends (prefixWord ++ tailWord_899957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899961 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_899961 : Nat := 118140960795 + 899961 * 2 ^ 59
def prefixEnd_899961 : Nat := 4983230072969 + 3 ^ 40 * 899961 * 2
def baseEnd_899961 : Nat := 154037521100352877382887

theorem tailTrace_899961 : CollatzResearch.WordTrace tailWord_899961 prefixEnd_899961 154037521100352877382887 := by
  unfold tailWord_899961
  simp only [CollatzResearch.WordTrace]
  refine ⟨32824274292602472947139737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21882849528401648631426491 32824274292602472947139737)
  ·
    refine ⟨24618205719451854710354803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32824274292602472947139737 24618205719451854710354803)
    ·
      refine ⟨36927308579177782065532205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24618205719451854710354803 36927308579177782065532205)
      ·
        refine ⟨13847740717191668274574577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36927308579177782065532205 13847740717191668274574577)
        ·
          refine ⟨10385805537893751205930933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13847740717191668274574577 10385805537893751205930933)
          ·
            refine ⟨973669269177539175556025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10385805537893751205930933 973669269177539175556025)
            ·
              refine ⟨730251951883154381667019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973669269177539175556025 730251951883154381667019)
              ·
                refine ⟨1095377927824731572500529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730251951883154381667019 1095377927824731572500529)
                ·
                  refine ⟨821533445868548679375397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095377927824731572500529 821533445868548679375397)
                  ·
                    refine ⟨154037521100352877382887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 821533445868548679375397 154037521100352877382887)
                    ·
                      rfl

theorem cell23_899961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_899961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899961 prefixEnd_899961 := by exact prefixLift 899961
  have htrace : WordTrace (prefixWord ++ tailWord_899961) baseStart_899961 baseEnd_899961 := by
    simpa [prefixWord, tailWord_899961, baseEnd_899961] using wordTrace_append hprefix tailTrace_899961
  have hstable : (prefixWord ++ tailWord_899961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899961).length < 2 ^ (prefixWord ++ tailWord_899961).sum := by decide
  have hdescent : baseEnd_899961 < baseStart_899961 := by decide
  rcases family_descends (prefixWord ++ tailWord_899961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899980 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_899980 : Nat := 118140960795 + 899980 * 2 ^ 59
def prefixEnd_899980 : Nat := 4983230072969 + 3 ^ 40 * 899980 * 2
def baseEnd_899980 : Nat := 462122319433494057811073

theorem tailTrace_899980 : CollatzResearch.WordTrace tailWord_899980 prefixEnd_899980 462122319433494057811073 := by
  unfold tailWord_899980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412483639766819596040697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21883311519689092794720929 16412483639766819596040697)
  ·
    refine ⟨12309362729825114697030523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16412483639766819596040697 12309362729825114697030523)
    ·
      refine ⟨18464044094737672045545785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12309362729825114697030523 18464044094737672045545785)
      ·
        refine ⟨13848033071053254034159339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18464044094737672045545785 13848033071053254034159339)
        ·
          refine ⟨20772049606579881051239009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13848033071053254034159339 20772049606579881051239009)
          ·
            refine ⟨15579037204934910788429257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20772049606579881051239009 15579037204934910788429257)
            ·
              refine ⟨11684277903701183091321943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15579037204934910788429257 11684277903701183091321943)
              ·
                refine ⟨17526416855551774636982915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11684277903701183091321943 17526416855551774636982915)
                ·
                  refine ⟨26289625283327661955474373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17526416855551774636982915 26289625283327661955474373)
                  ·
                    refine ⟨4929304740623936616651445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26289625283327661955474373 4929304740623936616651445)
                    ·
                      refine ⟨462122319433494057811073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4929304740623936616651445 462122319433494057811073)
                      ·
                        rfl

theorem cell23_899980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_899980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_899980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_899980 prefixEnd_899980 := by exact prefixLift 899980
  have htrace : WordTrace (prefixWord ++ tailWord_899980) baseStart_899980 baseEnd_899980 := by
    simpa [prefixWord, tailWord_899980, baseEnd_899980] using wordTrace_append hprefix tailTrace_899980
  have hstable : (prefixWord ++ tailWord_899980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899980).length < 2 ^ (prefixWord ++ tailWord_899980).sum := by decide
  have hdescent : baseEnd_899980 < baseStart_899980 := by decide
  rcases family_descends (prefixWord ++ tailWord_899980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900001 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_900001 : Nat := 118140960795 + 900001 * 2 ^ 59
def prefixEnd_900001 : Nat := 4983230072969 + 3 ^ 40 * 900001 * 2
def baseEnd_900001 : Nat := 462133102527238475648477

theorem tailTrace_900001 : CollatzResearch.WordTrace tailWord_900001 prefixEnd_900001 462133102527238475648477 := by
  unfold tailWord_900001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32825733212457559778595857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21883822141638373185730571 32825733212457559778595857)
  ·
    refine ⟨24619299909343169833946893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32825733212457559778595857 24619299909343169833946893)
    ·
      refine ⟨9232237466003688687730085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24619299909343169833946893 9232237466003688687730085)
      ·
        refine ⟨1731044524875691628949391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9232237466003688687730085 1731044524875691628949391)
        ·
          refine ⟨2596566787313537443424087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731044524875691628949391 2596566787313537443424087)
          ·
            refine ⟨3894850180970306165136131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596566787313537443424087 3894850180970306165136131)
            ·
              refine ⟨5842275271455459247704197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894850180970306165136131 5842275271455459247704197)
              ·
                refine ⟨1095426613397898608944537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5842275271455459247704197 1095426613397898608944537)
                ·
                  refine ⟨821569960048423956708403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095426613397898608944537 821569960048423956708403)
                  ·
                    refine ⟨1232354940072635935062605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821569960048423956708403 1232354940072635935062605)
                    ·
                      refine ⟨462133102527238475648477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232354940072635935062605 462133102527238475648477)
                      ·
                        rfl

theorem cell23_900001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_900001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900001 prefixEnd_900001 := by exact prefixLift 900001
  have htrace : WordTrace (prefixWord ++ tailWord_900001) baseStart_900001 baseEnd_900001 := by
    simpa [prefixWord, tailWord_900001, baseEnd_900001] using wordTrace_append hprefix tailTrace_900001
  have hstable : (prefixWord ++ tailWord_900001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900001).length < 2 ^ (prefixWord ++ tailWord_900001).sum := by decide
  have hdescent : baseEnd_900001 < baseStart_900001 := by decide
  rcases family_descends (prefixWord ++ tailWord_900001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900002 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_900002 : Nat := 118140960795 + 900002 * 2 ^ 59
def prefixEnd_900002 : Nat := 4983230072969 + 3 ^ 40 * 900002 * 2
def baseEnd_900002 : Nat := 462133616007892971735973

theorem tailTrace_900002 : CollatzResearch.WordTrace tailWord_900002 prefixEnd_900002 462133616007892971735973 := by
  unfold tailWord_900002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206442421363484237345565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21883846456969291299588173 8206442421363484237345565)
  ·
    refine ⟨3077415908011306589004587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8206442421363484237345565 3077415908011306589004587)
    ·
      refine ⟨4616123862016959883506881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077415908011306589004587 4616123862016959883506881)
      ·
        refine ⟨3462092896512719912630161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4616123862016959883506881 3462092896512719912630161)
        ·
          refine ⟨2596569672384539934472621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3462092896512719912630161 2596569672384539934472621)
          ·
            refine ⟨973713627144202475427233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596569672384539934472621 973713627144202475427233)
            ·
              refine ⟨730285220358151856570425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973713627144202475427233 730285220358151856570425)
              ·
                refine ⟨547713915268613892427819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730285220358151856570425 547713915268613892427819)
                ·
                  refine ⟨821570872902920838641729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547713915268613892427819 821570872902920838641729)
                  ·
                    refine ⟨616178154677190628981297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821570872902920838641729 616178154677190628981297)
                    ·
                      refine ⟨462133616007892971735973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616178154677190628981297 462133616007892971735973)
                      ·
                        rfl

theorem cell23_900002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_900002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900002 prefixEnd_900002 := by exact prefixLift 900002
  have htrace : WordTrace (prefixWord ++ tailWord_900002) baseStart_900002 baseEnd_900002 := by
    simpa [prefixWord, tailWord_900002, baseEnd_900002] using wordTrace_append hprefix tailTrace_900002
  have hstable : (prefixWord ++ tailWord_900002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900002).length < 2 ^ (prefixWord ++ tailWord_900002).sum := by decide
  have hdescent : baseEnd_900002 < baseStart_900002 := by decide
  rcases family_descends (prefixWord ++ tailWord_900002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900024 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_900024 : Nat := 118140960795 + 900024 * 2 ^ 59
def prefixEnd_900024 : Nat := 4983230072969 + 3 ^ 40 * 900024 * 2
def baseEnd_900024 : Nat := 462144912582291885660871

theorem tailTrace_900024 : CollatzResearch.WordTrace tailWord_900024 prefixEnd_900024 462144912582291885660871 := by
  unfold tailWord_900024
  simp only [CollatzResearch.WordTrace]
  refine ⟨16413286045687117353341563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21884381394249489804455417 16413286045687117353341563)
  ·
    refine ⟨24619929068530676030012345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16413286045687117353341563 24619929068530676030012345)
    ·
      refine ⟨18464946801398007022509259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24619929068530676030012345 18464946801398007022509259)
      ·
        refine ⟨27697420202097010533763889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18464946801398007022509259 27697420202097010533763889)
        ·
          refine ⟨20773065151572757900322917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27697420202097010533763889 20773065151572757900322917)
          ·
            refine ⟨3894949715919892106310547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20773065151572757900322917 3894949715919892106310547)
            ·
              refine ⟨5842424573879838159465821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894949715919892106310547 5842424573879838159465821)
              ·
                refine ⟨2190909215204939309799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842424573879838159465821 2190909215204939309799683)
                ·
                  refine ⟨3286363822807408964699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2190909215204939309799683 3286363822807408964699525)
                  ·
                    refine ⟨616193216776389180881161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3286363822807408964699525 616193216776389180881161)
                    ·
                      refine ⟨462144912582291885660871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616193216776389180881161 462144912582291885660871)
                      ·
                        rfl

theorem cell23_900024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_900024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900024 prefixEnd_900024 := by exact prefixLift 900024
  have htrace : WordTrace (prefixWord ++ tailWord_900024) baseStart_900024 baseEnd_900024 := by
    simpa [prefixWord, tailWord_900024, baseEnd_900024] using wordTrace_append hprefix tailTrace_900024
  have hstable : (prefixWord ++ tailWord_900024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900024).length < 2 ^ (prefixWord ++ tailWord_900024).sum := by decide
  have hdescent : baseEnd_900024 < baseStart_900024 := by decide
  rcases family_descends (prefixWord ++ tailWord_900024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900058 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_900058 : Nat := 118140960795 + 900058 * 2 ^ 59
def prefixEnd_900058 : Nat := 4983230072969 + 3 ^ 40 * 900058 * 2
def baseEnd_900058 : Nat := 462162370924544752635715

theorem tailTrace_900058 : CollatzResearch.WordTrace tailWord_900058 prefixEnd_900058 462162370924544752635715 := by
  unfold tailWord_900058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206953043312764628355207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21885208115500705675613885 8206953043312764628355207)
  ·
    refine ⟨12310429564969146942532811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8206953043312764628355207 12310429564969146942532811)
    ·
      refine ⟨18465644347453720413799217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12310429564969146942532811 18465644347453720413799217)
      ·
        refine ⟨13849233260590290310349413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18465644347453720413799217 13849233260590290310349413)
        ·
          refine ⟨2596731236360679433190515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13849233260590290310349413 2596731236360679433190515)
          ·
            refine ⟨3895096854541019149785773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596731236360679433190515 3895096854541019149785773)
            ·
              refine ⟨1460661320452882181169665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3895096854541019149785773 1460661320452882181169665)
              ·
                refine ⟨1095495990339661635877249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460661320452882181169665 1095495990339661635877249)
                ·
                  refine ⟨821621992754746226907937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095495990339661635877249 821621992754746226907937)
                  ·
                    refine ⟨616216494566059670180953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821621992754746226907937 616216494566059670180953)
                    ·
                      refine ⟨462162370924544752635715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616216494566059670180953 462162370924544752635715)
                      ·
                        rfl

theorem cell23_900058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_900058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900058 prefixEnd_900058 := by exact prefixLift 900058
  have htrace : WordTrace (prefixWord ++ tailWord_900058) baseStart_900058 baseEnd_900058 := by
    simpa [prefixWord, tailWord_900058, baseEnd_900058] using wordTrace_append hprefix tailTrace_900058
  have hstable : (prefixWord ++ tailWord_900058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900058).length < 2 ^ (prefixWord ++ tailWord_900058).sum := by decide
  have hdescent : baseEnd_900058 < baseStart_900058 := by decide
  rcases family_descends (prefixWord ++ tailWord_900058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900074 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_900074 : Nat := 118140960795 + 900074 * 2 ^ 59
def prefixEnd_900074 : Nat := 4983230072969 + 3 ^ 40 * 900074 * 2
def baseEnd_900074 : Nat := 462170586615016690035641

theorem tailTrace_900074 : CollatzResearch.WordTrace tailWord_900074 prefixEnd_900074 462170586615016690035641 := by
  unfold tailWord_900074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207098935298273311500819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21885597160795395497335517 8207098935298273311500819)
  ·
    refine ⟨12310648402947409967251229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8207098935298273311500819 12310648402947409967251229)
    ·
      refine ⟨4616493151105278737719211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12310648402947409967251229 4616493151105278737719211)
      ·
        refine ⟨6924739726657918106578817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616493151105278737719211 6924739726657918106578817)
        ·
          refine ⟨5193554794993438579934113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924739726657918106578817 5193554794993438579934113)
          ·
            refine ⟨3895166096245078934950585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5193554794993438579934113 3895166096245078934950585)
            ·
              refine ⟨2921374572183809201212939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895166096245078934950585 2921374572183809201212939)
              ·
                refine ⟨4382061858275713801819409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2921374572183809201212939 4382061858275713801819409)
                ·
                  refine ⟨3286546393706785351364557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4382061858275713801819409 3286546393706785351364557)
                  ·
                    refine ⟨1232454897640044506761709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3286546393706785351364557 1232454897640044506761709)
                    ·
                      refine ⟨462170586615016690035641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232454897640044506761709 462170586615016690035641)
                      ·
                        rfl

theorem cell23_900074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_900074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900074 prefixEnd_900074 := by exact prefixLift 900074
  have htrace : WordTrace (prefixWord ++ tailWord_900074) baseStart_900074 baseEnd_900074 := by
    simpa [prefixWord, tailWord_900074, baseEnd_900074] using wordTrace_append hprefix tailTrace_900074
  have hstable : (prefixWord ++ tailWord_900074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900074).length < 2 ^ (prefixWord ++ tailWord_900074).sum := by decide
  have hdescent : baseEnd_900074 < baseStart_900074 := by decide
  rcases family_descends (prefixWord ++ tailWord_900074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900148 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_900148 : Nat := 118140960795 + 900148 * 2 ^ 59
def prefixEnd_900148 : Nat := 4983230072969 + 3 ^ 40 * 900148 * 2
def baseEnd_900148 : Nat := 462208584183449400510301

theorem tailTrace_900148 : CollatzResearch.WordTrace tailWord_900148 prefixEnd_900148 462208584183449400510301 := by
  unfold tailWord_900148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415547371462501942098549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21887396495283335922798065 16415547371462501942098549)
  ·
    refine ⟨1538957566074609557071739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16415547371462501942098549 1538957566074609557071739)
    ·
      refine ⟨2308436349111914335607609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538957566074609557071739 2308436349111914335607609)
      ·
        refine ⟨1731327261833935751705707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2308436349111914335607609 1731327261833935751705707)
        ·
          refine ⟨2596990892750903627558561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731327261833935751705707 2596990892750903627558561)
          ·
            refine ⟨1947743169563177720668921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2596990892750903627558561 1947743169563177720668921)
            ·
              refine ⟨1460807377172383290501691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947743169563177720668921 1460807377172383290501691)
              ·
                refine ⟨2191211065758574935752537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1460807377172383290501691 2191211065758574935752537)
                ·
                  refine ⟨1643408299318931201814403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191211065758574935752537 1643408299318931201814403)
                  ·
                    refine ⟨2465112448978396802721605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643408299318931201814403 2465112448978396802721605)
                    ·
                      refine ⟨462208584183449400510301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2465112448978396802721605 462208584183449400510301)
                      ·
                        rfl

theorem cell23_900148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_900148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900148 prefixEnd_900148 := by exact prefixLift 900148
  have htrace : WordTrace (prefixWord ++ tailWord_900148) baseStart_900148 baseEnd_900148 := by
    simpa [prefixWord, tailWord_900148, baseEnd_900148] using wordTrace_append hprefix tailTrace_900148
  have hstable : (prefixWord ++ tailWord_900148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900148).length < 2 ^ (prefixWord ++ tailWord_900148).sum := by decide
  have hdescent : baseEnd_900148 < baseStart_900148 := by decide
  rcases family_descends (prefixWord ++ tailWord_900148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900181 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_900181 : Nat := 118140960795 + 900181 * 2 ^ 59
def prefixEnd_900181 : Nat := 4983230072969 + 3 ^ 40 * 900181 * 2
def baseEnd_900181 : Nat := 462225529045047771397649

theorem tailTrace_900181 : CollatzResearch.WordTrace tailWord_900181 prefixEnd_900181 462225529045047771397649 := by
  unfold tailWord_900181
  simp only [CollatzResearch.WordTrace]
  refine ⟨32832298351805450520148397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21888198901203633680098931 32832298351805450520148397)
  ·
    refine ⟨12312111881927043945055649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32832298351805450520148397 12312111881927043945055649)
    ·
      refine ⟨9234083911445282958791737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12312111881927043945055649 9234083911445282958791737)
      ·
        refine ⟨6925562933583962219093803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9234083911445282958791737 6925562933583962219093803)
        ·
          refine ⟨10388344400375943328640705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925562933583962219093803 10388344400375943328640705)
          ·
            refine ⟨7791258300281957496480529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10388344400375943328640705 7791258300281957496480529)
            ·
              refine ⟨5843443725211468122360397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791258300281957496480529 5843443725211468122360397)
              ·
                refine ⟨2191291396954300545885149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5843443725211468122360397 2191291396954300545885149)
                ·
                  refine ⟨821734273857862704706931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2191291396954300545885149 821734273857862704706931)
                  ·
                    refine ⟨1232601410786794057060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821734273857862704706931 1232601410786794057060397)
                    ·
                      refine ⟨462225529045047771397649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232601410786794057060397 462225529045047771397649)
                      ·
                        rfl

theorem cell23_900181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_900181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900181 prefixEnd_900181 := by exact prefixLift 900181
  have htrace : WordTrace (prefixWord ++ tailWord_900181) baseStart_900181 baseEnd_900181 := by
    simpa [prefixWord, tailWord_900181, baseEnd_900181] using wordTrace_append hprefix tailTrace_900181
  have hstable : (prefixWord ++ tailWord_900181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900181).length < 2 ^ (prefixWord ++ tailWord_900181).sum := by decide
  have hdescent : baseEnd_900181 < baseStart_900181 := by decide
  rcases family_descends (prefixWord ++ tailWord_900181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900204 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_900204 : Nat := 118140960795 + 900204 * 2 ^ 59
def prefixEnd_900204 : Nat := 4983230072969 + 3 ^ 40 * 900204 * 2
def baseEnd_900204 : Nat := 462237339100101181410043

theorem tailTrace_900204 : CollatzResearch.WordTrace tailWord_900204 prefixEnd_900204 462237339100101181410043 := by
  unfold tailWord_900204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416568615361062724117833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21888758153814750298823777 16416568615361062724117833)
  ·
    refine ⟨12312426461520797043088375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16416568615361062724117833 12312426461520797043088375)
    ·
      refine ⟨18468639692281195564632563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12312426461520797043088375 18468639692281195564632563)
      ·
        refine ⟨27702959538421793346948845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18468639692281195564632563 27702959538421793346948845)
        ·
          refine ⟨10388609826908172505105817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27702959538421793346948845 10388609826908172505105817)
          ·
            refine ⟨7791457370181129378829363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10388609826908172505105817 7791457370181129378829363)
            ·
              refine ⟨11687186055271694068244045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791457370181129378829363 11687186055271694068244045)
              ·
                refine ⟨4382694770726885275591517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11687186055271694068244045 4382694770726885275591517)
                ·
                  refine ⟨1643510539022581978346819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4382694770726885275591517 1643510539022581978346819)
                  ·
                    refine ⟨2465265808533872967520229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643510539022581978346819 2465265808533872967520229)
                    ·
                      refine ⟨462237339100101181410043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2465265808533872967520229 462237339100101181410043)
                      ·
                        rfl

theorem cell23_900204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_900204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900204 prefixEnd_900204 := by exact prefixLift 900204
  have htrace : WordTrace (prefixWord ++ tailWord_900204) baseStart_900204 baseEnd_900204 := by
    simpa [prefixWord, tailWord_900204, baseEnd_900204] using wordTrace_append hprefix tailTrace_900204
  have hstable : (prefixWord ++ tailWord_900204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900204).length < 2 ^ (prefixWord ++ tailWord_900204).sum := by decide
  have hdescent : baseEnd_900204 < baseStart_900204 := by decide
  rcases family_descends (prefixWord ++ tailWord_900204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900221 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_900221 : Nat := 118140960795 + 900221 * 2 ^ 59
def prefixEnd_900221 : Nat := 4983230072969 + 3 ^ 40 * 900221 * 2
def baseEnd_900221 : Nat := 462246068271227614897465

theorem tailTrace_900221 : CollatzResearch.WordTrace tailWord_900221 prefixEnd_900221 462246068271227614897465 := by
  unfold tailWord_900221
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833757271660537351604517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21889171514440358234403011 32833757271660537351604517)
  ·
    refine ⟨6156329488436350753425847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32833757271660537351604517 6156329488436350753425847)
    ·
      refine ⟨9234494232654526130138771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6156329488436350753425847 9234494232654526130138771)
      ·
        refine ⟨13851741348981789195208157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234494232654526130138771 13851741348981789195208157)
        ·
          refine ⟨5194403005868170948203059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13851741348981789195208157 5194403005868170948203059)
          ·
            refine ⟨7791604508802256422304589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194403005868170948203059 7791604508802256422304589)
            ·
              refine ⟨2921851690800846158364221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7791604508802256422304589 2921851690800846158364221)
              ·
                refine ⟨1095694384050317309386583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2921851690800846158364221 1095694384050317309386583)
                ·
                  refine ⟨1643541576075475964079875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095694384050317309386583 1643541576075475964079875)
                  ·
                    refine ⟨2465312364113213946119813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643541576075475964079875 2465312364113213946119813)
                    ·
                      refine ⟨462246068271227614897465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2465312364113213946119813 462246068271227614897465)
                      ·
                        rfl

theorem cell23_900221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_900221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900221 prefixEnd_900221 := by exact prefixLift 900221
  have htrace : WordTrace (prefixWord ++ tailWord_900221) baseStart_900221 baseEnd_900221 := by
    simpa [prefixWord, tailWord_900221, baseEnd_900221] using wordTrace_append hprefix tailTrace_900221
  have hstable : (prefixWord ++ tailWord_900221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900221).length < 2 ^ (prefixWord ++ tailWord_900221).sum := by decide
  have hdescent : baseEnd_900221 < baseStart_900221 := by decide
  rcases family_descends (prefixWord ++ tailWord_900221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900222 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_900222 : Nat := 118140960795 + 900222 * 2 ^ 59
def prefixEnd_900222 : Nat := 4983230072969 + 3 ^ 40 * 900222 * 2
def baseEnd_900222 : Nat := 51360731305764678998329

theorem tailTrace_900222 : CollatzResearch.WordTrace tailWord_900222 prefixEnd_900222 51360731305764678998329 := by
  unfold tailWord_900222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104224218082114315298865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21889195829771276348260613 4104224218082114315298865)
  ·
    refine ⟨3078168163561585736474149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4104224218082114315298865 3078168163561585736474149)
    ·
      refine ⟨577156530667797325588903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3078168163561585736474149 577156530667797325588903)
      ·
        refine ⟨865734796001695988383355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577156530667797325588903 865734796001695988383355)
        ·
          refine ⟨1298602194002543982575033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865734796001695988383355 1298602194002543982575033)
          ·
            refine ⟨973951645501907986931275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298602194002543982575033 973951645501907986931275)
            ·
              refine ⟨1460927468252861980396913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973951645501907986931275 1460927468252861980396913)
              ·
                refine ⟨1095695601189646485297685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460927468252861980396913 1095695601189646485297685)
                ·
                  refine ⟨51360731305764678998329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1095695601189646485297685 51360731305764678998329)
                  ·
                    rfl

theorem cell23_900222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_900222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900222 prefixEnd_900222 := by exact prefixLift 900222
  have htrace : WordTrace (prefixWord ++ tailWord_900222) baseStart_900222 baseEnd_900222 := by
    simpa [prefixWord, tailWord_900222, baseEnd_900222] using wordTrace_append hprefix tailTrace_900222
  have hstable : (prefixWord ++ tailWord_900222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900222).length < 2 ^ (prefixWord ++ tailWord_900222).sum := by decide
  have hdescent : baseEnd_900222 < baseStart_900222 := by decide
  rcases family_descends (prefixWord ++ tailWord_900222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900227 : List Nat := [1, 1, 1, 3, 3, 2, 12]
def baseStart_900227 : Nat := 118140960795 + 900227 * 2 ^ 59
def prefixEnd_900227 : Nat := 4983230072969 + 3 ^ 40 * 900227 * 2
def baseEnd_900227 : Nat := 5706779619199439400277

theorem tailTrace_900227 : CollatzResearch.WordTrace tailWord_900227 prefixEnd_900227 5706779619199439400277 := by
  unfold tailWord_900227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32833976109638800376322935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21889317406425866917548623 32833976109638800376322935)
  ·
    refine ⟨49250964164458200564484403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32833976109638800376322935 49250964164458200564484403)
    ·
      refine ⟨73876446246687300846726605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49250964164458200564484403 73876446246687300846726605)
      ·
        refine ⟨27703667342507737817522477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73876446246687300846726605 27703667342507737817522477)
        ·
          refine ⟨10388875253440401681570929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27703667342507737817522477 10388875253440401681570929)
          ·
            refine ⟨7791656440080301261178197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10388875253440401681570929 7791656440080301261178197)
            ·
              refine ⟨5706779619199439400277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 7791656440080301261178197 5706779619199439400277)
              ·
                rfl

theorem cell23_900227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 12].length) (baseStart_900227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900227 prefixEnd_900227 := by exact prefixLift 900227
  have htrace : WordTrace (prefixWord ++ tailWord_900227) baseStart_900227 baseEnd_900227 := by
    simpa [prefixWord, tailWord_900227, baseEnd_900227] using wordTrace_append hprefix tailTrace_900227
  have hstable : (prefixWord ++ tailWord_900227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900227).length < 2 ^ (prefixWord ++ tailWord_900227).sum := by decide
  have hdescent : baseEnd_900227 < baseStart_900227 := by decide
  rcases family_descends (prefixWord ++ tailWord_900227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900234 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_900234 : Nat := 118140960795 + 900234 * 2 ^ 59
def prefixEnd_900234 : Nat := 4983230072969 + 3 ^ 40 * 900234 * 2
def baseEnd_900234 : Nat := 462252743519736064034905

theorem tailTrace_900234 : CollatzResearch.WordTrace tailWord_900234 prefixEnd_900234 462252743519736064034905 := by
  unfold tailWord_900234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8208557855153360142956939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21889487613742293714551837 8208557855153360142956939)
  ·
    refine ⟨12312836782730040214435409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8208557855153360142956939 12312836782730040214435409)
    ·
      refine ⟨9234627587047530160826557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12312836782730040214435409 9234627587047530160826557)
      ·
        refine ⟨3462985345142823810309959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9234627587047530160826557 3462985345142823810309959)
        ·
          refine ⟨5194478017714235715464939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3462985345142823810309959 5194478017714235715464939)
          ·
            refine ⟨7791717026571353573197409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5194478017714235715464939 7791717026571353573197409)
            ·
              refine ⟨5843787769928515179898057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7791717026571353573197409 5843787769928515179898057)
              ·
                refine ⟨4382840827446386384923543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5843787769928515179898057 4382840827446386384923543)
                ·
                  refine ⟨6574261241169579577385315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382840827446386384923543 6574261241169579577385315)
                  ·
                    refine ⟨9861391861754369366077973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6574261241169579577385315 9861391861754369366077973)
                    ·
                      refine ⟨462252743519736064034905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9861391861754369366077973 462252743519736064034905)
                      ·
                        rfl

theorem cell23_900234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_900234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900234 prefixEnd_900234 := by exact prefixLift 900234
  have htrace : WordTrace (prefixWord ++ tailWord_900234) baseStart_900234 baseEnd_900234 := by
    simpa [prefixWord, tailWord_900234, baseEnd_900234] using wordTrace_append hprefix tailTrace_900234
  have hstable : (prefixWord ++ tailWord_900234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900234).length < 2 ^ (prefixWord ++ tailWord_900234).sum := by decide
  have hdescent : baseEnd_900234 < baseStart_900234 := by decide
  rcases family_descends (prefixWord ++ tailWord_900234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900261 : List Nat := [1, 3, 1, 2, 1, 6, 2, 7]
def baseStart_900261 : Nat := 118140960795 + 900261 * 2 ^ 59
def prefixEnd_900261 : Nat := 4983230072969 + 3 ^ 40 * 900261 * 2
def baseEnd_900261 : Nat := 17120985462866942903603

theorem tailTrace_900261 : CollatzResearch.WordTrace tailWord_900261 prefixEnd_900261 17120985462866942903603 := by
  unfold tailWord_900261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32835216191515624183060637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21890144127677082788707091 32835216191515624183060637)
  ·
    refine ⟨12313206071818359068647739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32835216191515624183060637 12313206071818359068647739)
    ·
      refine ⟨18469809107727538602971609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12313206071818359068647739 18469809107727538602971609)
      ·
        refine ⟨13852356830795653952228707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18469809107727538602971609 13852356830795653952228707)
        ·
          refine ⟨20778535246193480928343061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13852356830795653952228707 20778535246193480928343061)
          ·
            refine ⟨973993839665319418516081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20778535246193480928343061 973993839665319418516081)
            ·
              refine ⟨730495379748989563887061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973993839665319418516081 730495379748989563887061)
              ·
                refine ⟨17120985462866942903603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 730495379748989563887061 17120985462866942903603)
                ·
                  rfl

theorem cell23_900261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 7].length) (baseStart_900261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900261 prefixEnd_900261 := by exact prefixLift 900261
  have htrace : WordTrace (prefixWord ++ tailWord_900261) baseStart_900261 baseEnd_900261 := by
    simpa [prefixWord, tailWord_900261, baseEnd_900261] using wordTrace_append hprefix tailTrace_900261
  have hstable : (prefixWord ++ tailWord_900261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900261).length < 2 ^ (prefixWord ++ tailWord_900261).sum := by decide
  have hdescent : baseEnd_900261 < baseStart_900261 := by decide
  rcases family_descends (prefixWord ++ tailWord_900261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900271 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_900271 : Nat := 118140960795 + 900271 * 2 ^ 59
def prefixEnd_900271 : Nat := 4983230072969 + 3 ^ 40 * 900271 * 2
def baseEnd_900271 : Nat := 462271742303952419272235

theorem tailTrace_900271 : CollatzResearch.WordTrace tailWord_900271 prefixEnd_900271 462271742303952419272235 := by
  unfold tailWord_900271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32835580921479395890924667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21890387280986263927283111 32835580921479395890924667)
  ·
    refine ⟨49253371382219093836387001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32835580921479395890924667 49253371382219093836387001)
    ·
      refine ⟨36940028536664320377290251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49253371382219093836387001 36940028536664320377290251)
      ·
        refine ⟨55410042804996480565935377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36940028536664320377290251 55410042804996480565935377)
        ·
          refine ⟨41557532103747360424451533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55410042804996480565935377 41557532103747360424451533)
          ·
            refine ⟨15584074538905260159169325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41557532103747360424451533 15584074538905260159169325)
            ·
              refine ⟨5844027952089472559688497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15584074538905260159169325 5844027952089472559688497)
              ·
                refine ⟨4383020964067104419766373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5844027952089472559688497 4383020964067104419766373)
                ·
                  refine ⟨821816430762582078706195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4383020964067104419766373 821816430762582078706195)
                  ·
                    refine ⟨1232724646143873118059293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 821816430762582078706195 1232724646143873118059293)
                    ·
                      refine ⟨462271742303952419272235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232724646143873118059293 462271742303952419272235)
                      ·
                        rfl

theorem cell23_900271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_900271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900271 prefixEnd_900271 := by exact prefixLift 900271
  have htrace : WordTrace (prefixWord ++ tailWord_900271) baseStart_900271 baseEnd_900271 := by
    simpa [prefixWord, tailWord_900271, baseEnd_900271] using wordTrace_append hprefix tailTrace_900271
  have hstable : (prefixWord ++ tailWord_900271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900271).length < 2 ^ (prefixWord ++ tailWord_900271).sum := by decide
  have hdescent : baseEnd_900271 < baseStart_900271 := by decide
  rcases family_descends (prefixWord ++ tailWord_900271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900328 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_900328 : Nat := 118140960795 + 900328 * 2 ^ 59
def prefixEnd_900328 : Nat := 4983230072969 + 3 ^ 40 * 900328 * 2
def baseEnd_900328 : Nat := 462301010701258696259473

theorem tailTrace_900328 : CollatzResearch.WordTrace tailWord_900328 prefixEnd_900328 462301010701258696259473 := by
  unfold tailWord_900328
  simp only [CollatzResearch.WordTrace]
  refine ⟨16418829941136447312874819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21891773254848596417166425 16418829941136447312874819)
  ·
    refine ⟨24628244911704670969312229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16418829941136447312874819 24628244911704670969312229)
    ·
      refine ⟨4617795920944625806746043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24628244911704670969312229 4617795920944625806746043)
      ·
        refine ⟨6926693881416938710119065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4617795920944625806746043 6926693881416938710119065)
        ·
          refine ⟨5195020411062704032589299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6926693881416938710119065 5195020411062704032589299)
          ·
            refine ⟨7792530616594056048883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195020411062704032589299 7792530616594056048883949)
            ·
              refine ⟨2922198981222771018331481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7792530616594056048883949 2922198981222771018331481)
              ·
                refine ⟨2191649235917078263748611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922198981222771018331481 2191649235917078263748611)
                ·
                  refine ⟨3287473853875617395622917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2191649235917078263748611 3287473853875617395622917)
                  ·
                    refine ⟨616401347601678261679297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3287473853875617395622917 616401347601678261679297)
                    ·
                      refine ⟨462301010701258696259473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616401347601678261679297 462301010701258696259473)
                      ·
                        rfl

theorem cell23_900328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_900328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900328 prefixEnd_900328 := by exact prefixLift 900328
  have htrace : WordTrace (prefixWord ++ tailWord_900328) baseStart_900328 baseEnd_900328 := by
    simpa [prefixWord, tailWord_900328, baseEnd_900328] using wordTrace_append hprefix tailTrace_900328
  have hstable : (prefixWord ++ tailWord_900328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900328).length < 2 ^ (prefixWord ++ tailWord_900328).sum := by decide
  have hdescent : baseEnd_900328 < baseStart_900328 := by decide
  rcases family_descends (prefixWord ++ tailWord_900328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900340 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_900340 : Nat := 118140960795 + 900340 * 2 ^ 59
def prefixEnd_900340 : Nat := 4983230072969 + 3 ^ 40 * 900340 * 2
def baseEnd_900340 : Nat := 462307172469112649309419

theorem tailTrace_900340 : CollatzResearch.WordTrace tailWord_900340 prefixEnd_900340 462307172469112649309419 := by
  unfold tailWord_900340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419048779114710337593237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21892065038819613783457649 16419048779114710337593237)
  ·
    refine ⟨769642911521002047074683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16419048779114710337593237 769642911521002047074683)
    ·
      refine ⟨1154464367281503070612025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769642911521002047074683 1154464367281503070612025)
      ·
        refine ⟨865848275461127302959019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1154464367281503070612025 865848275461127302959019)
        ·
          refine ⟨1298772413191690954438529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865848275461127302959019 1298772413191690954438529)
          ·
            refine ⟨974079309893768215828897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298772413191690954438529 974079309893768215828897)
            ·
              refine ⟨730559482420326161871673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974079309893768215828897 730559482420326161871673)
              ·
                refine ⟨547919611815244621403755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730559482420326161871673 547919611815244621403755)
                ·
                  refine ⟨821879417722866932105633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547919611815244621403755 821879417722866932105633)
                  ·
                    refine ⟨616409563292150199079225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821879417722866932105633 616409563292150199079225)
                    ·
                      refine ⟨462307172469112649309419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616409563292150199079225 462307172469112649309419)
                      ·
                        rfl

theorem cell23_900340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_900340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900340 prefixEnd_900340 := by exact prefixLift 900340
  have htrace : WordTrace (prefixWord ++ tailWord_900340) baseStart_900340 baseEnd_900340 := by
    simpa [prefixWord, tailWord_900340, baseEnd_900340] using wordTrace_append hprefix tailTrace_900340
  have hstable : (prefixWord ++ tailWord_900340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900340).length < 2 ^ (prefixWord ++ tailWord_900340).sum := by decide
  have hdescent : baseEnd_900340 < baseStart_900340 := by decide
  rcases family_descends (prefixWord ++ tailWord_900340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900345 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 2, 2, 2]
def baseStart_900345 : Nat := 118140960795 + 900345 * 2 ^ 59
def prefixEnd_900345 : Nat := 4983230072969 + 3 ^ 40 * 900345 * 2
def baseEnd_900345 : Nat := 462309739872385129746895

theorem tailTrace_900345 : CollatzResearch.WordTrace tailWord_900345 prefixEnd_900345 462309739872385129746895 := by
  unfold tailWord_900345
  simp only [CollatzResearch.WordTrace]
  refine ⟨32838279923211306529118489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21892186615474204352745659 32838279923211306529118489)
  ·
    refine ⟨24628709942408479896838867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32838279923211306529118489 24628709942408479896838867)
    ·
      refine ⟨36943064913612719845258301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24628709942408479896838867 36943064913612719845258301)
      ·
        refine ⟨13853649342604769941971863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36943064913612719845258301 13853649342604769941971863)
        ·
          refine ⟨20780474013907154912957795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13853649342604769941971863 20780474013907154912957795)
          ·
            refine ⟨31170711020860732369436693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20780474013907154912957795 31170711020860732369436693)
            ·
              refine ⟨1461127079102846829817345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31170711020860732369436693 1461127079102846829817345)
              ·
                refine ⟨1095845309327135122363009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461127079102846829817345 1095845309327135122363009)
                ·
                  refine ⟨821883981995351341772257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095845309327135122363009 821883981995351341772257)
                  ·
                    refine ⟨616412986496513506329193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821883981995351341772257 616412986496513506329193)
                    ·
                      refine ⟨462309739872385129746895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616412986496513506329193 462309739872385129746895)
                      ·
                        rfl

theorem cell23_900345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_900345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900345 prefixEnd_900345 := by exact prefixLift 900345
  have htrace : WordTrace (prefixWord ++ tailWord_900345) baseStart_900345 baseEnd_900345 := by
    simpa [prefixWord, tailWord_900345, baseEnd_900345] using wordTrace_append hprefix tailTrace_900345
  have hstable : (prefixWord ++ tailWord_900345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900345).length < 2 ^ (prefixWord ++ tailWord_900345).sum := by decide
  have hdescent : baseEnd_900345 < baseStart_900345 := by decide
  rcases family_descends (prefixWord ++ tailWord_900345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900361 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_900361 : Nat := 118140960795 + 900361 * 2 ^ 59
def prefixEnd_900361 : Nat := 4983230072969 + 3 ^ 40 * 900361 * 2
def baseEnd_900361 : Nat := 462317955562857067146821

theorem tailTrace_900361 : CollatzResearch.WordTrace tailWord_900361 prefixEnd_900361 462317955562857067146821 := by
  unfold tailWord_900361
  simp only [CollatzResearch.WordTrace]
  refine ⟨32838863491153341261700937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21892575660768894174467291 32838863491153341261700937)
  ·
    refine ⟨24629147618365005946275703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32838863491153341261700937 24629147618365005946275703)
    ·
      refine ⟨36943721427547508919413555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24629147618365005946275703 36943721427547508919413555)
      ·
        refine ⟨55415582141321263379120333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36943721427547508919413555 55415582141321263379120333)
        ·
          refine ⟨20780843302995473767170125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55415582141321263379120333 20780843302995473767170125)
          ·
            refine ⟨7792816238623302662688797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20780843302995473767170125 7792816238623302662688797)
            ·
              refine ⟨2922306089483738498508299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7792816238623302662688797 2922306089483738498508299)
              ·
                refine ⟨4383459134225607747762449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922306089483738498508299 4383459134225607747762449)
                ·
                  refine ⟨3287594350669205810821837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4383459134225607747762449 3287594350669205810821837)
                  ·
                    refine ⟨1232847881500952179058189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3287594350669205810821837 1232847881500952179058189)
                    ·
                      refine ⟨462317955562857067146821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232847881500952179058189 462317955562857067146821)
                      ·
                        rfl

theorem cell23_900361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_900361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900361 prefixEnd_900361 := by exact prefixLift 900361
  have htrace : WordTrace (prefixWord ++ tailWord_900361) baseStart_900361 baseEnd_900361 := by
    simpa [prefixWord, tailWord_900361, baseEnd_900361] using wordTrace_append hprefix tailTrace_900361
  have hstable : (prefixWord ++ tailWord_900361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900361).length < 2 ^ (prefixWord ++ tailWord_900361).sum := by decide
  have hdescent : baseEnd_900361 < baseStart_900361 := by decide
  rcases family_descends (prefixWord ++ tailWord_900361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900428 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_900428 : Nat := 118140960795 + 900428 * 2 ^ 59
def prefixEnd_900428 : Nat := 4983230072969 + 3 ^ 40 * 900428 * 2
def baseEnd_900428 : Nat := 154117452922236101669671

theorem tailTrace_900428 : CollatzResearch.WordTrace tailWord_900428 prefixEnd_900428 154117452922236101669671 := by
  unfold tailWord_900428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16420653590955305852194969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21894204787940407802926625 16420653590955305852194969)
  ·
    refine ⟨12315490193216479389146227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16420653590955305852194969 12315490193216479389146227)
    ·
      refine ⟨18473235289824719083719341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12315490193216479389146227 18473235289824719083719341)
      ·
        refine ⟨6927463233684269656394753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18473235289824719083719341 6927463233684269656394753)
        ·
          refine ⟨5195597425263202242296065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6927463233684269656394753 5195597425263202242296065)
          ·
            refine ⟨3896698068947401681722049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5195597425263202242296065 3896698068947401681722049)
            ·
              refine ⟨2922523551710551261291537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896698068947401681722049 2922523551710551261291537)
              ·
                refine ⟨2191892663782913445968653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922523551710551261291537 2191892663782913445968653)
                ·
                  refine ⟨821959748918592542238245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2191892663782913445968653 821959748918592542238245)
                  ·
                    refine ⟨154117452922236101669671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 821959748918592542238245 154117452922236101669671)
                    ·
                      rfl

theorem cell23_900428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_900428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900428 prefixEnd_900428 := by exact prefixLift 900428
  have htrace : WordTrace (prefixWord ++ tailWord_900428) baseStart_900428 baseEnd_900428 := by
    simpa [prefixWord, tailWord_900428, baseEnd_900428] using wordTrace_append hprefix tailTrace_900428
  have hstable : (prefixWord ++ tailWord_900428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900428).length < 2 ^ (prefixWord ++ tailWord_900428).sum := by decide
  have hdescent : baseEnd_900428 < baseStart_900428 := by decide
  rcases family_descends (prefixWord ++ tailWord_900428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900455 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_900455 : Nat := 118140960795 + 900455 * 2 ^ 59
def prefixEnd_900455 : Nat := 4983230072969 + 3 ^ 40 * 900455 * 2
def baseEnd_900455 : Nat := 462366222744379699371389

theorem tailTrace_900455 : CollatzResearch.WordTrace tailWord_900455 prefixEnd_900455 462366222744379699371389 := by
  unfold tailWord_900455
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842291952812795315622819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21894861301875196877081879 32842291952812795315622819)
  ·
    refine ⟨49263437929219192973434229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32842291952812795315622819 49263437929219192973434229)
    ·
      refine ⟨4618447305864299341259459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49263437929219192973434229 4618447305864299341259459)
      ·
        refine ⟨6927670958796449011889189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618447305864299341259459 6927670958796449011889189)
        ·
          refine ⟨1298938304774334189729223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6927670958796449011889189 1298938304774334189729223)
          ·
            refine ⟨1948407457161501284593835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298938304774334189729223 1948407457161501284593835)
            ·
              refine ⟨2922611185742251926890753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948407457161501284593835 2922611185742251926890753)
              ·
                refine ⟨2191958389306688945168065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922611185742251926890753 2191958389306688945168065)
                ·
                  refine ⟨1643968791980016708876049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2191958389306688945168065 1643968791980016708876049)
                  ·
                    refine ⟨1232976593985012531657037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1643968791980016708876049 1232976593985012531657037)
                    ·
                      refine ⟨462366222744379699371389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1232976593985012531657037 462366222744379699371389)
                      ·
                        rfl

theorem cell23_900455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_900455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900455 prefixEnd_900455 := by exact prefixLift 900455
  have htrace : WordTrace (prefixWord ++ tailWord_900455) baseStart_900455 baseEnd_900455 := by
    simpa [prefixWord, tailWord_900455, baseEnd_900455] using wordTrace_append hprefix tailTrace_900455
  have hstable : (prefixWord ++ tailWord_900455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900455).length < 2 ^ (prefixWord ++ tailWord_900455).sum := by decide
  have hdescent : baseEnd_900455 < baseStart_900455 := by decide
  rcases family_descends (prefixWord ++ tailWord_900455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900471 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 3, 5]
def baseStart_900471 : Nat := 118140960795 + 900471 * 2 ^ 59
def prefixEnd_900471 : Nat := 4983230072969 + 3 ^ 40 * 900471 * 2
def baseEnd_900471 : Nat := 154124812811617212257105

theorem tailTrace_900471 : CollatzResearch.WordTrace tailWord_900471 prefixEnd_900471 154124812811617212257105 := by
  unfold tailWord_900471
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842875520754830048205267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21895250347169886698803511 32842875520754830048205267)
  ·
    refine ⟨49264313281132245072307901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32842875520754830048205267 49264313281132245072307901)
    ·
      refine ⟨18474117480424591902115463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49264313281132245072307901 18474117480424591902115463)
      ·
        refine ⟨27711176220636887853173195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18474117480424591902115463 27711176220636887853173195)
        ·
          refine ⟨41566764330955331779759793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27711176220636887853173195 41566764330955331779759793)
          ·
            refine ⟨31175073248216498834819845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41566764330955331779759793 31175073248216498834819845)
            ·
              refine ⟨5845326234040593531528721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31175073248216498834819845 5845326234040593531528721)
              ·
                refine ⟨4383994675530445148646541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845326234040593531528721 4383994675530445148646541)
                ·
                  refine ⟨1643998003323916930742453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4383994675530445148646541 1643998003323916930742453)
                  ·
                    refine ⟨154124812811617212257105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1643998003323916930742453 154124812811617212257105)
                    ·
                      rfl

theorem cell23_900471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_900471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900471 prefixEnd_900471 := by exact prefixLift 900471
  have htrace : WordTrace (prefixWord ++ tailWord_900471) baseStart_900471 baseEnd_900471 := by
    simpa [prefixWord, tailWord_900471, baseEnd_900471] using wordTrace_append hprefix tailTrace_900471
  have hstable : (prefixWord ++ tailWord_900471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900471).length < 2 ^ (prefixWord ++ tailWord_900471).sum := by decide
  have hdescent : baseEnd_900471 < baseStart_900471 := by decide
  rcases family_descends (prefixWord ++ tailWord_900471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900488 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_900488 : Nat := 118140960795 + 900488 * 2 ^ 59
def prefixEnd_900488 : Nat := 4983230072969 + 3 ^ 40 * 900488 * 2
def baseEnd_900488 : Nat := 154127722535326023419579

theorem tailTrace_900488 : CollatzResearch.WordTrace tailWord_900488 prefixEnd_900488 154127722535326023419579 := by
  unfold tailWord_900488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16421747780846620975787059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21895663707795494634382745 16421747780846620975787059)
  ·
    refine ⟨24632621671269931463680589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16421747780846620975787059 24632621671269931463680589)
    ·
      refine ⟨9237233126726224298880221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24632621671269931463680589 9237233126726224298880221)
      ·
        refine ⟨3463962422522334112080083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9237233126726224298880221 3463962422522334112080083)
        ·
          refine ⟨5195943633783501168120125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3463962422522334112080083 5195943633783501168120125)
          ·
            refine ⟨1948478862668812938045047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5195943633783501168120125 1948478862668812938045047)
            ·
              refine ⟨2922718294003219407067571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948478862668812938045047 2922718294003219407067571)
              ·
                refine ⟨4384077441004829110601357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922718294003219407067571 4384077441004829110601357)
                ·
                  refine ⟨1644029040376810916475509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384077441004829110601357 1644029040376810916475509)
                  ·
                    refine ⟨154127722535326023419579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1644029040376810916475509 154127722535326023419579)
                    ·
                      rfl

theorem cell23_900488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_900488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900488 prefixEnd_900488 := by exact prefixLift 900488
  have htrace : WordTrace (prefixWord ++ tailWord_900488) baseStart_900488 baseEnd_900488 := by
    simpa [prefixWord, tailWord_900488, baseEnd_900488] using wordTrace_append hprefix tailTrace_900488
  have hstable : (prefixWord ++ tailWord_900488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900488).length < 2 ^ (prefixWord ++ tailWord_900488).sum := by decide
  have hdescent : baseEnd_900488 < baseStart_900488 := by decide
  rcases family_descends (prefixWord ++ tailWord_900488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900501 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_900501 : Nat := 118140960795 + 900501 * 2 ^ 59
def prefixEnd_900501 : Nat := 4983230072969 + 3 ^ 40 * 900501 * 2
def baseEnd_900501 : Nat := 154129947618162173132059

theorem tailTrace_900501 : CollatzResearch.WordTrace tailWord_900501 prefixEnd_900501 154129947618162173132059 := by
  unfold tailWord_900501
  simp only [CollatzResearch.WordTrace]
  refine ⟨32843969710646145171797357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21895979807097430114531571 32843969710646145171797357)
  ·
    refine ⟨12316488641492304439424009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32843969710646145171797357 12316488641492304439424009)
    ·
      refine ⟨9237366481119228329568007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12316488641492304439424009 9237366481119228329568007)
      ·
        refine ⟨13856049721678842494352011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9237366481119228329568007 13856049721678842494352011)
        ·
          refine ⟨20784074582518263741528017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13856049721678842494352011 20784074582518263741528017)
          ·
            refine ⟨15588055936888697806146013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20784074582518263741528017 15588055936888697806146013)
            ·
              refine ⟨5845520976333261677304755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15588055936888697806146013 5845520976333261677304755)
              ·
                refine ⟨8768281464499892515957133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5845520976333261677304755 8768281464499892515957133)
                ·
                  refine ⟨3288105549187459693483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8768281464499892515957133 3288105549187459693483925)
                  ·
                    refine ⟨154129947618162173132059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3288105549187459693483925 154129947618162173132059)
                    ·
                      rfl

theorem cell23_900501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_900501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900501 prefixEnd_900501 := by exact prefixLift 900501
  have htrace : WordTrace (prefixWord ++ tailWord_900501) baseStart_900501 baseEnd_900501 := by
    simpa [prefixWord, tailWord_900501, baseEnd_900501] using wordTrace_append hprefix tailTrace_900501
  have hstable : (prefixWord ++ tailWord_900501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900501).length < 2 ^ (prefixWord ++ tailWord_900501).sum := by decide
  have hdescent : baseEnd_900501 < baseStart_900501 := by decide
  rcases family_descends (prefixWord ++ tailWord_900501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900505 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_900505 : Nat := 118140960795 + 900505 * 2 ^ 59
def prefixEnd_900505 : Nat := 4983230072969 + 3 ^ 40 * 900505 * 2
def baseEnd_900505 : Nat := 154130632259034834582053

theorem tailTrace_900505 : CollatzResearch.WordTrace tailWord_900505 prefixEnd_900505 154130632259034834582053 := by
  unfold tailWord_900505
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844115602631653854942969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21896077068421102569961979 32844115602631653854942969)
  ·
    refine ⟨24633086701973740391207227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32844115602631653854942969 24633086701973740391207227)
    ·
      refine ⟨36949630052960610586810841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24633086701973740391207227 36949630052960610586810841)
      ·
        refine ⟨27712222539720457940108131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36949630052960610586810841 27712222539720457940108131)
        ·
          refine ⟨41568333809580686910162197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27712222539720457940108131 41568333809580686910162197)
          ·
            refine ⟨1948515647324094698913853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41568333809580686910162197 1948515647324094698913853)
            ·
              refine ⟨730693367746535512092695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948515647324094698913853 730693367746535512092695)
              ·
                refine ⟨1096040051619803268139043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730693367746535512092695 1096040051619803268139043)
                ·
                  refine ⟨1644060077429704902208565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096040051619803268139043 1644060077429704902208565)
                  ·
                    refine ⟨154130632259034834582053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1644060077429704902208565 154130632259034834582053)
                    ·
                      rfl

theorem cell23_900505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_900505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900505 prefixEnd_900505 := by exact prefixLift 900505
  have htrace : WordTrace (prefixWord ++ tailWord_900505) baseStart_900505 baseEnd_900505 := by
    simpa [prefixWord, tailWord_900505, baseEnd_900505] using wordTrace_append hprefix tailTrace_900505
  have hstable : (prefixWord ++ tailWord_900505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900505).length < 2 ^ (prefixWord ++ tailWord_900505).sum := by decide
  have hdescent : baseEnd_900505 < baseStart_900505 := by decide
  rcases family_descends (prefixWord ++ tailWord_900505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900525 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_900525 : Nat := 118140960795 + 900525 * 2 ^ 59
def prefixEnd_900525 : Nat := 4983230072969 + 3 ^ 40 * 900525 * 2
def baseEnd_900525 : Nat := 462402166390194425496067

theorem tailTrace_900525 : CollatzResearch.WordTrace tailWord_900525 prefixEnd_900525 462402166390194425496067 := by
  unfold tailWord_900525
  simp only [CollatzResearch.WordTrace]
  refine ⟨32844845062559197270671029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21896563375039464847114019 32844845062559197270671029)
  ·
    refine ⟨3079204224614924744125409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32844845062559197270671029 3079204224614924744125409)
    ·
      refine ⟨2309403168461193558094057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3079204224614924744125409 2309403168461193558094057)
      ·
        refine ⟨1732052376345895168570543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309403168461193558094057 1732052376345895168570543)
        ·
          refine ⟨2598078564518842752855815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732052376345895168570543 2598078564518842752855815)
          ·
            refine ⟨3897117846778264129283723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598078564518842752855815 3897117846778264129283723)
            ·
              refine ⟨5845676770167396193925585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897117846778264129283723 5845676770167396193925585)
              ·
                refine ⟨4384257577625547145444189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5845676770167396193925585 4384257577625547145444189)
                ·
                  refine ⟨1644096591609580179541571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4384257577625547145444189 1644096591609580179541571)
                  ·
                    refine ⟨2466144887414370269312357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644096591609580179541571 2466144887414370269312357)
                    ·
                      refine ⟨462402166390194425496067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2466144887414370269312357 462402166390194425496067)
                      ·
                        rfl

theorem cell23_900525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_900525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900525 prefixEnd_900525 := by exact prefixLift 900525
  have htrace : WordTrace (prefixWord ++ tailWord_900525) baseStart_900525 baseEnd_900525 := by
    simpa [prefixWord, tailWord_900525, baseEnd_900525] using wordTrace_append hprefix tailTrace_900525
  have hstable : (prefixWord ++ tailWord_900525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900525).length < 2 ^ (prefixWord ++ tailWord_900525).sum := by decide
  have hdescent : baseEnd_900525 < baseStart_900525 := by decide
  rcases family_descends (prefixWord ++ tailWord_900525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900575 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_900575 : Nat := 118140960795 + 900575 * 2 ^ 59
def prefixEnd_900575 : Nat := 4983230072969 + 3 ^ 40 * 900575 * 2
def baseEnd_900575 : Nat := 462427840422919229870837

theorem tailTrace_900575 : CollatzResearch.WordTrace tailWord_900575 prefixEnd_900575 462427840422919229870837 := by
  unfold tailWord_900575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846668712378055809991179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21897779141585370539994119 32846668712378055809991179)
  ·
    refine ⟨49270003068567083714986769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32846668712378055809991179 49270003068567083714986769)
    ·
      refine ⟨36952502301425312786240077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49270003068567083714986769 36952502301425312786240077)
      ·
        refine ⟨13857188363034492294840029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36952502301425312786240077 13857188363034492294840029)
        ·
          refine ⟨5196445636137934610565011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13857188363034492294840029 5196445636137934610565011)
          ·
            refine ⟨7794668454206901915847517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5196445636137934610565011 7794668454206901915847517)
            ·
              refine ⟨2923000670327588218442819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7794668454206901915847517 2923000670327588218442819)
              ·
                refine ⟨4384501005491382327664229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923000670327588218442819 4384501005491382327664229)
                ·
                  refine ⟨822093938529634186437043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4384501005491382327664229 822093938529634186437043)
                  ·
                    refine ⟨1233140907794451279655565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822093938529634186437043 1233140907794451279655565)
                    ·
                      refine ⟨462427840422919229870837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1233140907794451279655565 462427840422919229870837)
                      ·
                        rfl

theorem cell23_900575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_900575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900575 prefixEnd_900575 := by exact prefixLift 900575
  have htrace : WordTrace (prefixWord ++ tailWord_900575) baseStart_900575 baseEnd_900575 := by
    simpa [prefixWord, tailWord_900575, baseEnd_900575] using wordTrace_append hprefix tailTrace_900575
  have hstable : (prefixWord ++ tailWord_900575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900575).length < 2 ^ (prefixWord ++ tailWord_900575).sum := by decide
  have hdescent : baseEnd_900575 < baseStart_900575 := by decide
  rcases family_descends (prefixWord ++ tailWord_900575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900589 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_900589 : Nat := 118140960795 + 900589 * 2 ^ 59
def prefixEnd_900589 : Nat := 4983230072969 + 3 ^ 40 * 900589 * 2
def baseEnd_900589 : Nat := 462435029152082175095773

theorem tailTrace_900589 : CollatzResearch.WordTrace tailWord_900589 prefixEnd_900589 462435029152082175095773 := by
  unfold tailWord_900589
  simp only [CollatzResearch.WordTrace]
  refine ⟨32847179334327336201000821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21898119556218224134000547 32847179334327336201000821)
  ·
    refine ⟨3079423062593187768843827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32847179334327336201000821 3079423062593187768843827)
    ·
      refine ⟨4619134593889781653265741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079423062593187768843827 4619134593889781653265741)
      ·
        refine ⟨1732175472708668119974653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4619134593889781653265741 1732175472708668119974653)
        ·
          refine ⟨649565802265750544990495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1732175472708668119974653 649565802265750544990495)
          ·
            refine ⟨974348703398625817485743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649565802265750544990495 974348703398625817485743)
            ·
              refine ⟨1461523055097938726228615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974348703398625817485743 1461523055097938726228615)
              ·
                refine ⟨2192284582646908089342923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461523055097938726228615 2192284582646908089342923)
                ·
                  refine ⟨3288426873970362134014385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192284582646908089342923 3288426873970362134014385)
                  ·
                    refine ⟨2466320155477771600510789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3288426873970362134014385 2466320155477771600510789)
                    ·
                      refine ⟨462435029152082175095773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2466320155477771600510789 462435029152082175095773)
                      ·
                        rfl

theorem cell23_900589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_900589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900589 prefixEnd_900589 := by exact prefixLift 900589
  have htrace : WordTrace (prefixWord ++ tailWord_900589) baseStart_900589 baseEnd_900589 := by
    simpa [prefixWord, tailWord_900589, baseEnd_900589] using wordTrace_append hprefix tailTrace_900589
  have hstable : (prefixWord ++ tailWord_900589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900589).length < 2 ^ (prefixWord ++ tailWord_900589).sum := by decide
  have hdescent : baseEnd_900589 < baseStart_900589 := by decide
  rcases family_descends (prefixWord ++ tailWord_900589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900602 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_900602 : Nat := 118140960795 + 900602 * 2 ^ 59
def prefixEnd_900602 : Nat := 4983230072969 + 3 ^ 40 * 900602 * 2
def baseEnd_900602 : Nat := 462441704400590624233213

theorem tailTrace_900602 : CollatzResearch.WordTrace tailWord_900602 prefixEnd_900602 462441704400590624233213 := by
  unfold tailWord_900602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211913370820059855306015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21898435655520159614149373 8211913370820059855306015)
  ·
    refine ⟨12317870056230089782959023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211913370820059855306015 12317870056230089782959023)
    ·
      refine ⟨18476805084345134674438535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12317870056230089782959023 18476805084345134674438535)
      ·
        refine ⟨27715207626517702011657803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18476805084345134674438535 27715207626517702011657803)
        ·
          refine ⟨41572811439776553017486705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715207626517702011657803 41572811439776553017486705)
          ·
            refine ⟨31179608579832414763115029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41572811439776553017486705 31179608579832414763115029)
            ·
              refine ⟨1461544152179644442021017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31179608579832414763115029 1461544152179644442021017)
              ·
                refine ⟨1096158114134733331515763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461544152179644442021017 1096158114134733331515763)
                ·
                  refine ⟨1644237171202099997273645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096158114134733331515763 1644237171202099997273645)
                  ·
                    refine ⟨616588939200787498977617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644237171202099997273645 616588939200787498977617)
                    ·
                      refine ⟨462441704400590624233213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616588939200787498977617 462441704400590624233213)
                      ·
                        rfl

theorem cell23_900602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_900602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900602 prefixEnd_900602 := by exact prefixLift 900602
  have htrace : WordTrace (prefixWord ++ tailWord_900602) baseStart_900602 baseEnd_900602 := by
    simpa [prefixWord, tailWord_900602, baseEnd_900602] using wordTrace_append hprefix tailTrace_900602
  have hstable : (prefixWord ++ tailWord_900602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900602).length < 2 ^ (prefixWord ++ tailWord_900602).sum := by decide
  have hdescent : baseEnd_900602 < baseStart_900602 := by decide
  rcases family_descends (prefixWord ++ tailWord_900602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900618 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_900618 : Nat := 118140960795 + 900618 * 2 ^ 59
def prefixEnd_900618 : Nat := 4983230072969 + 3 ^ 40 * 900618 * 2
def baseEnd_900618 : Nat := 462449920091062561633139

theorem tailTrace_900618 : CollatzResearch.WordTrace tailWord_900618 prefixEnd_900618 462449920091062561633139 := by
  unfold tailWord_900618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212059262805568538451627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21898824700814849435871005 8212059262805568538451627)
  ·
    refine ⟨12318088894208352807677441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8212059262805568538451627 12318088894208352807677441)
    ·
      refine ⟨9238566670656264605758081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12318088894208352807677441 9238566670656264605758081)
      ·
        refine ⟨6928925002992198454318561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9238566670656264605758081 6928925002992198454318561)
        ·
          refine ⟨5196693752244148840738921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6928925002992198454318561 5196693752244148840738921)
          ·
            refine ⟨3897520314183111630554191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196693752244148840738921 3897520314183111630554191)
            ·
              refine ⟨5846280471274667445831287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897520314183111630554191 5846280471274667445831287)
              ·
                refine ⟨8769420706912001168746931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5846280471274667445831287 8769420706912001168746931)
                ·
                  refine ⟨13154131060368001753120397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8769420706912001168746931 13154131060368001753120397)
                  ·
                    refine ⟨4932799147638000657420149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13154131060368001753120397 4932799147638000657420149)
                    ·
                      refine ⟨462449920091062561633139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4932799147638000657420149 462449920091062561633139)
                      ·
                        rfl

theorem cell23_900618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_900618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900618 prefixEnd_900618 := by exact prefixLift 900618
  have htrace : WordTrace (prefixWord ++ tailWord_900618) baseStart_900618 baseEnd_900618 := by
    simpa [prefixWord, tailWord_900618, baseEnd_900618] using wordTrace_append hprefix tailTrace_900618
  have hstable : (prefixWord ++ tailWord_900618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900618).length < 2 ^ (prefixWord ++ tailWord_900618).sum := by decide
  have hdescent : baseEnd_900618 < baseStart_900618 := by decide
  rcases family_descends (prefixWord ++ tailWord_900618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900722 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_900722 : Nat := 118140960795 + 900722 * 2 ^ 59
def prefixEnd_900722 : Nat := 4983230072969 + 3 ^ 40 * 900722 * 2
def baseEnd_900722 : Nat := 462503322079130154732661

theorem tailTrace_900722 : CollatzResearch.WordTrace tailWord_900722 prefixEnd_900722 462503322079130154732661 := by
  unfold tailWord_900722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213007560711374978898105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21901353495230333277061613 8213007560711374978898105)
  ·
    refine ⟨6159755670533531234173579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8213007560711374978898105 6159755670533531234173579)
    ·
      refine ⟨9239633505800296851260369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159755670533531234173579 9239633505800296851260369)
      ·
        refine ⟨6929725129350222638445277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9239633505800296851260369 6929725129350222638445277)
        ·
          refine ⟨2598646923506333489416979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6929725129350222638445277 2598646923506333489416979)
          ·
            refine ⟨3897970385259500234125469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2598646923506333489416979 3897970385259500234125469)
            ·
              refine ⟨1461738894472312587797051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3897970385259500234125469 1461738894472312587797051)
              ·
                refine ⟨2192608341708468881695577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461738894472312587797051 2192608341708468881695577)
                ·
                  refine ⟨1644456256281351661271683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192608341708468881695577 1644456256281351661271683)
                  ·
                    refine ⟨2466684384422027491907525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644456256281351661271683 2466684384422027491907525)
                    ·
                      refine ⟨462503322079130154732661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2466684384422027491907525 462503322079130154732661)
                      ·
                        rfl

theorem cell23_900722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_900722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900722 prefixEnd_900722 := by exact prefixLift 900722
  have htrace : WordTrace (prefixWord ++ tailWord_900722) baseStart_900722 baseEnd_900722 := by
    simpa [prefixWord, tailWord_900722, baseEnd_900722] using wordTrace_append hprefix tailTrace_900722
  have hstable : (prefixWord ++ tailWord_900722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900722).length < 2 ^ (prefixWord ++ tailWord_900722).sum := by decide
  have hdescent : baseEnd_900722 < baseStart_900722 := by decide
  rcases family_descends (prefixWord ++ tailWord_900722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900745 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 6]
def baseStart_900745 : Nat := 118140960795 + 900745 * 2 ^ 59
def prefixEnd_900745 : Nat := 4983230072969 + 3 ^ 40 * 900745 * 2
def baseEnd_900745 : Nat := 51390570237131507193895

theorem tailTrace_900745 : CollatzResearch.WordTrace tailWord_900745 prefixEnd_900745 51390570237131507193895 := by
  unfold tailWord_900745
  simp only [CollatzResearch.WordTrace]
  refine ⟨32852869121762174843679689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21901912747841449895786459 32852869121762174843679689)
  ·
    refine ⟨24639651841321631132759767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32852869121762174843679689 24639651841321631132759767)
    ·
      refine ⟨36959477761982446699139651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24639651841321631132759767 36959477761982446699139651)
      ·
        refine ⟨55439216642973670048709477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36959477761982446699139651 55439216642973670048709477)
        ·
          refine ⟨10394853120557563134133027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55439216642973670048709477 10394853120557563134133027)
          ·
            refine ⟨15592279680836344701199541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394853120557563134133027 15592279680836344701199541)
            ·
              refine ⟨1461776220078407315737457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15592279680836344701199541 1461776220078407315737457)
              ·
                refine ⟨1096332165058805486803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461776220078407315737457 1096332165058805486803093)
                ·
                  refine ⟨51390570237131507193895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1096332165058805486803093 51390570237131507193895)
                  ·
                    rfl

theorem cell23_900745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_900745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900745 prefixEnd_900745 := by exact prefixLift 900745
  have htrace : WordTrace (prefixWord ++ tailWord_900745) baseStart_900745 baseEnd_900745 := by
    simpa [prefixWord, tailWord_900745, baseEnd_900745] using wordTrace_append hprefix tailTrace_900745
  have hstable : (prefixWord ++ tailWord_900745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900745).length < 2 ^ (prefixWord ++ tailWord_900745).sum := by decide
  have hdescent : baseEnd_900745 < baseStart_900745 := by decide
  rcases family_descends (prefixWord ++ tailWord_900745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900748 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_900748 : Nat := 118140960795 + 900748 * 2 ^ 59
def prefixEnd_900748 : Nat := 4983230072969 + 3 ^ 40 * 900748 * 2
def baseEnd_900748 : Nat := 462516672576147053007541

theorem tailTrace_900748 : CollatzResearch.WordTrace tailWord_900748 prefixEnd_900748 462516672576147053007541 := by
  unfold tailWord_900748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426489270375653178019449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21901985693834204237359265 16426489270375653178019449)
  ·
    refine ⟨12319866952781739883514587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16426489270375653178019449 12319866952781739883514587)
    ·
      refine ⟨18479800429172609825271881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12319866952781739883514587 18479800429172609825271881)
      ·
        refine ⟨13859850321879457368953911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18479800429172609825271881 13859850321879457368953911)
        ·
          refine ⟨20789775482819186053430867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13859850321879457368953911 20789775482819186053430867)
          ·
            refine ⟨31184663224228779080146301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20789775482819186053430867 31184663224228779080146301)
            ·
              refine ⟨11694248709085792155054863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31184663224228779080146301 11694248709085792155054863)
              ·
                refine ⟨17541373063628688232582295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11694248709085792155054863 17541373063628688232582295)
                ·
                  refine ⟨26312059595443032348873443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17541373063628688232582295 26312059595443032348873443)
                  ·
                    refine ⟨39468089393164548523310165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26312059595443032348873443 39468089393164548523310165)
                    ·
                      refine ⟨462516672576147053007541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39468089393164548523310165 462516672576147053007541)
                      ·
                        rfl

theorem cell23_900748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_900748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900748 prefixEnd_900748 := by exact prefixLift 900748
  have htrace : WordTrace (prefixWord ++ tailWord_900748) baseStart_900748 baseEnd_900748 := by
    simpa [prefixWord, tailWord_900748, baseEnd_900748] using wordTrace_append hprefix tailTrace_900748
  have hstable : (prefixWord ++ tailWord_900748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900748).length < 2 ^ (prefixWord ++ tailWord_900748).sum := by decide
  have hdescent : baseEnd_900748 < baseStart_900748 := by decide
  rcases family_descends (prefixWord ++ tailWord_900748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900825 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_900825 : Nat := 118140960795 + 900825 * 2 ^ 59
def prefixEnd_900825 : Nat := 4983230072969 + 3 ^ 40 * 900825 * 2
def baseEnd_900825 : Nat := 462556210586543251744687

theorem tailTrace_900825 : CollatzResearch.WordTrace tailWord_900825 prefixEnd_900825 462556210586543251744687 := by
  unfold tailWord_900825
  simp only [CollatzResearch.WordTrace]
  refine ⟨32855786961472348506591929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21903857974314899004394619 32855786961472348506591929)
  ·
    refine ⟨24641840221104261379943947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32855786961472348506591929 24641840221104261379943947)
    ·
      refine ⟨36962760331656392069915921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24641840221104261379943947 36962760331656392069915921)
      ·
        refine ⟨27722070248742294052436941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36962760331656392069915921 27722070248742294052436941)
        ·
          refine ⟨10395776343278360269663853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27722070248742294052436941 10395776343278360269663853)
          ·
            refine ⟨3898416128729385101123945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10395776343278360269663853 3898416128729385101123945)
            ·
              refine ⟨2923812096547038825842959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3898416128729385101123945 2923812096547038825842959)
              ·
                refine ⟨4385718144820558238764439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2923812096547038825842959 4385718144820558238764439)
                ·
                  refine ⟨6578577217230837358146659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4385718144820558238764439 6578577217230837358146659)
                  ·
                    refine ⟨9867865825846256037219989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6578577217230837358146659 9867865825846256037219989)
                    ·
                      refine ⟨462556210586543251744687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9867865825846256037219989 462556210586543251744687)
                      ·
                        rfl

theorem cell23_900825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_900825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900825 prefixEnd_900825 := by exact prefixLift 900825
  have htrace : WordTrace (prefixWord ++ tailWord_900825) baseStart_900825 baseEnd_900825 := by
    simpa [prefixWord, tailWord_900825, baseEnd_900825] using wordTrace_append hprefix tailTrace_900825
  have hstable : (prefixWord ++ tailWord_900825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900825).length < 2 ^ (prefixWord ++ tailWord_900825).sum := by decide
  have hdescent : baseEnd_900825 < baseStart_900825 := by decide
  rcases family_descends (prefixWord ++ tailWord_900825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900839 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 6]
def baseStart_900839 : Nat := 118140960795 + 900839 * 2 ^ 59
def prefixEnd_900839 : Nat := 4983230072969 + 3 ^ 40 * 900839 * 2
def baseEnd_900839 : Nat := 154187799771902065656541

theorem tailTrace_900839 : CollatzResearch.WordTrace tailWord_900839 prefixEnd_900839 154187799771902065656541 := by
  unfold tailWord_900839
  simp only [CollatzResearch.WordTrace]
  refine ⟨32856297583421628897601571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21904198388947752598401047 32856297583421628897601571)
  ·
    refine ⟨49284446375132443346402357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32856297583421628897601571 49284446375132443346402357)
    ·
      refine ⟨4620416847668666563725221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49284446375132443346402357 4620416847668666563725221)
      ·
        refine ⟨866328158937874980698479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4620416847668666563725221 866328158937874980698479)
        ·
          refine ⟨1299492238406812471047719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866328158937874980698479 1299492238406812471047719)
          ·
            refine ⟨1949238357610218706571579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299492238406812471047719 1949238357610218706571579)
            ·
              refine ⟨2923857536415328059857369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949238357610218706571579 2923857536415328059857369)
              ·
                refine ⟨2192893152311496044893027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923857536415328059857369 2192893152311496044893027)
                ·
                  refine ⟨3289339728467244067339541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2192893152311496044893027 3289339728467244067339541)
                  ·
                    refine ⟨154187799771902065656541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3289339728467244067339541 154187799771902065656541)
                    ·
                      rfl

theorem cell23_900839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_900839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900839 prefixEnd_900839 := by exact prefixLift 900839
  have htrace : WordTrace (prefixWord ++ tailWord_900839) baseStart_900839 baseEnd_900839 := by
    simpa [prefixWord, tailWord_900839, baseEnd_900839] using wordTrace_append hprefix tailTrace_900839
  have hstable : (prefixWord ++ tailWord_900839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900839).length < 2 ^ (prefixWord ++ tailWord_900839).sum := by decide
  have hdescent : baseEnd_900839 < baseStart_900839 := by decide
  rcases family_descends (prefixWord ++ tailWord_900839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900863 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 1, 2, 2]
def baseStart_900863 : Nat := 118140960795 + 900863 * 2 ^ 59
def prefixEnd_900863 : Nat := 4983230072969 + 3 ^ 40 * 900863 * 2
def baseEnd_900863 : Nat := 462575722851414103069513

theorem tailTrace_900863 : CollatzResearch.WordTrace tailWord_900863 prefixEnd_900863 462575722851414103069513 := by
  unfold tailWord_900863
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857172935334680996475243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21904781956889787330983495 32857172935334680996475243)
  ·
    refine ⟨49285759403002021494712865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32857172935334680996475243 49285759403002021494712865)
    ·
      refine ⟨36964319552251516121034649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49285759403002021494712865 36964319552251516121034649)
      ·
        refine ⟨27723239664188637090775987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36964319552251516121034649 27723239664188637090775987)
        ·
          refine ⟨41584859496282955636163981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27723239664188637090775987 41584859496282955636163981)
          ·
            refine ⟨15594322311106108363561493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41584859496282955636163981 15594322311106108363561493)
            ·
              refine ⟨730983858333098829541945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15594322311106108363561493 730983858333098829541945)
              ·
                refine ⟨548237893749824122156459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730983858333098829541945 548237893749824122156459)
                ·
                  refine ⟨822356840624736183234689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548237893749824122156459 822356840624736183234689)
                  ·
                    refine ⟨616767630468552137426017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 822356840624736183234689 616767630468552137426017)
                    ·
                      refine ⟨462575722851414103069513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616767630468552137426017 462575722851414103069513)
                      ·
                        rfl

theorem cell23_900863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_900863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900863 prefixEnd_900863 := by exact prefixLift 900863
  have htrace : WordTrace (prefixWord ++ tailWord_900863) baseStart_900863 baseEnd_900863 := by
    simpa [prefixWord, tailWord_900863, baseEnd_900863] using wordTrace_append hprefix tailTrace_900863
  have hstable : (prefixWord ++ tailWord_900863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900863).length < 2 ^ (prefixWord ++ tailWord_900863).sum := by decide
  have hdescent : baseEnd_900863 < baseStart_900863 := by decide
  rcases family_descends (prefixWord ++ tailWord_900863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900865 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_900865 : Nat := 118140960795 + 900865 * 2 ^ 59
def prefixEnd_900865 : Nat := 4983230072969 + 3 ^ 40 * 900865 * 2
def baseEnd_900865 : Nat := 154192249937574365081501

theorem tailTrace_900865 : CollatzResearch.WordTrace tailWord_900865 prefixEnd_900865 154192249937574365081501 := by
  unfold tailWord_900865
  simp only [CollatzResearch.WordTrace]
  refine ⟨32857245881327435338048049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21904830587551623558698699 32857245881327435338048049)
  ·
    refine ⟨24642934410995576503536037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32857245881327435338048049 24642934410995576503536037)
    ·
      refine ⟨4620550202061670594413007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24642934410995576503536037 4620550202061670594413007)
      ·
        refine ⟨6930825303092505891619511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620550202061670594413007 6930825303092505891619511)
        ·
          refine ⟨10396237954638758837429267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930825303092505891619511 10396237954638758837429267)
          ·
            refine ⟨15594356931958138256143901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10396237954638758837429267 15594356931958138256143901)
            ·
              refine ⟨5847883849484301846053963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15594356931958138256143901 5847883849484301846053963)
              ·
                refine ⟨8771825774226452769080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5847883849484301846053963 8771825774226452769080945)
                ·
                  refine ⟨6578869330669839576810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8771825774226452769080945 6578869330669839576810709)
                  ·
                    refine ⟨154192249937574365081501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6578869330669839576810709 154192249937574365081501)
                    ·
                      rfl

theorem cell23_900865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_900865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900865 prefixEnd_900865 := by exact prefixLift 900865
  have htrace : WordTrace (prefixWord ++ tailWord_900865) baseStart_900865 baseEnd_900865 := by
    simpa [prefixWord, tailWord_900865, baseEnd_900865] using wordTrace_append hprefix tailTrace_900865
  have hstable : (prefixWord ++ tailWord_900865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900865).length < 2 ^ (prefixWord ++ tailWord_900865).sum := by decide
  have hdescent : baseEnd_900865 < baseStart_900865 := by decide
  rcases family_descends (prefixWord ++ tailWord_900865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900895 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 8]
def baseStart_900895 : Nat := 118140960795 + 900895 * 2 ^ 59
def prefixEnd_900895 : Nat := 4983230072969 + 3 ^ 40 * 900895 * 2
def baseEnd_900895 : Nat := 154197384744119325956455

theorem tailTrace_900895 : CollatzResearch.WordTrace tailWord_900895 prefixEnd_900895 154197384744119325956455 := by
  unfold tailWord_900895
  simp only [CollatzResearch.WordTrace]
  refine ⟨32858340071218750461640139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21905560047479166974426759 32858340071218750461640139)
  ·
    refine ⟨49287510106828125692460209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32858340071218750461640139 49287510106828125692460209)
    ·
      refine ⟨36965632580121094269345157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49287510106828125692460209 36965632580121094269345157)
      ·
        refine ⟨6931056108772705175502217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36965632580121094269345157 6931056108772705175502217)
        ·
          refine ⟨5198292081579528881626663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931056108772705175502217 5198292081579528881626663)
          ·
            refine ⟨7797438122369293322439995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198292081579528881626663 7797438122369293322439995)
            ·
              refine ⟨11696157183553939983659993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7797438122369293322439995 11696157183553939983659993)
              ·
                refine ⟨8772117887665454987744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11696157183553939983659993 8772117887665454987744995)
                ·
                  refine ⟨13158176831498182481617493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8772117887665454987744995 13158176831498182481617493)
                  ·
                    refine ⟨154197384744119325956455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13158176831498182481617493 154197384744119325956455)
                    ·
                      rfl

theorem cell23_900895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_900895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900895 prefixEnd_900895 := by exact prefixLift 900895
  have htrace : WordTrace (prefixWord ++ tailWord_900895) baseStart_900895 baseEnd_900895 := by
    simpa [prefixWord, tailWord_900895, baseEnd_900895] using wordTrace_append hprefix tailTrace_900895
  have hstable : (prefixWord ++ tailWord_900895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900895).length < 2 ^ (prefixWord ++ tailWord_900895).sum := by decide
  have hdescent : baseEnd_900895 < baseStart_900895 := by decide
  rcases family_descends (prefixWord ++ tailWord_900895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900936 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_900936 : Nat := 118140960795 + 900936 * 2 ^ 59
def prefixEnd_900936 : Nat := 4983230072969 + 3 ^ 40 * 900936 * 2
def baseEnd_900936 : Nat := 462613206939192317456677

theorem tailTrace_900936 : CollatzResearch.WordTrace tailWord_900936 prefixEnd_900936 462613206939192317456677 := by
  unfold tailWord_900936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16429917732035107231941331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21906556976046809642588441 16429917732035107231941331)
  ·
    refine ⟨24644876598052660847911997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16429917732035107231941331 24644876598052660847911997)
    ·
      refine ⟨9241828724269747817966999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24644876598052660847911997 9241828724269747817966999)
      ·
        refine ⟨13862743086404621726950499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241828724269747817966999 13862743086404621726950499)
        ·
          refine ⟨20794114629606932590425749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13862743086404621726950499 20794114629606932590425749)
          ·
            refine ⟨974724123262824965176207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20794114629606932590425749 974724123262824965176207)
            ·
              refine ⟨1462086184894237447764311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974724123262824965176207 1462086184894237447764311)
              ·
                refine ⟨2193129277341356171646467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462086184894237447764311 2193129277341356171646467)
                ·
                  refine ⟨3289693916012034257469701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193129277341356171646467 3289693916012034257469701)
                  ·
                    refine ⟨616817609252256423275569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3289693916012034257469701 616817609252256423275569)
                    ·
                      refine ⟨462613206939192317456677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 616817609252256423275569 462613206939192317456677)
                      ·
                        rfl

theorem cell23_900936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_900936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900936 prefixEnd_900936 := by exact prefixLift 900936
  have htrace : WordTrace (prefixWord ++ tailWord_900936) baseStart_900936 baseEnd_900936 := by
    simpa [prefixWord, tailWord_900936, baseEnd_900936] using wordTrace_append hprefix tailTrace_900936
  have hstable : (prefixWord ++ tailWord_900936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900936).length < 2 ^ (prefixWord ++ tailWord_900936).sum := by decide
  have hdescent : baseEnd_900936 < baseStart_900936 := by decide
  rcases family_descends (prefixWord ++ tailWord_900936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900959 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 5]
def baseStart_900959 : Nat := 118140960795 + 900959 * 2 ^ 59
def prefixEnd_900959 : Nat := 4983230072969 + 3 ^ 40 * 900959 * 2
def baseEnd_900959 : Nat := 51402779666027303052119

theorem tailTrace_900959 : CollatzResearch.WordTrace tailWord_900959 prefixEnd_900959 51402779666027303052119 := by
  unfold tailWord_900959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32860674342986889391969931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21907116228657926261313287 32860674342986889391969931)
  ·
    refine ⟨49291011514480334087954897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32860674342986889391969931 49291011514480334087954897)
    ·
      refine ⟨36968258635860250565966173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49291011514480334087954897 36968258635860250565966173)
      ·
        refine ⟨13863096988447593962237315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36968258635860250565966173 13863096988447593962237315)
        ·
          refine ⟨20794645482671390943355973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13863096988447593962237315 20794645482671390943355973)
          ·
            refine ⟨3898996028000885801879245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20794645482671390943355973 3898996028000885801879245)
            ·
              refine ⟨1462123510500332175704717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3898996028000885801879245 1462123510500332175704717)
              ·
                refine ⟨548296316437624565889269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462123510500332175704717 548296316437624565889269)
                ·
                  refine ⟨51402779666027303052119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548296316437624565889269 51402779666027303052119)
                  ·
                    rfl

theorem cell23_900959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 5].length) (baseStart_900959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900959 prefixEnd_900959 := by exact prefixLift 900959
  have htrace : WordTrace (prefixWord ++ tailWord_900959) baseStart_900959 baseEnd_900959 := by
    simpa [prefixWord, tailWord_900959, baseEnd_900959] using wordTrace_append hprefix tailTrace_900959
  have hstable : (prefixWord ++ tailWord_900959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900959).length < 2 ^ (prefixWord ++ tailWord_900959).sum := by decide
  have hdescent : baseEnd_900959 < baseStart_900959 := by decide
  rcases family_descends (prefixWord ++ tailWord_900959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900972 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_900972 : Nat := 118140960795 + 900972 * 2 ^ 59
def prefixEnd_900972 : Nat := 4983230072969 + 3 ^ 40 * 900972 * 2
def baseEnd_900972 : Nat := 154210564080918058868837

theorem tailTrace_900972 : CollatzResearch.WordTrace tailWord_900972 prefixEnd_900972 154210564080918058868837 := by
  unfold tailWord_900972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430574245969896306096585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21907432327959861741462113 16430574245969896306096585)
  ·
    refine ⟨12322930684477422229572439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16430574245969896306096585 12322930684477422229572439)
    ·
      refine ⟨18484396026716133344358659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12322930684477422229572439 18484396026716133344358659)
      ·
        refine ⟨27726594040074200016537989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18484396026716133344358659 27726594040074200016537989)
        ·
          refine ⟨5198736382513912503100873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27726594040074200016537989 5198736382513912503100873)
          ·
            refine ⟨3899052286885434377325655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5198736382513912503100873 3899052286885434377325655)
            ·
              refine ⟨5848578430328151565988483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899052286885434377325655 5848578430328151565988483)
              ·
                refine ⟨8772867645492227348982725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5848578430328151565988483 8772867645492227348982725)
                ·
                  refine ⟨1644912683529792627934261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8772867645492227348982725 1644912683529792627934261)
                  ·
                    refine ⟨154210564080918058868837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1644912683529792627934261 154210564080918058868837)
                    ·
                      rfl

theorem cell23_900972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_900972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900972 prefixEnd_900972 := by exact prefixLift 900972
  have htrace : WordTrace (prefixWord ++ tailWord_900972) baseStart_900972 baseEnd_900972 := by
    simpa [prefixWord, tailWord_900972, baseEnd_900972] using wordTrace_append hprefix tailTrace_900972
  have hstable : (prefixWord ++ tailWord_900972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900972).length < 2 ^ (prefixWord ++ tailWord_900972).sum := by decide
  have hdescent : baseEnd_900972 < baseStart_900972 := by decide
  rcases family_descends (prefixWord ++ tailWord_900972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900975 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_900975 : Nat := 118140960795 + 900975 * 2 ^ 59
def prefixEnd_900975 : Nat := 4983230072969 + 3 ^ 40 * 900975 * 2
def baseEnd_900975 : Nat := 462633232684717664868997

theorem tailTrace_900975 : CollatzResearch.WordTrace tailWord_900975 prefixEnd_900975 462633232684717664868997 := by
  unfold tailWord_900975
  simp only [CollatzResearch.WordTrace]
  refine ⟨32861257910928924124552379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21907505273952616083034919 32861257910928924124552379)
  ·
    refine ⟨49291886866393386186828569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32861257910928924124552379 49291886866393386186828569)
    ·
      refine ⟨36968915149795039640121427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49291886866393386186828569 36968915149795039640121427)
      ·
        refine ⟨55453372724692559460182141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36968915149795039640121427 55453372724692559460182141)
        ·
          refine ⟨20795014771759709797568303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55453372724692559460182141 20795014771759709797568303)
          ·
            refine ⟨31192522157639564696352455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20795014771759709797568303 31192522157639564696352455)
            ·
              refine ⟨46788783236459347044528683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31192522157639564696352455 46788783236459347044528683)
              ·
                refine ⟨70183174854689020566793025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46788783236459347044528683 70183174854689020566793025)
                ·
                  refine ⟨52637381141016765425094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70183174854689020566793025 52637381141016765425094769)
                  ·
                    refine ⟨39478035855762574068821077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52637381141016765425094769 39478035855762574068821077)
                    ·
                      refine ⟨462633232684717664868997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39478035855762574068821077 462633232684717664868997)
                      ·
                        rfl

theorem cell23_900975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_900975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900975 prefixEnd_900975 := by exact prefixLift 900975
  have htrace : WordTrace (prefixWord ++ tailWord_900975) baseStart_900975 baseEnd_900975 := by
    simpa [prefixWord, tailWord_900975, baseEnd_900975] using wordTrace_append hprefix tailTrace_900975
  have hstable : (prefixWord ++ tailWord_900975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900975).length < 2 ^ (prefixWord ++ tailWord_900975).sum := by decide
  have hdescent : baseEnd_900975 < baseStart_900975 := by decide
  rcases family_descends (prefixWord ++ tailWord_900975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900992 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_900992 : Nat := 118140960795 + 900992 * 2 ^ 59
def prefixEnd_900992 : Nat := 4983230072969 + 3 ^ 40 * 900992 * 2
def baseEnd_900992 : Nat := 462641961855844098356419

theorem tailTrace_900992 : CollatzResearch.WordTrace tailWord_900992 prefixEnd_900992 462641961855844098356419 := by
  unfold tailWord_900992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16430938975933668013960615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21907918634578224018614153 16430938975933668013960615)
  ·
    refine ⟨24646408463900502020940923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16430938975933668013960615 24646408463900502020940923)
    ·
      refine ⟨36969612695850753031411385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24646408463900502020940923 36969612695850753031411385)
      ·
        refine ⟨27727209521888064773558539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36969612695850753031411385 27727209521888064773558539)
        ·
          refine ⟨41590814282832097160337809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27727209521888064773558539 41590814282832097160337809)
          ·
            refine ⟨31193110712124072870253357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41590814282832097160337809 31193110712124072870253357)
            ·
              refine ⟨11697416517046527326345009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31193110712124072870253357 11697416517046527326345009)
              ·
                refine ⟨8773062387784895494758757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11697416517046527326345009 8773062387784895494758757)
                ·
                  refine ⟨1644949197709667905267267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8773062387784895494758757 1644949197709667905267267)
                  ·
                    refine ⟨2467423796564501857900901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644949197709667905267267 2467423796564501857900901)
                    ·
                      refine ⟨462641961855844098356419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2467423796564501857900901 462641961855844098356419)
                      ·
                        rfl

theorem cell23_900992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_900992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_900992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_900992 prefixEnd_900992 := by exact prefixLift 900992
  have htrace : WordTrace (prefixWord ++ tailWord_900992) baseStart_900992 baseEnd_900992 := by
    simpa [prefixWord, tailWord_900992, baseEnd_900992] using wordTrace_append hprefix tailTrace_900992
  have hstable : (prefixWord ++ tailWord_900992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900992).length < 2 ^ (prefixWord ++ tailWord_900992).sum := by decide
  have hdescent : baseEnd_900992 < baseStart_900992 := by decide
  rcases family_descends (prefixWord ++ tailWord_900992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901076 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_901076 : Nat := 118140960795 + 901076 * 2 ^ 59
def prefixEnd_901076 : Nat := 4983230072969 + 3 ^ 40 * 901076 * 2
def baseEnd_901076 : Nat := 462685094230821769706033

theorem tailTrace_901076 : CollatzResearch.WordTrace tailWord_901076 prefixEnd_901076 462685094230821769706033 := by
  unfold tailWord_901076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16432470841781509186989541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21909961122375345582652721 16432470841781509186989541)
  ·
    refine ⟨3081088282834032972560539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16432470841781509186989541 3081088282834032972560539)
    ·
      refine ⟨4621632424251049458840809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081088282834032972560539 4621632424251049458840809)
      ·
        refine ⟨3466224318188287094130607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4621632424251049458840809 3466224318188287094130607)
        ·
          refine ⟨5199336477282430641195911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466224318188287094130607 5199336477282430641195911)
          ·
            refine ⟨7799004715923645961793867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199336477282430641195911 7799004715923645961793867)
            ·
              refine ⟨11698507073885468942690801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7799004715923645961793867 11698507073885468942690801)
              ·
                refine ⟨8773880305414101707018101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11698507073885468942690801 8773880305414101707018101)
                ·
                  refine ⟨822551278632572035032947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8773880305414101707018101 822551278632572035032947)
                  ·
                    refine ⟨1233826917948858052549421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822551278632572035032947 1233826917948858052549421)
                    ·
                      refine ⟨462685094230821769706033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1233826917948858052549421 462685094230821769706033)
                      ·
                        rfl

theorem cell23_901076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_901076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901076 prefixEnd_901076 := by exact prefixLift 901076
  have htrace : WordTrace (prefixWord ++ tailWord_901076) baseStart_901076 baseEnd_901076 := by
    simpa [prefixWord, tailWord_901076, baseEnd_901076] using wordTrace_append hprefix tailTrace_901076
  have hstable : (prefixWord ++ tailWord_901076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901076).length < 2 ^ (prefixWord ++ tailWord_901076).sum := by decide
  have hdescent : baseEnd_901076 < baseStart_901076 := by decide
  rcases family_descends (prefixWord ++ tailWord_901076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901079 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 1, 5]
def baseStart_901079 : Nat := 118140960795 + 901079 * 2 ^ 59
def prefixEnd_901079 : Nat := 4983230072969 + 3 ^ 40 * 901079 * 2
def baseEnd_901079 : Nat := 154228878224261752656173

theorem tailTrace_901079 : CollatzResearch.WordTrace tailWord_901079 prefixEnd_901079 154228878224261752656173 := by
  unfold tailWord_901079
  simp only [CollatzResearch.WordTrace]
  refine ⟨32865051102552149886338291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21910034068368099924225527 32865051102552149886338291)
  ·
    refine ⟨49297576653828224829507437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32865051102552149886338291 49297576653828224829507437)
    ·
      refine ⟨18486591245185584311065289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49297576653828224829507437 18486591245185584311065289)
      ·
        refine ⟨13864943433889188233298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18486591245185584311065289 13864943433889188233298967)
        ·
          refine ⟨20797415150833782349948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13864943433889188233298967 20797415150833782349948451)
          ·
            refine ⟨31196122726250673524922677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20797415150833782349948451 31196122726250673524922677)
            ·
              refine ⟨2924636505586000642961501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31196122726250673524922677 2924636505586000642961501)
              ·
                refine ⟨1096738689594750241110563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2924636505586000642961501 1096738689594750241110563)
                ·
                  refine ⟨1645108034392125361665845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096738689594750241110563 1645108034392125361665845)
                  ·
                    refine ⟨154228878224261752656173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1645108034392125361665845 154228878224261752656173)
                    ·
                      rfl

theorem cell23_901079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_901079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901079 prefixEnd_901079 := by exact prefixLift 901079
  have htrace : WordTrace (prefixWord ++ tailWord_901079) baseStart_901079 baseEnd_901079 := by
    simpa [prefixWord, tailWord_901079, baseEnd_901079] using wordTrace_append hprefix tailTrace_901079
  have hstable : (prefixWord ++ tailWord_901079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901079).length < 2 ^ (prefixWord ++ tailWord_901079).sum := by decide
  have hdescent : baseEnd_901079 < baseStart_901079 := by decide
  rcases family_descends (prefixWord ++ tailWord_901079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901116 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_901116 : Nat := 118140960795 + 901116 * 2 ^ 59
def prefixEnd_901116 : Nat := 4983230072969 + 3 ^ 40 * 901116 * 2
def baseEnd_901116 : Nat := 462705633457001613205849

theorem tailTrace_901116 : CollatzResearch.WordTrace tailWord_901116 prefixEnd_901116 462705633457001613205849 := by
  unfold tailWord_901116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433200301709052602717601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21910933735612070136956801 16433200301709052602717601)
  ·
    refine ⟨12324900226281789452038201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16433200301709052602717601 12324900226281789452038201)
    ·
      refine ⟨9243675169711342089028651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12324900226281789452038201 9243675169711342089028651)
      ·
        refine ⟨13865512754567013133542977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243675169711342089028651 13865512754567013133542977)
        ·
          refine ⟨10399134565925259850157233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13865512754567013133542977 10399134565925259850157233)
          ·
            refine ⟨7799350924443944887617925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10399134565925259850157233 7799350924443944887617925)
            ·
              refine ⟨1462378298333239666428361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7799350924443944887617925 1462378298333239666428361)
              ·
                refine ⟨1096783723749929749821271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462378298333239666428361 1096783723749929749821271)
                ·
                  refine ⟨1645175585624894624731907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096783723749929749821271 1645175585624894624731907)
                  ·
                    refine ⟨2467763378437341937097861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645175585624894624731907 2467763378437341937097861)
                    ·
                      refine ⟨462705633457001613205849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2467763378437341937097861 462705633457001613205849)
                      ·
                        rfl

theorem cell23_901116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_901116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901116 prefixEnd_901116 := by exact prefixLift 901116
  have htrace : WordTrace (prefixWord ++ tailWord_901116) baseStart_901116 baseEnd_901116 := by
    simpa [prefixWord, tailWord_901116, baseEnd_901116] using wordTrace_append hprefix tailTrace_901116
  have hstable : (prefixWord ++ tailWord_901116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901116).length < 2 ^ (prefixWord ++ tailWord_901116).sum := by decide
  have hdescent : baseEnd_901116 < baseStart_901116 := by decide
  rcases family_descends (prefixWord ++ tailWord_901116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901119 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_901119 : Nat := 118140960795 + 901119 * 2 ^ 59
def prefixEnd_901119 : Nat := 4983230072969 + 3 ^ 40 * 901119 * 2
def baseEnd_901119 : Nat := 462707173898965101468335

theorem tailTrace_901119 : CollatzResearch.WordTrace tailWord_901119 prefixEnd_901119 462707173898965101468335 := by
  unfold tailWord_901119
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866510022407236717794411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21911006681604824478529607 32866510022407236717794411)
  ·
    refine ⟨49299765033610855076691617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866510022407236717794411 49299765033610855076691617)
    ·
      refine ⟨36974823775208141307518713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49299765033610855076691617 36974823775208141307518713)
      ·
        refine ⟨27731117831406105980639035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36974823775208141307518713 27731117831406105980639035)
        ·
          refine ⟨41596676747109158970958553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27731117831406105980639035 41596676747109158970958553)
          ·
            refine ⟨31197507560331869228218915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41596676747109158970958553 31197507560331869228218915)
            ·
              refine ⟨46796261340497803842328373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31197507560331869228218915 46796261340497803842328373)
              ·
                refine ⟨4387149500671669110218285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46796261340497803842328373 4387149500671669110218285)
                ·
                  refine ⟨1645181062751875916331857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4387149500671669110218285 1645181062751875916331857)
                  ·
                    refine ⟨1233885797063906937248893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1645181062751875916331857 1233885797063906937248893)
                    ·
                      refine ⟨462707173898965101468335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1233885797063906937248893 462707173898965101468335)
                      ·
                        rfl

theorem cell23_901119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_901119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901119 prefixEnd_901119 := by exact prefixLift 901119
  have htrace : WordTrace (prefixWord ++ tailWord_901119) baseStart_901119 baseEnd_901119 := by
    simpa [prefixWord, tailWord_901119, baseEnd_901119] using wordTrace_append hprefix tailTrace_901119
  have hstable : (prefixWord ++ tailWord_901119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901119).length < 2 ^ (prefixWord ++ tailWord_901119).sum := by decide
  have hdescent : baseEnd_901119 < baseStart_901119 := by decide
  rcases family_descends (prefixWord ++ tailWord_901119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901156 : List Nat := [2, 3, 1, 4, 2, 1, 2, 8]
def baseStart_901156 : Nat := 118140960795 + 901156 * 2 ^ 59
def prefixEnd_901156 : Nat := 4983230072969 + 3 ^ 40 * 901156 * 2
def baseEnd_901156 : Nat := 17138006395673387285395

theorem tailTrace_901156 : CollatzResearch.WordTrace tailWord_901156 prefixEnd_901156 17138006395673387285395 := by
  unfold tailWord_901156
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433929761636596018445661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21911906348848794691260881 16433929761636596018445661)
  ·
    refine ⟨6162723660613723506917123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16433929761636596018445661 6162723660613723506917123)
    ·
      refine ⟨9244085490920585260375685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162723660613723506917123 9244085490920585260375685)
      ·
        refine ⟨1733266029547609736320441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9244085490920585260375685 1733266029547609736320441)
        ·
          refine ⟨1299949522160707302240331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733266029547609736320441 1299949522160707302240331)
          ·
            refine ⟨1949924283241060953360497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299949522160707302240331 1949924283241060953360497)
            ·
              refine ⟨1462443212430795715020373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949924283241060953360497 1462443212430795715020373)
              ·
                refine ⟨17138006395673387285395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1462443212430795715020373 17138006395673387285395)
                ·
                  rfl

theorem cell23_901156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 8].length) (baseStart_901156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901156 prefixEnd_901156 := by exact prefixLift 901156
  have htrace : WordTrace (prefixWord ++ tailWord_901156) baseStart_901156 baseEnd_901156 := by
    simpa [prefixWord, tailWord_901156, baseEnd_901156] using wordTrace_append hprefix tailTrace_901156
  have hstable : (prefixWord ++ tailWord_901156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901156).length < 2 ^ (prefixWord ++ tailWord_901156).sum := by decide
  have hdescent : baseEnd_901156 < baseStart_901156 := by decide
  rcases family_descends (prefixWord ++ tailWord_901156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901160 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_901160 : Nat := 118140960795 + 901160 * 2 ^ 59
def prefixEnd_901160 : Nat := 4983230072969 + 3 ^ 40 * 901160 * 2
def baseEnd_901160 : Nat := 154242742201933147018549

theorem tailTrace_901160 : CollatzResearch.WordTrace tailWord_901160 prefixEnd_901160 154242742201933147018549 := by
  unfold tailWord_901160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434002707629350360018467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21912003610172467146691289 16434002707629350360018467)
  ·
    refine ⟨24651004061444025540027701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16434002707629350360018467 24651004061444025540027701)
    ·
      refine ⟨2311031630760377394377597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24651004061444025540027701 2311031630760377394377597)
      ·
        refine ⟨866636861535141522891599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2311031630760377394377597 866636861535141522891599)
        ·
          refine ⟨1299955292302712284337399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866636861535141522891599 1299955292302712284337399)
          ·
            refine ⟨1949932938454068426506099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299955292302712284337399 1949932938454068426506099)
            ·
              refine ⟨2924899407681102639759149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949932938454068426506099 2924899407681102639759149)
              ·
                refine ⟨1096837277880413489909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2924899407681102639759149 1096837277880413489909681)
                ·
                  refine ⟨822627958410310117432261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1096837277880413489909681 822627958410310117432261)
                  ·
                    refine ⟨154242742201933147018549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 822627958410310117432261 154242742201933147018549)
                    ·
                      rfl

theorem cell23_901160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_901160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901160 prefixEnd_901160 := by exact prefixLift 901160
  have htrace : WordTrace (prefixWord ++ tailWord_901160) baseStart_901160 baseEnd_901160 := by
    simpa [prefixWord, tailWord_901160, baseEnd_901160] using wordTrace_append hprefix tailTrace_901160
  have hstable : (prefixWord ++ tailWord_901160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901160).length < 2 ^ (prefixWord ++ tailWord_901160).sum := by decide
  have hdescent : baseEnd_901160 < baseStart_901160 := by decide
  rcases family_descends (prefixWord ++ tailWord_901160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901209 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_901209 : Nat := 118140960795 + 901209 * 2 ^ 59
def prefixEnd_901209 : Nat := 4983230072969 + 3 ^ 40 * 901209 * 2
def baseEnd_901209 : Nat := 462753387157869749342921

theorem tailTrace_901209 : CollatzResearch.WordTrace tailWord_901209 prefixEnd_901209 462753387157869749342921 := by
  unfold tailWord_901209
  simp only [CollatzResearch.WordTrace]
  refine ⟨32869792592081182088570681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21913195061387454725713787 32869792592081182088570681)
  ·
    refine ⟨24652344444060886566428011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32869792592081182088570681 24652344444060886566428011)
    ·
      refine ⟨36978516666091329849642017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24652344444060886566428011 36978516666091329849642017)
      ·
        refine ⟨27733887499568497387231513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36978516666091329849642017 27733887499568497387231513)
        ·
          refine ⟨20800415624676373040423635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27733887499568497387231513 20800415624676373040423635)
          ·
            refine ⟨31200623437014559560635453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20800415624676373040423635 31200623437014559560635453)
            ·
              refine ⟨11700233788880459835238295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31200623437014559560635453 11700233788880459835238295)
              ·
                refine ⟨17550350683320689752857443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11700233788880459835238295 17550350683320689752857443)
                ·
                  refine ⟨26325526024981034629286165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17550350683320689752857443 26325526024981034629286165)
                  ·
                    refine ⟨1234009032420985998247789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26325526024981034629286165 1234009032420985998247789)
                    ·
                      refine ⟨462753387157869749342921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1234009032420985998247789 462753387157869749342921)
                      ·
                        rfl

theorem cell23_901209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_901209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901209 prefixEnd_901209 := by exact prefixLift 901209
  have htrace : WordTrace (prefixWord ++ tailWord_901209) baseStart_901209 baseEnd_901209 := by
    simpa [prefixWord, tailWord_901209, baseEnd_901209] using wordTrace_append hprefix tailTrace_901209
  have hstable : (prefixWord ++ tailWord_901209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901209).length < 2 ^ (prefixWord ++ tailWord_901209).sum := by decide
  have hdescent : baseEnd_901209 < baseStart_901209 := by decide
  rcases family_descends (prefixWord ++ tailWord_901209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901219 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_901219 : Nat := 118140960795 + 901219 * 2 ^ 59
def prefixEnd_901219 : Nat := 4983230072969 + 3 ^ 40 * 901219 * 2
def baseEnd_901219 : Nat := 462758521964414710217875

theorem tailTrace_901219 : CollatzResearch.WordTrace tailWord_901219 prefixEnd_901219 462758521964414710217875 := by
  unfold tailWord_901219
  simp only [CollatzResearch.WordTrace]
  refine ⟨32870157322044953796434711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21913438214696635864289807 32870157322044953796434711)
  ·
    refine ⟨49305235983067430694652067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32870157322044953796434711 49305235983067430694652067)
    ·
      refine ⟨73957853974601146041978101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49305235983067430694652067 73957853974601146041978101)
      ·
        refine ⟨6933548810118857441435447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73957853974601146041978101 6933548810118857441435447)
        ·
          refine ⟨10400323215178286162153171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933548810118857441435447 10400323215178286162153171)
          ·
            refine ⟨15600484822767429243229757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10400323215178286162153171 15600484822767429243229757)
            ·
              refine ⟨5850181808537785966211159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15600484822767429243229757 5850181808537785966211159)
              ·
                refine ⟨8775272712806678949316739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850181808537785966211159 8775272712806678949316739)
                ·
                  refine ⟨13162909069210018423975109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775272712806678949316739 13162909069210018423975109)
                  ·
                    refine ⟨2468045450476878454495333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13162909069210018423975109 2468045450476878454495333)
                    ·
                      refine ⟨462758521964414710217875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2468045450476878454495333 462758521964414710217875)
                      ·
                        rfl

theorem cell23_901219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_901219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901219 prefixEnd_901219 := by exact prefixLift 901219
  have htrace : WordTrace (prefixWord ++ tailWord_901219) baseStart_901219 baseEnd_901219 := by
    simpa [prefixWord, tailWord_901219, baseEnd_901219] using wordTrace_append hprefix tailTrace_901219
  have hstable : (prefixWord ++ tailWord_901219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901219).length < 2 ^ (prefixWord ++ tailWord_901219).sum := by decide
  have hdescent : baseEnd_901219 < baseStart_901219 := by decide
  rcases family_descends (prefixWord ++ tailWord_901219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901223 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_901223 : Nat := 118140960795 + 901223 * 2 ^ 59
def prefixEnd_901223 : Nat := 4983230072969 + 3 ^ 40 * 901223 * 2
def baseEnd_901223 : Nat := 462760575887032694567857

theorem tailTrace_901223 : CollatzResearch.WordTrace tailWord_901223 prefixEnd_901223 462760575887032694567857 := by
  unfold tailWord_901223
  simp only [CollatzResearch.WordTrace]
  refine ⟨32870303214030462479580323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21913535476020308319720215 32870303214030462479580323)
  ·
    refine ⟨49305454821045693719370485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32870303214030462479580323 49305454821045693719370485)
    ·
      refine ⟨4622386389473033786190983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49305454821045693719370485 4622386389473033786190983)
      ·
        refine ⟨6933579584209550679286475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4622386389473033786190983 6933579584209550679286475)
        ·
          refine ⟨10400369376314326018929713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6933579584209550679286475 10400369376314326018929713)
          ·
            refine ⟨7800277032235744514197285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400369376314326018929713 7800277032235744514197285)
            ·
              refine ⟨1462551943544202096411991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7800277032235744514197285 1462551943544202096411991)
              ·
                refine ⟨2193827915316303144617987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462551943544202096411991 2193827915316303144617987)
                ·
                  refine ⟨3290741872974454716926981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2193827915316303144617987 3290741872974454716926981)
                  ·
                    refine ⟨617014101182710259423809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3290741872974454716926981 617014101182710259423809)
                    ·
                      refine ⟨462760575887032694567857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617014101182710259423809 462760575887032694567857)
                      ·
                        rfl

theorem cell23_901223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_901223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901223 prefixEnd_901223 := by exact prefixLift 901223
  have htrace : WordTrace (prefixWord ++ tailWord_901223) baseStart_901223 baseEnd_901223 := by
    simpa [prefixWord, tailWord_901223, baseEnd_901223] using wordTrace_append hprefix tailTrace_901223
  have hstable : (prefixWord ++ tailWord_901223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901223).length < 2 ^ (prefixWord ++ tailWord_901223).sum := by decide
  have hdescent : baseEnd_901223 < baseStart_901223 := by decide
  rcases family_descends (prefixWord ++ tailWord_901223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901269 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_901269 : Nat := 118140960795 + 901269 * 2 ^ 59
def prefixEnd_901269 : Nat := 4983230072969 + 3 ^ 40 * 901269 * 2
def baseEnd_901269 : Nat := 462784195997139514592645

theorem tailTrace_901269 : CollatzResearch.WordTrace tailWord_901269 prefixEnd_901269 462784195997139514592645 := by
  unfold tailWord_901269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32871980971863812335754861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21914653981242541557169907 32871980971863812335754861)
  ·
    refine ⟨12326992864448929625908073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32871980971863812335754861 12326992864448929625908073)
    ·
      refine ⟨9245244648336697219431055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12326992864448929625908073 9245244648336697219431055)
      ·
        refine ⟨13867866972505045829146583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245244648336697219431055 13867866972505045829146583)
        ·
          refine ⟨20801800458757568743719875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13867866972505045829146583 20801800458757568743719875)
          ·
            refine ⟨31202700688136353115579813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801800458757568743719875 31202700688136353115579813)
            ·
              refine ⟨5850506379025566209171215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31202700688136353115579813 5850506379025566209171215)
              ·
                refine ⟨8775759568538349313756823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850506379025566209171215 8775759568538349313756823)
                ·
                  refine ⟨13163639352807523970635235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775759568538349313756823 13163639352807523970635235)
                  ·
                    refine ⟨19745459029211285955952853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13163639352807523970635235 19745459029211285955952853)
                    ·
                      refine ⟨462784195997139514592645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19745459029211285955952853 462784195997139514592645)
                      ·
                        rfl

theorem cell23_901269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_901269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901269 prefixEnd_901269 := by exact prefixLift 901269
  have htrace : WordTrace (prefixWord ++ tailWord_901269) baseStart_901269 baseEnd_901269 := by
    simpa [prefixWord, tailWord_901269, baseEnd_901269] using wordTrace_append hprefix tailTrace_901269
  have hstable : (prefixWord ++ tailWord_901269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901269).length < 2 ^ (prefixWord ++ tailWord_901269).sum := by decide
  have hdescent : baseEnd_901269 < baseStart_901269 := by decide
  rcases family_descends (prefixWord ++ tailWord_901269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901274 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_901274 : Nat := 118140960795 + 901274 * 2 ^ 59
def prefixEnd_901274 : Nat := 4983230072969 + 3 ^ 40 * 901274 * 2
def baseEnd_901274 : Nat := 462786763400411995030123

theorem tailTrace_901274 : CollatzResearch.WordTrace tailWord_901274 prefixEnd_901274 462786763400411995030123 := by
  unfold tailWord_901274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218040834211424547421719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21914775557897132126457917 8218040834211424547421719)
  ·
    refine ⟨12327061251317136821132579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218040834211424547421719 12327061251317136821132579)
    ·
      refine ⟨18490591876975705231698869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327061251317136821132579 18490591876975705231698869)
      ·
        refine ⟨1733492988466472365471769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18490591876975705231698869 1733492988466472365471769)
        ·
          refine ⟨1300119741349854274103827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733492988466472365471769 1300119741349854274103827)
          ·
            refine ⟨1950179612024781411155741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300119741349854274103827 1950179612024781411155741)
            ·
              refine ⟨731317354509293029183403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950179612024781411155741 731317354509293029183403)
              ·
                refine ⟨1096976031763939543775105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731317354509293029183403 1096976031763939543775105)
                ·
                  refine ⟨822732023822954657831329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1096976031763939543775105 822732023822954657831329)
                  ·
                    refine ⟨617049017867215993373497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 822732023822954657831329 617049017867215993373497)
                    ·
                      refine ⟨462786763400411995030123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617049017867215993373497 462786763400411995030123)
                      ·
                        rfl

theorem cell23_901274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_901274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901274 prefixEnd_901274 := by exact prefixLift 901274
  have htrace : WordTrace (prefixWord ++ tailWord_901274) baseStart_901274 baseEnd_901274 := by
    simpa [prefixWord, tailWord_901274, baseEnd_901274] using wordTrace_append hprefix tailTrace_901274
  have hstable : (prefixWord ++ tailWord_901274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901274).length < 2 ^ (prefixWord ++ tailWord_901274).sum := by decide
  have hdescent : baseEnd_901274 < baseStart_901274 := by decide
  rcases family_descends (prefixWord ++ tailWord_901274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901297 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 5]
def baseStart_901297 : Nat := 118140960795 + 901297 * 2 ^ 59
def prefixEnd_901297 : Nat := 4983230072969 + 3 ^ 40 * 901297 * 2
def baseEnd_901297 : Nat := 51422063717273933893613

theorem tailTrace_901297 : CollatzResearch.WordTrace tailWord_901297 prefixEnd_901297 51422063717273933893613 := by
  unfold tailWord_901297
  simp only [CollatzResearch.WordTrace]
  refine ⟨32873002215762373117774145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21915334810508248745182763 32873002215762373117774145)
  ·
    refine ⟨24654751661821779838330609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32873002215762373117774145 24654751661821779838330609)
    ·
      refine ⟨18491063746366334878747957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24654751661821779838330609 18491063746366334878747957)
      ·
        refine ⟨1733537226221843894882621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18491063746366334878747957 1733537226221843894882621)
        ·
          refine ⟨650076459833191460580983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1733537226221843894882621 650076459833191460580983)
          ·
            refine ⟨975114689749787190871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650076459833191460580983 975114689749787190871475)
            ·
              refine ⟨1462672034624680786307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975114689749787190871475 1462672034624680786307213)
              ·
                refine ⟨548502012984255294865205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462672034624680786307213 548502012984255294865205)
                ·
                  refine ⟨51422063717273933893613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548502012984255294865205 51422063717273933893613)
                  ·
                    rfl

theorem cell23_901297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 5].length) (baseStart_901297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901297 prefixEnd_901297 := by exact prefixLift 901297
  have htrace : WordTrace (prefixWord ++ tailWord_901297) baseStart_901297 baseEnd_901297 := by
    simpa [prefixWord, tailWord_901297, baseEnd_901297] using wordTrace_append hprefix tailTrace_901297
  have hstable : (prefixWord ++ tailWord_901297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901297).length < 2 ^ (prefixWord ++ tailWord_901297).sum := by decide
  have hdescent : baseEnd_901297 < baseStart_901297 := by decide
  rcases family_descends (prefixWord ++ tailWord_901297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901299 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_901299 : Nat := 118140960795 + 901299 * 2 ^ 59
def prefixEnd_901299 : Nat := 4983230072969 + 3 ^ 40 * 901299 * 2
def baseEnd_901299 : Nat := 462799600416774397217507

theorem tailTrace_901299 : CollatzResearch.WordTrace tailWord_901299 prefixEnd_901299 462799600416774397217507 := by
  unfold tailWord_901299
  simp only [CollatzResearch.WordTrace]
  refine ⟨32873075161755127459346951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21915383441170084972897967 32873075161755127459346951)
  ·
    refine ⟨49309612742632691189020427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32873075161755127459346951 49309612742632691189020427)
    ·
      refine ⟨73964419113949036783530641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49309612742632691189020427 73964419113949036783530641)
      ·
        refine ⟨55473314335461777587647981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73964419113949036783530641 55473314335461777587647981)
        ·
          refine ⟨20802492875798166595367993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55473314335461777587647981 20802492875798166595367993)
          ·
            refine ⟨15601869656848624946525995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20802492875798166595367993 15601869656848624946525995)
            ·
              refine ⟨23402804485272937419788993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15601869656848624946525995 23402804485272937419788993)
              ·
                refine ⟨17552103363954703064841745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23402804485272937419788993 17552103363954703064841745)
                ·
                  refine ⟨13164077522966027298631309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17552103363954703064841745 13164077522966027298631309)
                  ·
                    refine ⟨4936529071112260236986741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13164077522966027298631309 4936529071112260236986741)
                    ·
                      refine ⟨462799600416774397217507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4936529071112260236986741 462799600416774397217507)
                      ·
                        rfl

theorem cell23_901299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_901299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901299 prefixEnd_901299 := by exact prefixLift 901299
  have htrace : WordTrace (prefixWord ++ tailWord_901299) baseStart_901299 baseEnd_901299 := by
    simpa [prefixWord, tailWord_901299, baseEnd_901299] using wordTrace_append hprefix tailTrace_901299
  have hstable : (prefixWord ++ tailWord_901299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901299).length < 2 ^ (prefixWord ++ tailWord_901299).sum := by decide
  have hdescent : baseEnd_901299 < baseStart_901299 := by decide
  rcases family_descends (prefixWord ++ tailWord_901299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901306 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_901306 : Nat := 118140960795 + 901306 * 2 ^ 59
def prefixEnd_901306 : Nat := 4983230072969 + 3 ^ 40 * 901306 * 2
def baseEnd_901306 : Nat := 154267731593785289943325

theorem tailTrace_901306 : CollatzResearch.WordTrace tailWord_901306 prefixEnd_901306 154267731593785289943325 := by
  unfold tailWord_901306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218332618182441913712943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21915553648486511769901181 8218332618182441913712943)
  ·
    refine ⟨12327498927273662870569415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8218332618182441913712943 12327498927273662870569415)
    ·
      refine ⟨18491248390910494305854123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12327498927273662870569415 18491248390910494305854123)
      ·
        refine ⟨27736872586365741458781185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18491248390910494305854123 27736872586365741458781185)
        ·
          refine ⟨20802654439774306094085889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27736872586365741458781185 20802654439774306094085889)
          ·
            refine ⟨15601990829830729570564417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20802654439774306094085889 15601990829830729570564417)
            ·
              refine ⟨11701493122373047177923313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15601990829830729570564417 11701493122373047177923313)
              ·
                refine ⟨8776119841779785383442485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11701493122373047177923313 8776119841779785383442485)
                ·
                  refine ⟨822761235166854879697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8776119841779785383442485 822761235166854879697733)
                  ·
                    refine ⟨154267731593785289943325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 822761235166854879697733 154267731593785289943325)
                    ·
                      rfl

theorem cell23_901306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_901306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901306 prefixEnd_901306 := by exact prefixLift 901306
  have htrace : WordTrace (prefixWord ++ tailWord_901306) baseStart_901306 baseEnd_901306 := by
    simpa [prefixWord, tailWord_901306, baseEnd_901306] using wordTrace_append hprefix tailTrace_901306
  have hstable : (prefixWord ++ tailWord_901306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901306).length < 2 ^ (prefixWord ++ tailWord_901306).sum := by decide
  have hdescent : baseEnd_901306 < baseStart_901306 := by decide
  rcases family_descends (prefixWord ++ tailWord_901306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901314 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_901314 : Nat := 118140960795 + 901314 * 2 ^ 59
def prefixEnd_901314 : Nat := 4983230072969 + 3 ^ 40 * 901314 * 2
def baseEnd_901314 : Nat := 51423033625176870947771

theorem tailTrace_901314 : CollatzResearch.WordTrace tailWord_901314 prefixEnd_901314 51423033625176870947771 := by
  unfold tailWord_901314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218405564175196255285749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21915748171133856680761997 8218405564175196255285749)
  ·
    refine ⟨770475521641424648933039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8218405564175196255285749 770475521641424648933039)
    ·
      refine ⟨1155713282462136973399559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770475521641424648933039 1155713282462136973399559)
      ·
        refine ⟨1733569923693205460099339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155713282462136973399559 1733569923693205460099339)
        ·
          refine ⟨2600354885539808190149009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733569923693205460099339 2600354885539808190149009)
          ·
            refine ⟨1950266164154856142611757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600354885539808190149009 1950266164154856142611757)
            ·
              refine ⟨731349811558071053479409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950266164154856142611757 731349811558071053479409)
              ·
                refine ⟨548512358668553290109557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731349811558071053479409 548512358668553290109557)
                ·
                  refine ⟨51423033625176870947771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548512358668553290109557 51423033625176870947771)
                  ·
                    rfl

theorem cell23_901314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_901314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901314 prefixEnd_901314 := by exact prefixLift 901314
  have htrace : WordTrace (prefixWord ++ tailWord_901314) baseStart_901314 baseEnd_901314 := by
    simpa [prefixWord, tailWord_901314, baseEnd_901314] using wordTrace_append hprefix tailTrace_901314
  have hstable : (prefixWord ++ tailWord_901314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901314).length < 2 ^ (prefixWord ++ tailWord_901314).sum := by decide
  have hdescent : baseEnd_901314 < baseStart_901314 := by decide
  rcases family_descends (prefixWord ++ tailWord_901314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_901339 : Nat := 118140960795 + 901339 * 2 ^ 59
def prefixEnd_901339 : Nat := 4983230072969 + 3 ^ 40 * 901339 * 2
def baseEnd_901339 : Nat := 462820139642954240717323

theorem tailTrace_901339 : CollatzResearch.WordTrace tailWord_901339 prefixEnd_901339 462820139642954240717323 := by
  unfold tailWord_901339
  simp only [CollatzResearch.WordTrace]
  refine ⟨32874534081610214290803071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21916356054406809527202047 32874534081610214290803071)
  ·
    refine ⟨49311801122415321436204607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32874534081610214290803071 49311801122415321436204607)
    ·
      refine ⟨73967701683622982154306911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49311801122415321436204607 73967701683622982154306911)
      ·
        refine ⟨110951552525434473231460367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73967701683622982154306911 110951552525434473231460367)
        ·
          refine ⟨166427328788151709847190551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110951552525434473231460367 166427328788151709847190551)
          ·
            refine ⟨249640993182227564770785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166427328788151709847190551 249640993182227564770785827)
            ·
              refine ⟨374461489773341347156178741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249640993182227564770785827 374461489773341347156178741)
              ·
                refine ⟨35105764666250751295891757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374461489773341347156178741 35105764666250751295891757)
                ·
                  refine ⟨13164661749844031735959409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35105764666250751295891757 13164661749844031735959409)
                  ·
                    refine ⟨9873496312383023801969557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13164661749844031735959409 9873496312383023801969557)
                    ·
                      refine ⟨462820139642954240717323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9873496312383023801969557 462820139642954240717323)
                      ·
                        rfl

theorem cell23_901339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_901339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901339 prefixEnd_901339 := by exact prefixLift 901339
  have htrace : WordTrace (prefixWord ++ tailWord_901339) baseStart_901339 baseEnd_901339 := by
    simpa [prefixWord, tailWord_901339, baseEnd_901339] using wordTrace_append hprefix tailTrace_901339
  have hstable : (prefixWord ++ tailWord_901339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901339).length < 2 ^ (prefixWord ++ tailWord_901339).sum := by decide
  have hdescent : baseEnd_901339 < baseStart_901339 := by decide
  rcases family_descends (prefixWord ++ tailWord_901339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901407 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 2, 3, 2]
def baseStart_901407 : Nat := 118140960795 + 901407 * 2 ^ 59
def prefixEnd_901407 : Nat := 4983230072969 + 3 ^ 40 * 901407 * 2
def baseEnd_901407 : Nat := 462855056327459974667011

theorem tailTrace_901407 : CollatzResearch.WordTrace tailWord_901407 prefixEnd_901407 462855056327459974667011 := by
  unfold tailWord_901407
  simp only [CollatzResearch.WordTrace]
  refine ⟨32877014245363861904278475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21918009496909241269518983 32877014245363861904278475)
  ·
    refine ⟨49315521368045792856417713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32877014245363861904278475 49315521368045792856417713)
    ·
      refine ⟨36986641026034344642313285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49315521368045792856417713 36986641026034344642313285)
      ·
        refine ⟨6934995192381439620433741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36986641026034344642313285 6934995192381439620433741)
        ·
          refine ⟨2600623197143039857662653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6934995192381439620433741 2600623197143039857662653)
          ·
            refine ⟨975233698928639946623495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2600623197143039857662653 975233698928639946623495)
            ·
              refine ⟨1462850548392959919935243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975233698928639946623495 1462850548392959919935243)
              ·
                refine ⟨2194275822589439879902865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462850548392959919935243 2194275822589439879902865)
                ·
                  refine ⟨1645706866942079909927149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194275822589439879902865 1645706866942079909927149)
                  ·
                    refine ⟨617140075103279966222681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645706866942079909927149 617140075103279966222681)
                    ·
                      refine ⟨462855056327459974667011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617140075103279966222681 462855056327459974667011)
                      ·
                        rfl

theorem cell23_901407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_901407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901407 prefixEnd_901407 := by exact prefixLift 901407
  have htrace : WordTrace (prefixWord ++ tailWord_901407) baseStart_901407 baseEnd_901407 := by
    simpa [prefixWord, tailWord_901407, baseEnd_901407] using wordTrace_append hprefix tailTrace_901407
  have hstable : (prefixWord ++ tailWord_901407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901407).length < 2 ^ (prefixWord ++ tailWord_901407).sum := by decide
  have hdescent : baseEnd_901407 < baseStart_901407 := by decide
  rcases family_descends (prefixWord ++ tailWord_901407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901420 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_901420 : Nat := 118140960795 + 901420 * 2 ^ 59
def prefixEnd_901420 : Nat := 4983230072969 + 3 ^ 40 * 901420 * 2
def baseEnd_901420 : Nat := 462861731575968423804451

theorem tailTrace_901420 : CollatzResearch.WordTrace tailWord_901420 prefixEnd_901420 462861731575968423804451 := by
  unfold tailWord_901420
  simp only [CollatzResearch.WordTrace]
  refine ⟨16438744197158382562250857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21918325596211176749667809 16438744197158382562250857)
  ·
    refine ⟨12329058147868786921688143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16438744197158382562250857 12329058147868786921688143)
    ·
      refine ⟨18493587221803180382532215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12329058147868786921688143 18493587221803180382532215)
      ·
        refine ⟨27740380832704770573798323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18493587221803180382532215 27740380832704770573798323)
        ·
          refine ⟨41610571249057155860697485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27740380832704770573798323 41610571249057155860697485)
          ·
            refine ⟨15603964218396433447761557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41610571249057155860697485 15603964218396433447761557)
            ·
              refine ⟨731435822737332817863823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15603964218396433447761557 731435822737332817863823)
              ·
                refine ⟨1097153734105999226795735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731435822737332817863823 1097153734105999226795735)
                ·
                  refine ⟨1645730601158998840193603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097153734105999226795735 1645730601158998840193603)
                  ·
                    refine ⟨2468595901738498260290405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645730601158998840193603 2468595901738498260290405)
                    ·
                      refine ⟨462861731575968423804451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2468595901738498260290405 462861731575968423804451)
                      ·
                        rfl

theorem cell23_901420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_901420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901420 prefixEnd_901420 := by exact prefixLift 901420
  have htrace : WordTrace (prefixWord ++ tailWord_901420) baseStart_901420 baseEnd_901420 := by
    simpa [prefixWord, tailWord_901420, baseEnd_901420] using wordTrace_append hprefix tailTrace_901420
  have hstable : (prefixWord ++ tailWord_901420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901420).length < 2 ^ (prefixWord ++ tailWord_901420).sum := by decide
  have hdescent : baseEnd_901420 < baseStart_901420 := by decide
  rcases family_descends (prefixWord ++ tailWord_901420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901460 : List Nat := [2, 4, 1, 1, 2, 4, 2, 7]
def baseStart_901460 : Nat := 118140960795 + 901460 * 2 ^ 59
def prefixEnd_901460 : Nat := 4983230072969 + 3 ^ 40 * 901460 * 2
def baseEnd_901460 : Nat := 17143787807486972863121

theorem tailTrace_901460 : CollatzResearch.WordTrace tailWord_901460 prefixEnd_901460 17143787807486972863121 := by
  unfold tailWord_901460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439473657085925977978917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21919298209447901303971889 16439473657085925977978917)
  ·
    refine ⟨3082401310703611120871047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16439473657085925977978917 3082401310703611120871047)
    ·
      refine ⟨4623601966055416681306571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082401310703611120871047 4623601966055416681306571)
      ·
        refine ⟨6935402949083125021959857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4623601966055416681306571 6935402949083125021959857)
        ·
          refine ⟨5201552211812343766469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6935402949083125021959857 5201552211812343766469893)
          ·
            refine ⟨975291039714814456213105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5201552211812343766469893 975291039714814456213105)
            ·
              refine ⟨731468279786110842159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975291039714814456213105 731468279786110842159829)
              ·
                refine ⟨17143787807486972863121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 731468279786110842159829 17143787807486972863121)
                ·
                  rfl

theorem cell23_901460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 7].length) (baseStart_901460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901460 prefixEnd_901460 := by exact prefixLift 901460
  have htrace : WordTrace (prefixWord ++ tailWord_901460) baseStart_901460 baseEnd_901460 := by
    simpa [prefixWord, tailWord_901460, baseEnd_901460] using wordTrace_append hprefix tailTrace_901460
  have hstable : (prefixWord ++ tailWord_901460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901460).length < 2 ^ (prefixWord ++ tailWord_901460).sum := by decide
  have hdescent : baseEnd_901460 < baseStart_901460 := by decide
  rcases family_descends (prefixWord ++ tailWord_901460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901513 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_901513 : Nat := 118140960795 + 901513 * 2 ^ 59
def prefixEnd_901513 : Nat := 4983230072969 + 3 ^ 40 * 901513 * 2
def baseEnd_901513 : Nat := 462909485276836559941523

theorem tailTrace_901513 : CollatzResearch.WordTrace tailWord_901513 prefixEnd_901513 462909485276836559941523 := by
  unfold tailWord_901513
  simp only [CollatzResearch.WordTrace]
  refine ⟨32880880382979842007637193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21920586921986561338424795 32880880382979842007637193)
  ·
    refine ⟨24660660287234881505727895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32880880382979842007637193 24660660287234881505727895)
    ·
      refine ⟨36990990430852322258591843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24660660287234881505727895 36990990430852322258591843)
      ·
        refine ⟨55486485646278483387887765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36990990430852322258591843 55486485646278483387887765)
        ·
          refine ⟨2600929014669303908807239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55486485646278483387887765 2600929014669303908807239)
          ·
            refine ⟨3901393522003955863210859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600929014669303908807239 3901393522003955863210859)
            ·
              refine ⟨5852090283005933794816289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3901393522003955863210859 5852090283005933794816289)
              ·
                refine ⟨4389067712254450346112217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5852090283005933794816289 4389067712254450346112217)
                ·
                  refine ⟨3291800784190837759584163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4389067712254450346112217 3291800784190837759584163)
                  ·
                    refine ⟨4937701176286256639376245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3291800784190837759584163 4937701176286256639376245)
                    ·
                      refine ⟨462909485276836559941523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4937701176286256639376245 462909485276836559941523)
                      ·
                        rfl

theorem cell23_901513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_901513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901513 prefixEnd_901513 := by exact prefixLift 901513
  have htrace : WordTrace (prefixWord ++ tailWord_901513) baseStart_901513 baseEnd_901513 := by
    simpa [prefixWord, tailWord_901513, baseEnd_901513] using wordTrace_append hprefix tailTrace_901513
  have hstable : (prefixWord ++ tailWord_901513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901513).length < 2 ^ (prefixWord ++ tailWord_901513).sum := by decide
  have hdescent : baseEnd_901513 < baseStart_901513 := by decide
  rcases family_descends (prefixWord ++ tailWord_901513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901514 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_901514 : Nat := 118140960795 + 901514 * 2 ^ 59
def prefixEnd_901514 : Nat := 4983230072969 + 3 ^ 40 * 901514 * 2
def baseEnd_901514 : Nat := 462909998757491056029019

theorem tailTrace_901514 : CollatzResearch.WordTrace tailWord_901514 prefixEnd_901514 462909998757491056029019 := by
  unfold tailWord_901514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220229213994054794605899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21920611237317479452282397 8220229213994054794605899)
  ·
    refine ⟨12330343820991082191908849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8220229213994054794605899 12330343820991082191908849)
    ·
      refine ⟨9247757865743311643931637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12330343820991082191908849 9247757865743311643931637)
      ·
        refine ⟨866977299913435466618591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9247757865743311643931637 866977299913435466618591)
        ·
          refine ⟨1300465949870153199927887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866977299913435466618591 1300465949870153199927887)
          ·
            refine ⟨1950698924805229799891831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300465949870153199927887 1950698924805229799891831)
            ·
              refine ⟨2926048387207844699837747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950698924805229799891831 2926048387207844699837747)
              ·
                refine ⟨4389072580811767049756621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926048387207844699837747 4389072580811767049756621)
                ·
                  refine ⟨1645902217804412643658733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4389072580811767049756621 1645902217804412643658733)
                  ·
                    refine ⟨617213331676654741372025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1645902217804412643658733 617213331676654741372025)
                    ·
                      refine ⟨462909998757491056029019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617213331676654741372025 462909998757491056029019)
                      ·
                        rfl

theorem cell23_901514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_901514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901514 prefixEnd_901514 := by exact prefixLift 901514
  have htrace : WordTrace (prefixWord ++ tailWord_901514) baseStart_901514 baseEnd_901514 := by
    simpa [prefixWord, tailWord_901514, baseEnd_901514] using wordTrace_append hprefix tailTrace_901514
  have hstable : (prefixWord ++ tailWord_901514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901514).length < 2 ^ (prefixWord ++ tailWord_901514).sum := by decide
  have hdescent : baseEnd_901514 < baseStart_901514 := by decide
  rcases family_descends (prefixWord ++ tailWord_901514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901580 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_901580 : Nat := 118140960795 + 901580 * 2 ^ 59
def prefixEnd_901580 : Nat := 4983230072969 + 3 ^ 40 * 901580 * 2
def baseEnd_901580 : Nat := 154314629493562599267905

theorem tailTrace_901580 : CollatzResearch.WordTrace tailWord_901580 prefixEnd_901580 154314629493562599267905 := by
  unfold tailWord_901580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16441662036868556225163097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21922216049158074966884129 16441662036868556225163097)
  ·
    refine ⟨12331246527651417168872323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16441662036868556225163097 12331246527651417168872323)
    ·
      refine ⟨18496869791477125753308485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12331246527651417168872323 18496869791477125753308485)
      ·
        refine ⟨3468163085901961078745341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18496869791477125753308485 3468163085901961078745341)
        ·
          refine ⟨1300561157213235404529503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3468163085901961078745341 1300561157213235404529503)
          ·
            refine ⟨1950841735819853106794255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300561157213235404529503 1950841735819853106794255)
            ·
              refine ⟨2926262603729779660191383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950841735819853106794255 2926262603729779660191383)
              ·
                refine ⟨4389393905594669490287075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926262603729779660191383 4389393905594669490287075)
                ·
                  refine ⟨6584090858392004235430613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389393905594669490287075 6584090858392004235430613)
                  ·
                    refine ⟨154314629493562599267905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6584090858392004235430613 154314629493562599267905)
                    ·
                      rfl

theorem cell23_901580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_901580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901580 prefixEnd_901580 := by exact prefixLift 901580
  have htrace : WordTrace (prefixWord ++ tailWord_901580) baseStart_901580 baseEnd_901580 := by
    simpa [prefixWord, tailWord_901580, baseEnd_901580] using wordTrace_append hprefix tailTrace_901580
  have hstable : (prefixWord ++ tailWord_901580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901580).length < 2 ^ (prefixWord ++ tailWord_901580).sum := by decide
  have hdescent : baseEnd_901580 < baseStart_901580 := by decide
  rcases family_descends (prefixWord ++ tailWord_901580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901600 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2]
def baseStart_901600 : Nat := 118140960795 + 901600 * 2 ^ 59
def prefixEnd_901600 : Nat := 4983230072969 + 3 ^ 40 * 901600 * 2
def baseEnd_901600 : Nat := 462954158093777719553623

theorem tailTrace_901600 : CollatzResearch.WordTrace tailWord_901600 prefixEnd_901600 462954158093777719553623 := by
  unfold tailWord_901600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442026766832327933027127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21922702355776437244036169 16442026766832327933027127)
  ·
    refine ⟨24663040150248491899540691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16442026766832327933027127 24663040150248491899540691)
    ·
      refine ⟨36994560225372737849311037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24663040150248491899540691 36994560225372737849311037)
      ·
        refine ⟨13872960084514776693491639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36994560225372737849311037 13872960084514776693491639)
        ·
          refine ⟨20809440126772165040237459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13872960084514776693491639 20809440126772165040237459)
          ·
            refine ⟨31214160190158247560356189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20809440126772165040237459 31214160190158247560356189)
            ·
              refine ⟨11705310071309342835133571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31214160190158247560356189 11705310071309342835133571)
              ·
                refine ⟨17557965106964014252700357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11705310071309342835133571 17557965106964014252700357)
                ·
                  refine ⟨3292118457555752672381317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17557965106964014252700357 3292118457555752672381317)
                  ·
                    refine ⟨617272210791703626071497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3292118457555752672381317 617272210791703626071497)
                    ·
                      refine ⟨462954158093777719553623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617272210791703626071497 462954158093777719553623)
                      ·
                        rfl

theorem cell23_901600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_901600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901600 prefixEnd_901600 := by exact prefixLift 901600
  have htrace : WordTrace (prefixWord ++ tailWord_901600) baseStart_901600 baseEnd_901600 := by
    simpa [prefixWord, tailWord_901600, baseEnd_901600] using wordTrace_append hprefix tailTrace_901600
  have hstable : (prefixWord ++ tailWord_901600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901600).length < 2 ^ (prefixWord ++ tailWord_901600).sum := by decide
  have hdescent : baseEnd_901600 < baseStart_901600 := by decide
  rcases family_descends (prefixWord ++ tailWord_901600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901644 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_901644 : Nat := 118140960795 + 901644 * 2 ^ 59
def prefixEnd_901644 : Nat := 4983230072969 + 3 ^ 40 * 901644 * 2
def baseEnd_901644 : Nat := 154325583747525182467807

theorem tailTrace_901644 : CollatzResearch.WordTrace tailWord_901644 prefixEnd_901644 154325583747525182467807 := by
  unfold tailWord_901644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16442829172752625690327993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21923772230336834253770657 16442829172752625690327993)
  ·
    refine ⟨12332121879564469267745995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16442829172752625690327993 12332121879564469267745995)
    ·
      refine ⟨18498182819346703901618993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12332121879564469267745995 18498182819346703901618993)
      ·
        refine ⟨13873637114510027926214245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18498182819346703901618993 13873637114510027926214245)
        ·
          refine ⟨2601306958970630236165171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13873637114510027926214245 2601306958970630236165171)
          ·
            refine ⟨3901960438455945354247757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601306958970630236165171 3901960438455945354247757)
            ·
              refine ⟨1463235164420979507842909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3901960438455945354247757 1463235164420979507842909)
              ·
                refine ⟨548713186657867315441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463235164420979507842909 548713186657867315441091)
                ·
                  refine ⟨823069779986800973161637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548713186657867315441091 823069779986800973161637)
                  ·
                    refine ⟨154325583747525182467807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823069779986800973161637 154325583747525182467807)
                    ·
                      rfl

theorem cell23_901644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_901644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901644 prefixEnd_901644 := by exact prefixLift 901644
  have htrace : WordTrace (prefixWord ++ tailWord_901644) baseStart_901644 baseEnd_901644 := by
    simpa [prefixWord, tailWord_901644, baseEnd_901644] using wordTrace_append hprefix tailTrace_901644
  have hstable : (prefixWord ++ tailWord_901644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901644).length < 2 ^ (prefixWord ++ tailWord_901644).sum := by decide
  have hdescent : baseEnd_901644 < baseStart_901644 := by decide
  rcases family_descends (prefixWord ++ tailWord_901644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901661 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_901661 : Nat := 118140960795 + 901661 * 2 ^ 59
def prefixEnd_901661 : Nat := 4983230072969 + 3 ^ 40 * 901661 * 2
def baseEnd_901661 : Nat := 154328493471233993630281

theorem tailTrace_901661 : CollatzResearch.WordTrace tailWord_901661 prefixEnd_901661 154328493471233993630281 := by
  unfold tailWord_901661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32886278386443663284024837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21924185590962442189349891 32886278386443663284024837)
  ·
    refine ⟨6166177197458186865754657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32886278386443663284024837 6166177197458186865754657)
    ·
      refine ⟨4624632898093640149315993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6166177197458186865754657 4624632898093640149315993)
      ·
        refine ⟨3468474673570230111986995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4624632898093640149315993 3468474673570230111986995)
        ·
          refine ⟨5202712010355345167980493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468474673570230111986995 5202712010355345167980493)
          ·
            refine ⟨1951017003883254437992685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5202712010355345167980493 1951017003883254437992685)
            ·
              refine ⟨731631376456220414247257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1951017003883254437992685 731631376456220414247257)
              ·
                refine ⟨548723532342165310685443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731631376456220414247257 548723532342165310685443)
                ·
                  refine ⟨823085298513247966028165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548723532342165310685443 823085298513247966028165)
                  ·
                    refine ⟨154328493471233993630281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823085298513247966028165 154328493471233993630281)
                    ·
                      rfl

theorem cell23_901661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_901661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901661 prefixEnd_901661 := by exact prefixLift 901661
  have htrace : WordTrace (prefixWord ++ tailWord_901661) baseStart_901661 baseEnd_901661 := by
    simpa [prefixWord, tailWord_901661, baseEnd_901661] using wordTrace_append hprefix tailTrace_901661
  have hstable : (prefixWord ++ tailWord_901661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901661).length < 2 ^ (prefixWord ++ tailWord_901661).sum := by decide
  have hdescent : baseEnd_901661 < baseStart_901661 := by decide
  rcases family_descends (prefixWord ++ tailWord_901661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901663 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_901663 : Nat := 118140960795 + 901663 * 2 ^ 59
def prefixEnd_901663 : Nat := 4983230072969 + 3 ^ 40 * 901663 * 2
def baseEnd_901663 : Nat := 462986507375010973065833

theorem tailTrace_901663 : CollatzResearch.WordTrace tailWord_901663 prefixEnd_901663 462986507375010973065833 := by
  unfold tailWord_901663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32886351332436417625597643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21924234221624278417065095 32886351332436417625597643)
  ·
    refine ⟨49329526998654626438396465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32886351332436417625597643 49329526998654626438396465)
    ·
      refine ⟨36997145248990969828797349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49329526998654626438396465 36997145248990969828797349)
      ·
        refine ⟨6936964734185806842899503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36997145248990969828797349 6936964734185806842899503)
        ·
          refine ⟨10405447101278710264349255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6936964734185806842899503 10405447101278710264349255)
          ·
            refine ⟨15608170651918065396523883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10405447101278710264349255 15608170651918065396523883)
            ·
              refine ⟨23412255977877098094785825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15608170651918065396523883 23412255977877098094785825)
              ·
                refine ⟨17559191983407823571089369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23412255977877098094785825 17559191983407823571089369)
                ·
                  refine ⟨13169393987555867678317027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17559191983407823571089369 13169393987555867678317027)
                  ·
                    refine ⟨19754090981333801517475541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13169393987555867678317027 19754090981333801517475541)
                    ·
                      refine ⟨462986507375010973065833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19754090981333801517475541 462986507375010973065833)
                      ·
                        rfl

theorem cell23_901663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_901663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901663 prefixEnd_901663 := by exact prefixLift 901663
  have htrace : WordTrace (prefixWord ++ tailWord_901663) baseStart_901663 baseEnd_901663 := by
    simpa [prefixWord, tailWord_901663, baseEnd_901663] using wordTrace_append hprefix tailTrace_901663
  have hstable : (prefixWord ++ tailWord_901663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901663).length < 2 ^ (prefixWord ++ tailWord_901663).sum := by decide
  have hdescent : baseEnd_901663 < baseStart_901663 := by decide
  rcases family_descends (prefixWord ++ tailWord_901663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901674 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_901674 : Nat := 118140960795 + 901674 * 2 ^ 59
def prefixEnd_901674 : Nat := 4983230072969 + 3 ^ 40 * 901674 * 2
def baseEnd_901674 : Nat := 51443572851356714447587

theorem tailTrace_901674 : CollatzResearch.WordTrace tailWord_901674 prefixEnd_901674 51443572851356714447587 := by
  unfold tailWord_901674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8221688133849141626062019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21924501690264377669498717 8221688133849141626062019)
  ·
    refine ⟨12332532200773712439093029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8221688133849141626062019 12332532200773712439093029)
    ·
      refine ⟨2312349787645071082329943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12332532200773712439093029 2312349787645071082329943)
      ·
        refine ⟨3468524681467606623494915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312349787645071082329943 3468524681467606623494915)
        ·
          refine ⟨5202787022201409935242373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468524681467606623494915 5202787022201409935242373)
          ·
            refine ⟨975522566662764362857945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5202787022201409935242373 975522566662764362857945)
            ·
              refine ⟨731641924997073272143459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975522566662764362857945 731641924997073272143459)
              ·
                refine ⟨1097462887495609908215189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731641924997073272143459 1097462887495609908215189)
                ·
                  refine ⟨51443572851356714447587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1097462887495609908215189 51443572851356714447587)
                  ·
                    rfl

theorem cell23_901674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_901674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901674 prefixEnd_901674 := by exact prefixLift 901674
  have htrace : WordTrace (prefixWord ++ tailWord_901674) baseStart_901674 baseEnd_901674 := by
    simpa [prefixWord, tailWord_901674, baseEnd_901674] using wordTrace_append hprefix tailTrace_901674
  have hstable : (prefixWord ++ tailWord_901674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901674).length < 2 ^ (prefixWord ++ tailWord_901674).sum := by decide
  have hdescent : baseEnd_901674 < baseStart_901674 := by decide
  rcases family_descends (prefixWord ++ tailWord_901674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901713 : List Nat := [1, 2, 2, 1, 3, 14]
def baseStart_901713 : Nat := 118140960795 + 901713 * 2 ^ 59
def prefixEnd_901713 : Nat := 4983230072969 + 3 ^ 40 * 901713 * 2
def baseEnd_901713 : Nat := 1905399923488624598521

theorem tailTrace_901713 : CollatzResearch.WordTrace tailWord_901713 prefixEnd_901713 1905399923488624598521 := by
  unfold tailWord_901713
  simp only [CollatzResearch.WordTrace]
  refine ⟨32888174982255276164917793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21925449988170184109945195 32888174982255276164917793)
  ·
    refine ⟨24666131236691457123688345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32888174982255276164917793 24666131236691457123688345)
    ·
      refine ⟨18499598427518592842766259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24666131236691457123688345 18499598427518592842766259)
      ·
        refine ⟨27749397641277889264149389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18499598427518592842766259 27749397641277889264149389)
        ·
          refine ⟨10406024115479208474056021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27749397641277889264149389 10406024115479208474056021)
          ·
            refine ⟨1905399923488624598521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 10406024115479208474056021 1905399923488624598521)
            ·
              rfl

theorem cell23_901713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 14].length) (baseStart_901713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901713 prefixEnd_901713 := by exact prefixLift 901713
  have htrace : WordTrace (prefixWord ++ tailWord_901713) baseStart_901713 baseEnd_901713 := by
    simpa [prefixWord, tailWord_901713, baseEnd_901713] using wordTrace_append hprefix tailTrace_901713
  have hstable : (prefixWord ++ tailWord_901713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901713).length < 2 ^ (prefixWord ++ tailWord_901713).sum := by decide
  have hdescent : baseEnd_901713 < baseStart_901713 := by decide
  rcases family_descends (prefixWord ++ tailWord_901713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901717 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_901717 : Nat := 118140960795 + 901717 * 2 ^ 59
def prefixEnd_901717 : Nat := 4983230072969 + 3 ^ 40 * 901717 * 2
def baseEnd_901717 : Nat := 154338078443451253930195

theorem tailTrace_901717 : CollatzResearch.WordTrace tailWord_901717 prefixEnd_901717 154338078443451253930195 := by
  unfold tailWord_901717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32888320874240784848063405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21925547249493856565375603 32888320874240784848063405)
  ·
    refine ⟨12333120327840294318023777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32888320874240784848063405 12333120327840294318023777)
    ·
      refine ⟨9249840245880220738517833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12333120327840294318023777 9249840245880220738517833)
      ·
        refine ⟨6937380184410165553888375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9249840245880220738517833 6937380184410165553888375)
        ·
          refine ⟨10406070276615248330832563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6937380184410165553888375 10406070276615248330832563)
          ·
            refine ⟨15609105414922872496248845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10406070276615248330832563 15609105414922872496248845)
            ·
              refine ⟨5853414530596077186093317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15609105414922872496248845 5853414530596077186093317)
              ·
                refine ⟨1097515224486764472392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5853414530596077186093317 1097515224486764472392497)
                ·
                  refine ⟨823136418365073354294373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097515224486764472392497 823136418365073354294373)
                  ·
                    refine ⟨154338078443451253930195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823136418365073354294373 154338078443451253930195)
                    ·
                      rfl

theorem cell23_901717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_901717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901717 prefixEnd_901717 := by exact prefixLift 901717
  have htrace : WordTrace (prefixWord ++ tailWord_901717) baseStart_901717 baseEnd_901717 := by
    simpa [prefixWord, tailWord_901717, baseEnd_901717] using wordTrace_append hprefix tailTrace_901717
  have hstable : (prefixWord ++ tailWord_901717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901717).length < 2 ^ (prefixWord ++ tailWord_901717).sum := by decide
  have hdescent : baseEnd_901717 < baseStart_901717 := by decide
  rcases family_descends (prefixWord ++ tailWord_901717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901741 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_901741 : Nat := 118140960795 + 901741 * 2 ^ 59
def prefixEnd_901741 : Nat := 4983230072969 + 3 ^ 40 * 901741 * 2
def baseEnd_901741 : Nat := 463026558866061667890475

theorem tailTrace_901741 : CollatzResearch.WordTrace tailWord_901741 prefixEnd_901741 463026558866061667890475 := by
  unfold tailWord_901741
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889196226153836946937077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21926130817435891297958051 32889196226153836946937077)
  ·
    refine ⟨3083362146201922213775351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32889196226153836946937077 3083362146201922213775351)
    ·
      refine ⟨4625043219302883320663027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083362146201922213775351 4625043219302883320663027)
      ·
        refine ⟨6937564828954324980994541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4625043219302883320663027 6937564828954324980994541)
        ·
          refine ⟨2601586810857871867872953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6937564828954324980994541 2601586810857871867872953)
          ·
            refine ⟨1951190108143403900904715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2601586810857871867872953 1951190108143403900904715)
            ·
              refine ⟨2926785162215105851357073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951190108143403900904715 2926785162215105851357073)
              ·
                refine ⟨2195088871661329388517805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926785162215105851357073 2195088871661329388517805)
                ·
                  refine ⟨823158326872998520694177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2195088871661329388517805 823158326872998520694177)
                  ·
                    refine ⟨617368745154748890520633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823158326872998520694177 617368745154748890520633)
                    ·
                      refine ⟨463026558866061667890475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617368745154748890520633 463026558866061667890475)
                      ·
                        rfl

theorem cell23_901741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_901741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901741 prefixEnd_901741 := by exact prefixLift 901741
  have htrace : WordTrace (prefixWord ++ tailWord_901741) baseStart_901741 baseEnd_901741 := by
    simpa [prefixWord, tailWord_901741, baseEnd_901741] using wordTrace_append hprefix tailTrace_901741
  have hstable : (prefixWord ++ tailWord_901741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901741).length < 2 ^ (prefixWord ++ tailWord_901741).sum := by decide
  have hdescent : baseEnd_901741 < baseStart_901741 := by decide
  rcases family_descends (prefixWord ++ tailWord_901741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901774 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_901774 : Nat := 118140960795 + 901774 * 2 ^ 59
def prefixEnd_901774 : Nat := 4983230072969 + 3 ^ 40 * 901774 * 2
def baseEnd_901774 : Nat := 463043503727660038777823

theorem tailTrace_901774 : CollatzResearch.WordTrace tailWord_901774 prefixEnd_901774 463043503727660038777823 := by
  unfold tailWord_901774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111299979379285447861047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21926933223356189055258917 4111299979379285447861047)
  ·
    refine ⟨6166949969068928171791571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111299979379285447861047 6166949969068928171791571)
    ·
      refine ⟨9250424953603392257687357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6166949969068928171791571 9250424953603392257687357)
      ·
        refine ⟨3468909357601272096632759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9250424953603392257687357 3468909357601272096632759)
        ·
          refine ⟨5203364036401908144949139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468909357601272096632759 5203364036401908144949139)
          ·
            refine ⟨7805046054602862217423709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203364036401908144949139 7805046054602862217423709)
            ·
              refine ⟨2926892270476073331533891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7805046054602862217423709 2926892270476073331533891)
              ·
                refine ⟨4390338405714109997300837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926892270476073331533891 4390338405714109997300837)
                ·
                  refine ⟨823188451071395624493907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4390338405714109997300837 823188451071395624493907)
                  ·
                    refine ⟨1234782676607093436740861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 823188451071395624493907 1234782676607093436740861)
                    ·
                      refine ⟨463043503727660038777823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1234782676607093436740861 463043503727660038777823)
                      ·
                        rfl

theorem cell23_901774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_901774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901774 prefixEnd_901774 := by exact prefixLift 901774
  have htrace : WordTrace (prefixWord ++ tailWord_901774) baseStart_901774 baseEnd_901774 := by
    simpa [prefixWord, tailWord_901774, baseEnd_901774] using wordTrace_append hprefix tailTrace_901774
  have hstable : (prefixWord ++ tailWord_901774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901774).length < 2 ^ (prefixWord ++ tailWord_901774).sum := by decide
  have hdescent : baseEnd_901774 < baseStart_901774 := by decide
  rcases family_descends (prefixWord ++ tailWord_901774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901848 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_901848 : Nat := 118140960795 + 901848 * 2 ^ 59
def prefixEnd_901848 : Nat := 4983230072969 + 3 ^ 40 * 901848 * 2
def baseEnd_901848 : Nat := 463081501296092749252483

theorem tailTrace_901848 : CollatzResearch.WordTrace tailWord_901848 prefixEnd_901848 463081501296092749252483 := by
  unfold tailWord_901848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446549418383097110541099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21928732557844129480721465 16446549418383097110541099)
  ·
    refine ⟨24669824127574645665811649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16446549418383097110541099 24669824127574645665811649)
    ·
      refine ⟨18502368095680984249358737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24669824127574645665811649 18502368095680984249358737)
      ·
        refine ⟨13876776071760738187019053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18502368095680984249358737 13876776071760738187019053)
        ·
          refine ⟨5203791026910276820132145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13876776071760738187019053 5203791026910276820132145)
          ·
            refine ⟨3902843270182707615099109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5203791026910276820132145 3902843270182707615099109)
            ·
              refine ⟨731783113159257677831083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3902843270182707615099109 731783113159257677831083)
              ·
                refine ⟨1097674669738886516746625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731783113159257677831083 1097674669738886516746625)
                ·
                  refine ⟨823256002304164887559969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097674669738886516746625 823256002304164887559969)
                  ·
                    refine ⟨617442001728123665669977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823256002304164887559969 617442001728123665669977)
                    ·
                      refine ⟨463081501296092749252483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617442001728123665669977 463081501296092749252483)
                      ·
                        rfl

theorem cell23_901848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_901848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901848 prefixEnd_901848 := by exact prefixLift 901848
  have htrace : WordTrace (prefixWord ++ tailWord_901848) baseStart_901848 baseEnd_901848 := by
    simpa [prefixWord, tailWord_901848, baseEnd_901848] using wordTrace_append hprefix tailTrace_901848
  have hstable : (prefixWord ++ tailWord_901848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901848).length < 2 ^ (prefixWord ++ tailWord_901848).sum := by decide
  have hdescent : baseEnd_901848 < baseStart_901848 := by decide
  rcases family_descends (prefixWord ++ tailWord_901848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901907 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3]
def baseStart_901907 : Nat := 118140960795 + 901907 * 2 ^ 59
def prefixEnd_901907 : Nat := 4983230072969 + 3 ^ 40 * 901907 * 2
def baseEnd_901907 : Nat := 463111796654708018414711

theorem tailTrace_901907 : CollatzResearch.WordTrace tailWord_901907 prefixEnd_901907 463111796654708018414711 := by
  unfold tailWord_901907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32895250743552447297479975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21930167162368298198319983 32895250743552447297479975)
  ·
    refine ⟨49342876115328670946219963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32895250743552447297479975 49342876115328670946219963)
    ·
      refine ⟨74014314172993006419329945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49342876115328670946219963 74014314172993006419329945)
      ·
        refine ⟨55510735629744754814497459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74014314172993006419329945 55510735629744754814497459)
        ·
          refine ⟨83266103444617132221746189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55510735629744754814497459 83266103444617132221746189)
          ·
            refine ⟨31224788791731424583154821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83266103444617132221746189 31224788791731424583154821)
            ·
              refine ⟨5854647898449642109341529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31224788791731424583154821 5854647898449642109341529)
              ·
                refine ⟨4390985923837231582006147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5854647898449642109341529 4390985923837231582006147)
                ·
                  refine ⟨6586478885755847373009221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390985923837231582006147 6586478885755847373009221)
                  ·
                    refine ⟨1234964791079221382439229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6586478885755847373009221 1234964791079221382439229)
                    ·
                      refine ⟨463111796654708018414711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1234964791079221382439229 463111796654708018414711)
                      ·
                        rfl

theorem cell23_901907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_901907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901907 prefixEnd_901907 := by exact prefixLift 901907
  have htrace : WordTrace (prefixWord ++ tailWord_901907) baseStart_901907 baseEnd_901907 := by
    simpa [prefixWord, tailWord_901907, baseEnd_901907] using wordTrace_append hprefix tailTrace_901907
  have hstable : (prefixWord ++ tailWord_901907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901907).length < 2 ^ (prefixWord ++ tailWord_901907).sum := by decide
  have hdescent : baseEnd_901907 < baseStart_901907 := by decide
  rcases family_descends (prefixWord ++ tailWord_901907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901914 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_901914 : Nat := 118140960795 + 901914 * 2 ^ 59
def prefixEnd_901914 : Nat := 4983230072969 + 3 ^ 40 * 901914 * 2
def baseEnd_901914 : Nat := 154371797006429830342393

theorem tailTrace_901914 : CollatzResearch.WordTrace tailWord_901914 prefixEnd_901914 154371797006429830342393 := by
  unfold tailWord_901914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8223876513631771873246199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21930337369684724995323197 8223876513631771873246199)
  ·
    refine ⟨12335814770447657809869299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8223876513631771873246199 12335814770447657809869299)
    ·
      refine ⟨18503722155671486714803949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12335814770447657809869299 18503722155671486714803949)
      ·
        refine ⟨6938895808376807518051481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18503722155671486714803949 6938895808376807518051481)
        ·
          refine ⟨5204171856282605638538611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6938895808376807518051481 5204171856282605638538611)
          ·
            refine ⟨7806257784423908457807917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204171856282605638538611 7806257784423908457807917)
            ·
              refine ⟨2927346669158965671677969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7806257784423908457807917 2927346669158965671677969)
              ·
                refine ⟨2195510001869224253758477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927346669158965671677969 2195510001869224253758477)
                ·
                  refine ⟨823316250700959095159429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2195510001869224253758477 823316250700959095159429)
                  ·
                    refine ⟨154371797006429830342393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823316250700959095159429 154371797006429830342393)
                    ·
                      rfl

theorem cell23_901914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_901914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901914 prefixEnd_901914 := by exact prefixLift 901914
  have htrace : WordTrace (prefixWord ++ tailWord_901914) baseStart_901914 baseEnd_901914 := by
    simpa [prefixWord, tailWord_901914, baseEnd_901914] using wordTrace_append hprefix tailTrace_901914
  have hstable : (prefixWord ++ tailWord_901914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901914).length < 2 ^ (prefixWord ++ tailWord_901914).sum := by decide
  have hdescent : baseEnd_901914 < baseStart_901914 := by decide
  rcases family_descends (prefixWord ++ tailWord_901914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901934 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_901934 : Nat := 118140960795 + 901934 * 2 ^ 59
def prefixEnd_901934 : Nat := 4983230072969 + 3 ^ 40 * 901934 * 2
def baseEnd_901934 : Nat := 463125660632379412777087

theorem tailTrace_901934 : CollatzResearch.WordTrace tailWord_901934 prefixEnd_901934 463125660632379412777087 := by
  unfold tailWord_901934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112029439306828863589107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21930823676303087272475237 4112029439306828863589107)
  ·
    refine ⟨6168044158960243295383661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4112029439306828863589107 6168044158960243295383661)
    ·
      refine ⟨2313016559610091235768873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6168044158960243295383661 2313016559610091235768873)
      ·
        refine ⟨1734762419707568426826655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2313016559610091235768873 1734762419707568426826655)
        ·
          refine ⟨2602143629561352640239983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734762419707568426826655 2602143629561352640239983)
          ·
            refine ⟨3903215444342028960359975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602143629561352640239983 3903215444342028960359975)
            ·
              refine ⟨5854823166513043440539963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903215444342028960359975 5854823166513043440539963)
              ·
                refine ⟨8782234749769565160809945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854823166513043440539963 8782234749769565160809945)
                ·
                  refine ⟨6586676062327173870607459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8782234749769565160809945 6586676062327173870607459)
                  ·
                    refine ⟨9880014093490760805911189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586676062327173870607459 9880014093490760805911189)
                    ·
                      refine ⟨463125660632379412777087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9880014093490760805911189 463125660632379412777087)
                      ·
                        rfl

theorem cell23_901934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_901934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901934 prefixEnd_901934 := by exact prefixLift 901934
  have htrace : WordTrace (prefixWord ++ tailWord_901934) baseStart_901934 baseEnd_901934 := by
    simpa [prefixWord, tailWord_901934, baseEnd_901934] using wordTrace_append hprefix tailTrace_901934
  have hstable : (prefixWord ++ tailWord_901934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901934).length < 2 ^ (prefixWord ++ tailWord_901934).sum := by decide
  have hdescent : baseEnd_901934 < baseStart_901934 := by decide
  rcases family_descends (prefixWord ++ tailWord_901934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901957 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_901957 : Nat := 118140960795 + 901957 * 2 ^ 59
def prefixEnd_901957 : Nat := 4983230072969 + 3 ^ 40 * 901957 * 2
def baseEnd_901957 : Nat := 154379156895810940929827

theorem tailTrace_901957 : CollatzResearch.WordTrace tailWord_901957 prefixEnd_901957 154379156895810940929827 := by
  unfold tailWord_901957
  simp only [CollatzResearch.WordTrace]
  refine ⟨32897074393371305836800125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931382928914203891200083 32897074393371305836800125)
  ·
    refine ⟨12336402897514239688800047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32897074393371305836800125 12336402897514239688800047)
    ·
      refine ⟨18504604346271359533200071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336402897514239688800047 18504604346271359533200071)
      ·
        refine ⟨27756906519407039299800107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504604346271359533200071 27756906519407039299800107)
        ·
          refine ⟨41635359779110558949700161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756906519407039299800107 41635359779110558949700161)
          ·
            refine ⟨31226519834332919212275121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41635359779110558949700161 31226519834332919212275121)
            ·
              refine ⟨23419889875749689409206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31226519834332919212275121 23419889875749689409206341)
              ·
                refine ⟨4391229351703066764226189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23419889875749689409206341 4391229351703066764226189)
                ·
                  refine ⟨1646711006888650036584821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4391229351703066764226189 1646711006888650036584821)
                  ·
                    refine ⟨154379156895810940929827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1646711006888650036584821 154379156895810940929827)
                    ·
                      rfl

theorem cell23_901957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_901957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_901957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_901957 prefixEnd_901957 := by exact prefixLift 901957
  have htrace : WordTrace (prefixWord ++ tailWord_901957) baseStart_901957 baseEnd_901957 := by
    simpa [prefixWord, tailWord_901957, baseEnd_901957] using wordTrace_append hprefix tailTrace_901957
  have hstable : (prefixWord ++ tailWord_901957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901957).length < 2 ^ (prefixWord ++ tailWord_901957).sum := by decide
  have hdescent : baseEnd_901957 < baseStart_901957 := by decide
  rcases family_descends (prefixWord ++ tailWord_901957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902021 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_902021 : Nat := 118140960795 + 902021 * 2 ^ 59
def prefixEnd_902021 : Nat := 4983230072969 + 3 ^ 40 * 902021 * 2
def baseEnd_902021 : Nat := 154390111149773524129729

theorem tailTrace_902021 : CollatzResearch.WordTrace tailWord_902021 prefixEnd_902021 154390111149773524129729 := by
  unfold tailWord_902021
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899408665139444767129917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21932939110092963178086611 32899408665139444767129917)
  ·
    refine ⟨12337278249427291787673719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32899408665139444767129917 12337278249427291787673719)
    ·
      refine ⟨18505917374140937681510579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337278249427291787673719 18505917374140937681510579)
      ·
        refine ⟨27758876061211406522265869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18505917374140937681510579 27758876061211406522265869)
        ·
          refine ⟨10409578522954277445849701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27758876061211406522265869 10409578522954277445849701)
          ·
            refine ⟨1951795973053927021096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10409578522954277445849701 1951795973053927021096819)
            ·
              refine ⟨2927693959580890531645229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951795973053927021096819 2927693959580890531645229)
              ·
                refine ⟨1097885234842833949366961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2927693959580890531645229 1097885234842833949366961)
                ·
                  refine ⟨823413926132125462025221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097885234842833949366961 823413926132125462025221)
                  ·
                    refine ⟨154390111149773524129729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823413926132125462025221 154390111149773524129729)
                    ·
                      rfl

theorem cell23_902021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_902021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902021 prefixEnd_902021 := by exact prefixLift 902021
  have htrace : WordTrace (prefixWord ++ tailWord_902021) baseStart_902021 baseEnd_902021 := by
    simpa [prefixWord, tailWord_902021, baseEnd_902021] using wordTrace_append hprefix tailTrace_902021
  have hstable : (prefixWord ++ tailWord_902021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902021).length < 2 ^ (prefixWord ++ tailWord_902021).sum := by decide
  have hdescent : baseEnd_902021 < baseStart_902021 := by decide
  rcases family_descends (prefixWord ++ tailWord_902021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902024 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_902024 : Nat := 118140960795 + 902024 * 2 ^ 59
def prefixEnd_902024 : Nat := 4983230072969 + 3 ^ 40 * 902024 * 2
def baseEnd_902024 : Nat := 463171873891284060651673

theorem tailTrace_902024 : CollatzResearch.WordTrace tailWord_902024 prefixEnd_902024 463171873891284060651673 := by
  unfold tailWord_902024
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449759042064288139744563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21933012056085717519659417 16449759042064288139744563)
  ·
    refine ⟨24674638563096432209616845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16449759042064288139744563 24674638563096432209616845)
    ·
      refine ⟨9252989461161162078606317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24674638563096432209616845 9252989461161162078606317)
      ·
        refine ⟨3469871047935435779477369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9252989461161162078606317 3469871047935435779477369)
        ·
          refine ⟨2602403285951576834608027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3469871047935435779477369 2602403285951576834608027)
          ·
            refine ⟨3903604928927365251912041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602403285951576834608027 3903604928927365251912041)
            ·
              refine ⟨2927703696695523938934031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903604928927365251912041 2927703696695523938934031)
              ·
                refine ⟨4391555545043285908401047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927703696695523938934031 4391555545043285908401047)
                ·
                  refine ⟨6587333317564928862601571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391555545043285908401047 6587333317564928862601571)
                  ·
                    refine ⟨9880999976347393293902357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6587333317564928862601571 9880999976347393293902357)
                    ·
                      refine ⟨463171873891284060651673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9880999976347393293902357 463171873891284060651673)
                      ·
                        rfl

theorem cell23_902024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_902024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902024 prefixEnd_902024 := by exact prefixLift 902024
  have htrace : WordTrace (prefixWord ++ tailWord_902024) baseStart_902024 baseEnd_902024 := by
    simpa [prefixWord, tailWord_902024, baseEnd_902024] using wordTrace_append hprefix tailTrace_902024
  have hstable : (prefixWord ++ tailWord_902024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902024).length < 2 ^ (prefixWord ++ tailWord_902024).sum := by decide
  have hdescent : baseEnd_902024 < baseStart_902024 := by decide
  rcases family_descends (prefixWord ++ tailWord_902024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902038 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_902038 : Nat := 118140960795 + 902038 * 2 ^ 59
def prefixEnd_902038 : Nat := 4983230072969 + 3 ^ 40 * 902038 * 2
def baseEnd_902038 : Nat := 154393020873482335292203

theorem tailTrace_902038 : CollatzResearch.WordTrace tailWord_902038 prefixEnd_902038 154393020873482335292203 := by
  unfold tailWord_902038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056251794129866041906173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21933352470718571113665845 2056251794129866041906173)
  ·
    refine ⟨771094422798699765714815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2056251794129866041906173 771094422798699765714815)
    ·
      refine ⟨1156641634198049648572223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771094422798699765714815 1156641634198049648572223)
      ·
        refine ⟨1734962451297074472858335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156641634198049648572223 1734962451297074472858335)
        ·
          refine ⟨2602443676945611709287503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1734962451297074472858335 2602443676945611709287503)
          ·
            refine ⟨3903665515418417563931255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602443676945611709287503 3903665515418417563931255)
            ·
              refine ⟨5855498273127626345896883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903665515418417563931255 5855498273127626345896883)
              ·
                refine ⟨8783247409691439518845325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855498273127626345896883 8783247409691439518845325)
                ·
                  refine ⟨3293717778634289819566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8783247409691439518845325 3293717778634289819566997)
                  ·
                    refine ⟨154393020873482335292203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3293717778634289819566997 154393020873482335292203)
                    ·
                      rfl

theorem cell23_902038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_902038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902038 prefixEnd_902038 := by exact prefixLift 902038
  have htrace : WordTrace (prefixWord ++ tailWord_902038) baseStart_902038 baseEnd_902038 := by
    simpa [prefixWord, tailWord_902038, baseEnd_902038] using wordTrace_append hprefix tailTrace_902038
  have hstable : (prefixWord ++ tailWord_902038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902038).length < 2 ^ (prefixWord ++ tailWord_902038).sum := by decide
  have hdescent : baseEnd_902038 < baseStart_902038 := by decide
  rcases family_descends (prefixWord ++ tailWord_902038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902045 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_902045 : Nat := 118140960795 + 902045 * 2 ^ 59
def prefixEnd_902045 : Nat := 4983230072969 + 3 ^ 40 * 902045 * 2
def baseEnd_902045 : Nat := 463182656985028478489077

theorem tailTrace_902045 : CollatzResearch.WordTrace tailWord_902045 prefixEnd_902045 463182656985028478489077 := by
  unfold tailWord_902045
  simp only [CollatzResearch.WordTrace]
  refine ⟨32900284017052496866003589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21933522678034997910669059 32900284017052496866003589)
  ·
    refine ⟨6168803253197343162375673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32900284017052496866003589 6168803253197343162375673)
    ·
      refine ⟨4626602439898007371781755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6168803253197343162375673 4626602439898007371781755)
      ·
        refine ⟨6939903659847011057672633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626602439898007371781755 6939903659847011057672633)
        ·
          refine ⟨5204927744885258293254475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6939903659847011057672633 5204927744885258293254475)
          ·
            refine ⟨7807391617327887439881713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204927744885258293254475 7807391617327887439881713)
            ·
              refine ⟨5855543712995915579911285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7807391617327887439881713 5855543712995915579911285)
              ·
                refine ⟨548957223093367085616683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5855543712995915579911285 548957223093367085616683)
                ·
                  refine ⟨823435834640050628425025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548957223093367085616683 823435834640050628425025)
                  ·
                    refine ⟨617576875980037971318769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823435834640050628425025 617576875980037971318769)
                    ·
                      refine ⟨463182656985028478489077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617576875980037971318769 463182656985028478489077)
                      ·
                        rfl

theorem cell23_902045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_902045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902045 prefixEnd_902045 := by exact prefixLift 902045
  have htrace : WordTrace (prefixWord ++ tailWord_902045) baseStart_902045 baseEnd_902045 := by
    simpa [prefixWord, tailWord_902045, baseEnd_902045] using wordTrace_append hprefix tailTrace_902045
  have hstable : (prefixWord ++ tailWord_902045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902045).length < 2 ^ (prefixWord ++ tailWord_902045).sum := by decide
  have hdescent : baseEnd_902045 < baseStart_902045 := by decide
  rcases family_descends (prefixWord ++ tailWord_902045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902068 : List Nat := [2, 5, 2, 1, 1, 3, 1, 8]
def baseStart_902068 : Nat := 118140960795 + 902068 * 2 ^ 59
def prefixEnd_902068 : Nat := 4983230072969 + 3 ^ 40 * 902068 * 2
def baseEnd_902068 : Nat := 17155350631114144018573

theorem tailTrace_902068 : CollatzResearch.WordTrace tailWord_902068 prefixEnd_902068 17155350631114144018573 := by
  unfold tailWord_902068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450561447984585897045429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21934081930646114529393905 16450561447984585897045429)
  ·
    refine ⟨1542240135748554927848009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16450561447984585897045429 1542240135748554927848009)
    ·
      refine ⟨1156680101811416195886007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542240135748554927848009 1156680101811416195886007)
      ·
        refine ⟨1735020152717124293829011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156680101811416195886007 1735020152717124293829011)
        ·
          refine ⟨2602530229075686440743517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735020152717124293829011 2602530229075686440743517)
          ·
            refine ⟨975948835903382415278819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2602530229075686440743517 975948835903382415278819)
            ·
              refine ⟨1463923253855073622918229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975948835903382415278819 1463923253855073622918229)
              ·
                refine ⟨17155350631114144018573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1463923253855073622918229 17155350631114144018573)
                ·
                  rfl

theorem cell23_902068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 8].length) (baseStart_902068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902068 prefixEnd_902068 := by exact prefixLift 902068
  have htrace : WordTrace (prefixWord ++ tailWord_902068) baseStart_902068 baseEnd_902068 := by
    simpa [prefixWord, tailWord_902068, baseEnd_902068] using wordTrace_append hprefix tailTrace_902068
  have hstable : (prefixWord ++ tailWord_902068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902068).length < 2 ^ (prefixWord ++ tailWord_902068).sum := by decide
  have hdescent : baseEnd_902068 < baseStart_902068 := by decide
  rcases family_descends (prefixWord ++ tailWord_902068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902071 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_902071 : Nat := 118140960795 + 902071 * 2 ^ 59
def prefixEnd_902071 : Nat := 4983230072969 + 3 ^ 40 * 902071 * 2
def baseEnd_902071 : Nat := 463196007482045376763957

theorem tailTrace_902071 : CollatzResearch.WordTrace tailWord_902071 prefixEnd_902071 463196007482045376763957 := by
  unfold tailWord_902071
  simp only [CollatzResearch.WordTrace]
  refine ⟨32901232314958303306450067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21934154876638868870966711 32901232314958303306450067)
  ·
    refine ⟨49351848472437454959675101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32901232314958303306450067 49351848472437454959675101)
    ·
      refine ⟨18506943177164045609878163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49351848472437454959675101 18506943177164045609878163)
      ·
        refine ⟨27760414765746068414817245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18506943177164045609878163 27760414765746068414817245)
        ·
          refine ⟨10410155537154775655556467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27760414765746068414817245 10410155537154775655556467)
          ·
            refine ⟨15615233305732163483334701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410155537154775655556467 15615233305732163483334701)
            ·
              refine ⟨5855712489649561306250513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15615233305732163483334701 5855712489649561306250513)
              ·
                refine ⟨4391784367237170979687885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5855712489649561306250513 4391784367237170979687885)
                ·
                  refine ⟨1646919137713939117382957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4391784367237170979687885 1646919137713939117382957)
                  ·
                    refine ⟨617594676642727169018609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646919137713939117382957 617594676642727169018609)
                    ·
                      refine ⟨463196007482045376763957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617594676642727169018609 463196007482045376763957)
                      ·
                        rfl

theorem cell23_902071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_902071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902071 prefixEnd_902071 := by exact prefixLift 902071
  have htrace : WordTrace (prefixWord ++ tailWord_902071) baseStart_902071 baseEnd_902071 := by
    simpa [prefixWord, tailWord_902071, baseEnd_902071] using wordTrace_append hprefix tailTrace_902071
  have hstable : (prefixWord ++ tailWord_902071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902071).length < 2 ^ (prefixWord ++ tailWord_902071).sum := by decide
  have hdescent : baseEnd_902071 < baseStart_902071 := by decide
  rcases family_descends (prefixWord ++ tailWord_902071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902078 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_902078 : Nat := 118140960795 + 902078 * 2 ^ 59
def prefixEnd_902078 : Nat := 4983230072969 + 3 ^ 40 * 902078 * 2
def baseEnd_902078 : Nat := 463199601846626849376425

theorem tailTrace_902078 : CollatzResearch.WordTrace tailWord_902078 prefixEnd_902078 463199601846626849376425 := by
  unfold tailWord_902078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112685953241617937744361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21934325083955295667969925 4112685953241617937744361)
  ·
    refine ⟨3084514464931213453308271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4112685953241617937744361 3084514464931213453308271)
    ·
      refine ⟨4626771697396820179962407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084514464931213453308271 4626771697396820179962407)
      ·
        refine ⟨6940157546095230269943611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626771697396820179962407 6940157546095230269943611)
        ·
          refine ⟨10410236319142845404915417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940157546095230269943611 10410236319142845404915417)
          ·
            refine ⟨7807677239357134053686563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10410236319142845404915417 7807677239357134053686563)
            ·
              refine ⟨11711515859035701080529845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7807677239357134053686563 11711515859035701080529845)
              ·
                refine ⟨1097954611784596976299673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11711515859035701080529845 1097954611784596976299673)
                ·
                  refine ⟨823465958838447732224755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1097954611784596976299673 823465958838447732224755)
                  ·
                    refine ⟨1235198938257671598337133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 823465958838447732224755 1235198938257671598337133)
                    ·
                      refine ⟨463199601846626849376425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1235198938257671598337133 463199601846626849376425)
                      ·
                        rfl

theorem cell23_902078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_902078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902078 prefixEnd_902078 := by exact prefixLift 902078
  have htrace : WordTrace (prefixWord ++ tailWord_902078) baseStart_902078 baseEnd_902078 := by
    simpa [prefixWord, tailWord_902078, baseEnd_902078] using wordTrace_append hprefix tailTrace_902078
  have hstable : (prefixWord ++ tailWord_902078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902078).length < 2 ^ (prefixWord ++ tailWord_902078).sum := by decide
  have hdescent : baseEnd_902078 < baseStart_902078 := by decide
  rcases family_descends (prefixWord ++ tailWord_902078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902105 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 1, 3, 2]
def baseStart_902105 : Nat := 118140960795 + 902105 * 2 ^ 59
def prefixEnd_902105 : Nat := 4983230072969 + 3 ^ 40 * 902105 * 2
def baseEnd_902105 : Nat := 463213465824298243738801

theorem tailTrace_902105 : CollatzResearch.WordTrace tailWord_902105 prefixEnd_902105 463213465824298243738801 := by
  unfold tailWord_902105
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902472396835127113187769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21934981597890084742125179 32902472396835127113187769)
  ·
    refine ⟨24676854297626345334890827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32902472396835127113187769 24676854297626345334890827)
    ·
      refine ⟨37015281446439518002336241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24676854297626345334890827 37015281446439518002336241)
      ·
        refine ⟨27761461084829638501752181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37015281446439518002336241 27761461084829638501752181)
        ·
          refine ⟨2602636976702778609539267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27761461084829638501752181 2602636976702778609539267)
          ·
            refine ⟨3903955465054167914308901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602636976702778609539267 3903955465054167914308901)
            ·
              refine ⟨731991649697656483932919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3903955465054167914308901 731991649697656483932919)
              ·
                refine ⟨1097987474546484725899379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731991649697656483932919 1097987474546484725899379)
                ·
                  refine ⟨1646981211819727088849069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097987474546484725899379 1646981211819727088849069)
                  ·
                    refine ⟨617617954432397658318401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1646981211819727088849069 617617954432397658318401)
                    ·
                      refine ⟨463213465824298243738801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617617954432397658318401 463213465824298243738801)
                      ·
                        rfl

theorem cell23_902105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_902105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902105 prefixEnd_902105 := by exact prefixLift 902105
  have htrace : WordTrace (prefixWord ++ tailWord_902105) baseStart_902105 baseEnd_902105 := by
    simpa [prefixWord, tailWord_902105, baseEnd_902105] using wordTrace_append hprefix tailTrace_902105
  have hstable : (prefixWord ++ tailWord_902105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902105).length < 2 ^ (prefixWord ++ tailWord_902105).sum := by decide
  have hdescent : baseEnd_902105 < baseStart_902105 := by decide
  rcases family_descends (prefixWord ++ tailWord_902105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902158 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_902158 : Nat := 118140960795 + 902158 * 2 ^ 59
def prefixEnd_902158 : Nat := 4983230072969 + 3 ^ 40 * 902158 * 2
def baseEnd_902158 : Nat := 51471186699887392930673

theorem tailTrace_902158 : CollatzResearch.WordTrace tailWord_902158 prefixEnd_902158 51471186699887392930673 := by
  unfold tailWord_902158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113050683205389645608391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21936270310428744776578085 4113050683205389645608391)
  ·
    refine ⟨6169576024808084468412587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113050683205389645608391 6169576024808084468412587)
    ·
      refine ⟨9254364037212126702618881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6169576024808084468412587 9254364037212126702618881)
      ·
        refine ⟨6940773027909095026964161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9254364037212126702618881 6940773027909095026964161)
        ·
          refine ⟨5205579770931821270223121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6940773027909095026964161 5205579770931821270223121)
          ·
            refine ⟨3904184828198865952667341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5205579770931821270223121 3904184828198865952667341)
            ·
              refine ⟨1464069310574574732250253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904184828198865952667341 1464069310574574732250253)
              ·
                refine ⟨549025991465465524593845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464069310574574732250253 549025991465465524593845)
                ·
                  refine ⟨51471186699887392930673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 549025991465465524593845 51471186699887392930673)
                  ·
                    rfl

theorem cell23_902158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_902158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902158 prefixEnd_902158 := by exact prefixLift 902158
  have htrace : WordTrace (prefixWord ++ tailWord_902158) baseStart_902158 baseEnd_902158 := by
    simpa [prefixWord, tailWord_902158, baseEnd_902158] using wordTrace_append hprefix tailTrace_902158
  have hstable : (prefixWord ++ tailWord_902158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902158).length < 2 ^ (prefixWord ++ tailWord_902158).sum := by decide
  have hdescent : baseEnd_902158 < baseStart_902158 := by decide
  rcases family_descends (prefixWord ++ tailWord_902158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902186 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_902186 : Nat := 118140960795 + 902186 * 2 ^ 59
def prefixEnd_902186 : Nat := 4983230072969 + 3 ^ 40 * 902186 * 2
def baseEnd_902186 : Nat := 463255057757312426825929

theorem tailTrace_902186 : CollatzResearch.WordTrace tailWord_902186 prefixEnd_902186 463255057757312426825929 := by
  unfold tailWord_902186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8226356677385419486721603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21936951139694451964590941 8226356677385419486721603)
  ·
    refine ⟨12339535016078129230082405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8226356677385419486721603 12339535016078129230082405)
    ·
      refine ⟨2313662815514649230640451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12339535016078129230082405 2313662815514649230640451)
      ·
        refine ⟨3470494223271973845960677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313662815514649230640451 3470494223271973845960677)
        ·
          refine ⟨650717666863495096117627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3470494223271973845960677 650717666863495096117627)
          ·
            refine ⟨976076500295242644176441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650717666863495096117627 976076500295242644176441)
            ·
              refine ⟨732057375221431983132331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976076500295242644176441 732057375221431983132331)
              ·
                refine ⟨1098086062832147974698497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732057375221431983132331 1098086062832147974698497)
                ·
                  refine ⟨823564547124110981023873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098086062832147974698497 823564547124110981023873)
                  ·
                    refine ⟨617673410343083235767905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 823564547124110981023873 617673410343083235767905)
                    ·
                      refine ⟨463255057757312426825929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617673410343083235767905 463255057757312426825929)
                      ·
                        rfl

theorem cell23_902186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_902186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902186 prefixEnd_902186 := by exact prefixLift 902186
  have htrace : WordTrace (prefixWord ++ tailWord_902186) baseStart_902186 baseEnd_902186 := by
    simpa [prefixWord, tailWord_902186, baseEnd_902186] using wordTrace_append hprefix tailTrace_902186
  have hstable : (prefixWord ++ tailWord_902186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902186).length < 2 ^ (prefixWord ++ tailWord_902186).sum := by decide
  have hdescent : baseEnd_902186 < baseStart_902186 := by decide
  rcases family_descends (prefixWord ++ tailWord_902186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902191 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 6, 4, 2]
def baseStart_902191 : Nat := 118140960795 + 902191 * 2 ^ 59
def prefixEnd_902191 : Nat := 4983230072969 + 3 ^ 40 * 902191 * 2
def baseEnd_902191 : Nat := 463257625160584907263405

theorem tailTrace_902191 : CollatzResearch.WordTrace tailWord_902191 prefixEnd_902191 463257625160584907263405 := by
  unfold tailWord_902191
  simp only [CollatzResearch.WordTrace]
  refine ⟨32905609074523563800818427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21937072716349042533878951 32905609074523563800818427)
  ·
    refine ⟨49358413611785345701227641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32905609074523563800818427 49358413611785345701227641)
    ·
      refine ⟨37018810208839009275920731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49358413611785345701227641 37018810208839009275920731)
      ·
        refine ⟨55528215313258513913881097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37018810208839009275920731 55528215313258513913881097)
        ·
          refine ⟨41646161484943885435410823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55528215313258513913881097 41646161484943885435410823)
          ·
            refine ⟨62469242227415828153116235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41646161484943885435410823 62469242227415828153116235)
            ·
              refine ⟨93703863341123742229674353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62469242227415828153116235 93703863341123742229674353)
              ·
                refine ⟨70277897505842806672255765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93703863341123742229674353 70277897505842806672255765)
                ·
                  refine ⟨3294276445586381562761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70277897505842806672255765 3294276445586381562761989)
                  ·
                    refine ⟨617676833547446543017873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294276445586381562761989 617676833547446543017873)
                    ·
                      refine ⟨463257625160584907263405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617676833547446543017873 463257625160584907263405)
                      ·
                        rfl

theorem cell23_902191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 4, 2].length) (baseStart_902191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902191 prefixEnd_902191 := by exact prefixLift 902191
  have htrace : WordTrace (prefixWord ++ tailWord_902191) baseStart_902191 baseEnd_902191 := by
    simpa [prefixWord, tailWord_902191, baseEnd_902191] using wordTrace_append hprefix tailTrace_902191
  have hstable : (prefixWord ++ tailWord_902191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902191).length < 2 ^ (prefixWord ++ tailWord_902191).sum := by decide
  have hdescent : baseEnd_902191 < baseStart_902191 := by decide
  rcases family_descends (prefixWord ++ tailWord_902191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902228 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_902228 : Nat := 118140960795 + 902228 * 2 ^ 59
def prefixEnd_902228 : Nat := 4983230072969 + 3 ^ 40 * 902228 * 2
def baseEnd_902228 : Nat := 463276623944801262500735

theorem tailTrace_902228 : CollatzResearch.WordTrace tailWord_902228 prefixEnd_902228 463276623944801262500735 := by
  unfold tailWord_902228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453479287694759559957669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21937972383593012746610225 16453479287694759559957669)
  ·
    refine ⟨3085027366442767417492063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16453479287694759559957669 3085027366442767417492063)
    ·
      refine ⟨4627541049664151126238095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085027366442767417492063 4627541049664151126238095)
      ·
        refine ⟨6941311574496226689357143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627541049664151126238095 6941311574496226689357143)
        ·
          refine ⟨10411967361744340034035715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941311574496226689357143 10411967361744340034035715)
          ·
            refine ⟨15617951042616510051053573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411967361744340034035715 15617951042616510051053573)
            ·
              refine ⟨2928365820490595634572545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15617951042616510051053573 2928365820490595634572545)
              ·
                refine ⟨2196274365367946725929409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928365820490595634572545 2196274365367946725929409)
                ·
                  refine ⟨1647205774025960044447057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2196274365367946725929409 1647205774025960044447057)
                  ·
                    refine ⟨1235404330519470033335293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1647205774025960044447057 1235404330519470033335293)
                    ·
                      refine ⟨463276623944801262500735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1235404330519470033335293 463276623944801262500735)
                      ·
                        rfl

theorem cell23_902228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_902228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902228 prefixEnd_902228 := by exact prefixLift 902228
  have htrace : WordTrace (prefixWord ++ tailWord_902228) baseStart_902228 baseEnd_902228 := by
    simpa [prefixWord, tailWord_902228, baseEnd_902228] using wordTrace_append hprefix tailTrace_902228
  have hstable : (prefixWord ++ tailWord_902228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902228).length < 2 ^ (prefixWord ++ tailWord_902228).sum := by decide
  have hdescent : baseEnd_902228 < baseStart_902228 := by decide
  rcases family_descends (prefixWord ++ tailWord_902228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902268 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_902268 : Nat := 118140960795 + 902268 * 2 ^ 59
def prefixEnd_902268 : Nat := 4983230072969 + 3 ^ 40 * 902268 * 2
def baseEnd_902268 : Nat := 463297163170981106000551

theorem tailTrace_902268 : CollatzResearch.WordTrace tailWord_902268 prefixEnd_902268 463297163170981106000551 := by
  unfold tailWord_902268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16454208747622302975685729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21938944996829737300914305 16454208747622302975685729)
  ·
    refine ⟨12340656560716727231764297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16454208747622302975685729 12340656560716727231764297)
    ·
      refine ⟨9255492420537545423823223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12340656560716727231764297 9255492420537545423823223)
      ·
        refine ⟨13883238630806318135734835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255492420537545423823223 13883238630806318135734835)
        ·
          refine ⟨20824857946209477203602253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13883238630806318135734835 20824857946209477203602253)
          ·
            refine ⟨7809321729828553951350845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20824857946209477203602253 7809321729828553951350845)
            ·
              refine ⟨2928495648685707731756567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7809321729828553951350845 2928495648685707731756567)
              ·
                refine ⟨4392743473028561597634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928495648685707731756567 4392743473028561597634851)
                ·
                  refine ⟨6589115209542842396452277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392743473028561597634851 6589115209542842396452277)
                  ·
                    refine ⟨617729550894641474667401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6589115209542842396452277 617729550894641474667401)
                    ·
                      refine ⟨463297163170981106000551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617729550894641474667401 463297163170981106000551)
                      ·
                        rfl

theorem cell23_902268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_902268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902268 prefixEnd_902268 := by exact prefixLift 902268
  have htrace : WordTrace (prefixWord ++ tailWord_902268) baseStart_902268 baseEnd_902268 := by
    simpa [prefixWord, tailWord_902268, baseEnd_902268] using wordTrace_append hprefix tailTrace_902268
  have hstable : (prefixWord ++ tailWord_902268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902268).length < 2 ^ (prefixWord ++ tailWord_902268).sum := by decide
  have hdescent : baseEnd_902268 < baseStart_902268 := by decide
  rcases family_descends (prefixWord ++ tailWord_902268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902308 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_902308 : Nat := 118140960795 + 902308 * 2 ^ 59
def prefixEnd_902308 : Nat := 4983230072969 + 3 ^ 40 * 902308 * 2
def baseEnd_902308 : Nat := 154439234132386983166789

theorem tailTrace_902308 : CollatzResearch.WordTrace tailWord_902308 prefixEnd_902308 154439234132386983166789 := by
  unfold tailWord_902308
  simp only [CollatzResearch.WordTrace]
  refine ⟨16454938207549846391413789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21939917610066461855218385 16454938207549846391413789)
  ·
    refine ⟨6170601827831192396780171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16454938207549846391413789 6170601827831192396780171)
    ·
      refine ⟨9255902741746788595170257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170601827831192396780171 9255902741746788595170257)
      ·
        refine ⟨6941927056310091446377693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9255902741746788595170257 6941927056310091446377693)
        ·
          refine ⟨2603222646116284292391635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6941927056310091446377693 2603222646116284292391635)
          ·
            refine ⟨3904833969174426438587453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603222646116284292391635 3904833969174426438587453)
            ·
              refine ⟨1464312738440409914470295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904833969174426438587453 1464312738440409914470295)
              ·
                refine ⟨2196469107660614871705443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464312738440409914470295 2196469107660614871705443)
                ·
                  refine ⟨3294703661490922307558165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196469107660614871705443 3294703661490922307558165)
                  ·
                    refine ⟨154439234132386983166789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3294703661490922307558165 154439234132386983166789)
                    ·
                      rfl

theorem cell23_902308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_902308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902308 prefixEnd_902308 := by exact prefixLift 902308
  have htrace : WordTrace (prefixWord ++ tailWord_902308) baseStart_902308 baseEnd_902308 := by
    simpa [prefixWord, tailWord_902308, baseEnd_902308] using wordTrace_append hprefix tailTrace_902308
  have hstable : (prefixWord ++ tailWord_902308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902308).length < 2 ^ (prefixWord ++ tailWord_902308).sum := by decide
  have hdescent : baseEnd_902308 < baseStart_902308 := by decide
  rcases family_descends (prefixWord ++ tailWord_902308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902458 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_902458 : Nat := 118140960795 + 902458 * 2 ^ 59
def prefixEnd_902458 : Nat := 4983230072969 + 3 ^ 40 * 902458 * 2
def baseEnd_902458 : Nat := 154464908165111787541559

theorem tailTrace_902458 : CollatzResearch.WordTrace tailWord_902458 prefixEnd_902458 154464908165111787541559 := by
  unfold tailWord_902458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8228836841139067100197007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21943564909704178933858685 8228836841139067100197007)
  ·
    refine ⟨12343255261708600650295511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8228836841139067100197007 12343255261708600650295511)
    ·
      refine ⟨18514882892562900975443267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12343255261708600650295511 18514882892562900975443267)
      ·
        refine ⟨27772324338844351463164901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18514882892562900975443267 27772324338844351463164901)
        ·
          refine ⟨5207310813533315899343419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27772324338844351463164901 5207310813533315899343419)
          ·
            refine ⟨7810966220299973849015129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207310813533315899343419 7810966220299973849015129)
            ·
              refine ⟨5858224665224980386761347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7810966220299973849015129 5858224665224980386761347)
              ·
                refine ⟨8787336997837470580142021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858224665224980386761347 8787336997837470580142021)
                ·
                  refine ⟨1647625687094525733776629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8787336997837470580142021 1647625687094525733776629)
                  ·
                    refine ⟨154464908165111787541559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1647625687094525733776629 154464908165111787541559)
                    ·
                      rfl

theorem cell23_902458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_902458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902458 prefixEnd_902458 := by exact prefixLift 902458
  have htrace : WordTrace (prefixWord ++ tailWord_902458) baseStart_902458 baseEnd_902458 := by
    simpa [prefixWord, tailWord_902458, baseEnd_902458] using wordTrace_append hprefix tailTrace_902458
  have hstable : (prefixWord ++ tailWord_902458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902458).length < 2 ^ (prefixWord ++ tailWord_902458).sum := by decide
  have hdescent : baseEnd_902458 < baseStart_902458 := by decide
  rcases family_descends (prefixWord ++ tailWord_902458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902478 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_902478 : Nat := 118140960795 + 902478 * 2 ^ 59
def prefixEnd_902478 : Nat := 4983230072969 + 3 ^ 40 * 902478 * 2
def baseEnd_902478 : Nat := 463404994108425284374585

theorem tailTrace_902478 : CollatzResearch.WordTrace tailWord_902478 prefixEnd_902478 463404994108425284374585 := by
  unfold tailWord_902478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114509603060476477064511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21944051216322541211010725 4114509603060476477064511)
  ·
    refine ⟨6171764404590714715596767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114509603060476477064511 6171764404590714715596767)
    ·
      refine ⟨9257646606886072073395151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171764404590714715596767 9257646606886072073395151)
      ·
        refine ⟨13886469910329108110092727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257646606886072073395151 13886469910329108110092727)
        ·
          refine ⟨20829704865493662165139091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886469910329108110092727 20829704865493662165139091)
          ·
            refine ⟨31244557298240493247708637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829704865493662165139091 31244557298240493247708637)
            ·
              refine ⟨11716708986840184967890739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31244557298240493247708637 11716708986840184967890739)
              ·
                refine ⟨17575063480260277451836109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11716708986840184967890739 17575063480260277451836109)
                ·
                  refine ⟨6590648805097604044438541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17575063480260277451836109 6590648805097604044438541)
                  ·
                    refine ⟨2471493301911601516664453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6590648805097604044438541 2471493301911601516664453)
                    ·
                      refine ⟨463404994108425284374585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2471493301911601516664453 463404994108425284374585)
                      ·
                        rfl

theorem cell23_902478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_902478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902478 prefixEnd_902478 := by exact prefixLift 902478
  have htrace : WordTrace (prefixWord ++ tailWord_902478) baseStart_902478 baseEnd_902478 := by
    simpa [prefixWord, tailWord_902478, baseEnd_902478] using wordTrace_append hprefix tailTrace_902478
  have hstable : (prefixWord ++ tailWord_902478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902478).length < 2 ^ (prefixWord ++ tailWord_902478).sum := by decide
  have hdescent : baseEnd_902478 < baseStart_902478 := by decide
  rcases family_descends (prefixWord ++ tailWord_902478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902535 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 6]
def baseStart_902535 : Nat := 118140960795 + 902535 * 2 ^ 59
def prefixEnd_902535 : Nat := 4983230072969 + 3 ^ 40 * 902535 * 2
def baseEnd_902535 : Nat := 51492695833970173484647

theorem tailTrace_902535 : CollatzResearch.WordTrace tailWord_902535 prefixEnd_902535 51492695833970173484647 := by
  unfold tailWord_902535
  simp only [CollatzResearch.WordTrace]
  refine ⟨32918155785277310551341059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21945437190184873700894039 32918155785277310551341059)
  ·
    refine ⟨49377233677915965827011589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32918155785277310551341059 49377233677915965827011589)
    ·
      refine ⟨9258231314609243592564673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49377233677915965827011589 9258231314609243592564673)
      ·
        refine ⟨6943673485956932694423505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9258231314609243592564673 6943673485956932694423505)
        ·
          refine ⟨5207755114467699520817629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6943673485956932694423505 5207755114467699520817629)
          ·
            refine ⟨1952908167925387320306611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5207755114467699520817629 1952908167925387320306611)
            ·
              refine ⟨2929362251888080980459917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952908167925387320306611 2929362251888080980459917)
              ·
                refine ⟨1098510844458030367672469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2929362251888080980459917 1098510844458030367672469)
                ·
                  refine ⟨51492695833970173484647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1098510844458030367672469 51492695833970173484647)
                  ·
                    rfl

theorem cell23_902535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 6].length) (baseStart_902535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902535 prefixEnd_902535 := by exact prefixLift 902535
  have htrace : WordTrace (prefixWord ++ tailWord_902535) baseStart_902535 baseEnd_902535 := by
    simpa [prefixWord, tailWord_902535, baseEnd_902535] using wordTrace_append hprefix tailTrace_902535
  have hstable : (prefixWord ++ tailWord_902535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902535).length < 2 ^ (prefixWord ++ tailWord_902535).sum := by decide
  have hdescent : baseEnd_902535 < baseStart_902535 := by decide
  rcases family_descends (prefixWord ++ tailWord_902535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902572 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_902572 : Nat := 118140960795 + 902572 * 2 ^ 59
def prefixEnd_902572 : Nat := 4983230072969 + 3 ^ 40 * 902572 * 2
def baseEnd_902572 : Nat := 463453261289947916599153

theorem tailTrace_902572 : CollatzResearch.WordTrace tailWord_902572 prefixEnd_902572 463453261289947916599153 := by
  unfold tailWord_902572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16459752643071632935218985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21946336857428843913625313 16459752643071632935218985)
  ·
    refine ⟨12344814482303724701414239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16459752643071632935218985 12344814482303724701414239)
    ·
      refine ⟨18517221723455587052121359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12344814482303724701414239 18517221723455587052121359)
      ·
        refine ⟨27775832585183380578182039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18517221723455587052121359 27775832585183380578182039)
        ·
          refine ⟨41663748877775070867273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27775832585183380578182039 41663748877775070867273059)
          ·
            refine ⟨62495623316662606300909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41663748877775070867273059 62495623316662606300909589)
            ·
              refine ⟨2929482342968559670355137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62495623316662606300909589 2929482342968559670355137)
              ·
                refine ⟨2197111757226419752766353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929482342968559670355137 2197111757226419752766353)
                ·
                  refine ⟨1647833817919814814574765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197111757226419752766353 1647833817919814814574765)
                  ·
                    refine ⟨617937681719930555465537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1647833817919814814574765 617937681719930555465537)
                    ·
                      refine ⟨463453261289947916599153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 617937681719930555465537 463453261289947916599153)
                      ·
                        rfl

theorem cell23_902572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_902572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902572 prefixEnd_902572 := by exact prefixLift 902572
  have htrace : WordTrace (prefixWord ++ tailWord_902572) baseStart_902572 baseEnd_902572 := by
    simpa [prefixWord, tailWord_902572, baseEnd_902572] using wordTrace_append hprefix tailTrace_902572
  have hstable : (prefixWord ++ tailWord_902572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902572).length < 2 ^ (prefixWord ++ tailWord_902572).sum := by decide
  have hdescent : baseEnd_902572 < baseStart_902572 := by decide
  rcases family_descends (prefixWord ++ tailWord_902572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902573 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_902573 : Nat := 118140960795 + 902573 * 2 ^ 59
def prefixEnd_902573 : Nat := 4983230072969 + 3 ^ 40 * 902573 * 2
def baseEnd_902573 : Nat := 154484591590200804228883

theorem tailTrace_902573 : CollatzResearch.WordTrace tailWord_902573 prefixEnd_902573 154484591590200804228883 := by
  unfold tailWord_902573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32919541759139643041224373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21946361172759762027482915 32919541759139643041224373)
  ·
    refine ⟨3086207039919341535114785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32919541759139643041224373 3086207039919341535114785)
    ·
      refine ⟨2314655279939506151336089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3086207039919341535114785 2314655279939506151336089)
      ·
        refine ⟨1735991459954629613502067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2314655279939506151336089 1735991459954629613502067)
        ·
          refine ⟨2603987189931944420253101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735991459954629613502067 2603987189931944420253101)
          ·
            refine ⟨976495196224479157594913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2603987189931944420253101 976495196224479157594913)
            ·
              refine ⟨732371397168359368196185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976495196224479157594913 732371397168359368196185)
              ·
                refine ⟨549278547876269526147139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732371397168359368196185 549278547876269526147139)
                ·
                  refine ⟨823917821814404289220709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549278547876269526147139 823917821814404289220709)
                  ·
                    refine ⟨154484591590200804228883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823917821814404289220709 154484591590200804228883)
                    ·
                      rfl

theorem cell23_902573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_902573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902573 prefixEnd_902573 := by exact prefixLift 902573
  have htrace : WordTrace (prefixWord ++ tailWord_902573) baseStart_902573 baseEnd_902573 := by
    simpa [prefixWord, tailWord_902573, baseEnd_902573] using wordTrace_append hprefix tailTrace_902573
  have hstable : (prefixWord ++ tailWord_902573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902573).length < 2 ^ (prefixWord ++ tailWord_902573).sum := by decide
  have hdescent : baseEnd_902573 < baseStart_902573 := by decide
  rcases family_descends (prefixWord ++ tailWord_902573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902629 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_902629 : Nat := 118140960795 + 902629 * 2 ^ 59
def prefixEnd_902629 : Nat := 4983230072969 + 3 ^ 40 * 902629 * 2
def baseEnd_902629 : Nat := 154494176562418064528797

theorem tailTrace_902629 : CollatzResearch.WordTrace tailWord_902629 prefixEnd_902629 154494176562418064528797 := by
  unfold tailWord_902629
  simp only [CollatzResearch.WordTrace]
  refine ⟨32921584246936764605262941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21947722831291176403508627 32921584246936764605262941)
  ·
    refine ⟨12345594092601286726973603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32921584246936764605262941 12345594092601286726973603)
    ·
      refine ⟨18518391138901930090460405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12345594092601286726973603 18518391138901930090460405)
      ·
        refine ⟨1736099169272055945980663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18518391138901930090460405 1736099169272055945980663)
        ·
          refine ⟨2604148753908083918970995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736099169272055945980663 2604148753908083918970995)
          ·
            refine ⟨3906223130862125878456493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604148753908083918970995 3906223130862125878456493)
            ·
              refine ⟨1464833674073297204421185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3906223130862125878456493 1464833674073297204421185)
              ·
                refine ⟨1098625255554972903315889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464833674073297204421185 1098625255554972903315889)
                ·
                  refine ⟨823968941666229677486917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098625255554972903315889 823968941666229677486917)
                  ·
                    refine ⟨154494176562418064528797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823968941666229677486917 154494176562418064528797)
                    ·
                      rfl

theorem cell23_902629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_902629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902629 prefixEnd_902629 := by exact prefixLift 902629
  have htrace : WordTrace (prefixWord ++ tailWord_902629) baseStart_902629 baseEnd_902629 := by
    simpa [prefixWord, tailWord_902629, baseEnd_902629] using wordTrace_append hprefix tailTrace_902629
  have hstable : (prefixWord ++ tailWord_902629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902629).length < 2 ^ (prefixWord ++ tailWord_902629).sum := by decide
  have hdescent : baseEnd_902629 < baseStart_902629 := by decide
  rcases family_descends (prefixWord ++ tailWord_902629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902646 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_902646 : Nat := 118140960795 + 902646 * 2 ^ 59
def prefixEnd_902646 : Nat := 4983230072969 + 3 ^ 40 * 902646 * 2
def baseEnd_902646 : Nat := 154497086286126875691271

theorem tailTrace_902646 : CollatzResearch.WordTrace tailWord_902646 prefixEnd_902646 154497086286126875691271 := by
  unfold tailWord_902646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057637767992198531789487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21948136191916784339087861 2057637767992198531789487)
  ·
    refine ⟨3086456651988297797684231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057637767992198531789487 3086456651988297797684231)
    ·
      refine ⟨4629684977982446696526347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3086456651988297797684231 4629684977982446696526347)
      ·
        refine ⟨6944527466973670044789521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629684977982446696526347 6944527466973670044789521)
        ·
          refine ⟨5208395600230252533592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6944527466973670044789521 5208395600230252533592141)
          ·
            refine ⟨1953148350086344700097053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5208395600230252533592141 1953148350086344700097053)
            ·
              refine ⟨732430631282379262536395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953148350086344700097053 732430631282379262536395)
              ·
                refine ⟨1098645946923568893804593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732430631282379262536395 1098645946923568893804593)
                ·
                  refine ⟨823984460192676670353445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098645946923568893804593 823984460192676670353445)
                  ·
                    refine ⟨154497086286126875691271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 823984460192676670353445 154497086286126875691271)
                    ·
                      rfl

theorem cell23_902646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_902646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902646 prefixEnd_902646 := by exact prefixLift 902646
  have htrace : WordTrace (prefixWord ++ tailWord_902646) baseStart_902646 baseEnd_902646 := by
    simpa [prefixWord, tailWord_902646, baseEnd_902646] using wordTrace_append hprefix tailTrace_902646
  have hstable : (prefixWord ++ tailWord_902646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902646).length < 2 ^ (prefixWord ++ tailWord_902646).sum := by decide
  have hdescent : baseEnd_902646 < baseStart_902646 := by decide
  rcases family_descends (prefixWord ++ tailWord_902646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902652 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_902652 : Nat := 118140960795 + 902652 * 2 ^ 59
def prefixEnd_902652 : Nat := 4983230072969 + 3 ^ 40 * 902652 * 2
def baseEnd_902652 : Nat := 463494339742307603598785

theorem tailTrace_902652 : CollatzResearch.WordTrace tailWord_902652 prefixEnd_902652 463494339742307603598785 := by
  unfold tailWord_902652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461211562926719766675105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21948282083902293022233473 16461211562926719766675105)
  ·
    refine ⟨12345908672195039825006329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16461211562926719766675105 12345908672195039825006329)
    ·
      refine ⟨9259431504146279868754747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12345908672195039825006329 9259431504146279868754747)
      ·
        refine ⟨13889147256219419803132121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9259431504146279868754747 13889147256219419803132121)
        ·
          refine ⟨10416860442164564852349091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13889147256219419803132121 10416860442164564852349091)
          ·
            refine ⟨15625290663246847278523637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10416860442164564852349091 15625290663246847278523637)
            ·
              refine ⟨1464870999679391932361591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15625290663246847278523637 1464870999679391932361591)
              ·
                refine ⟨2197306499519087898542387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464870999679391932361591 2197306499519087898542387)
                ·
                  refine ⟨3295959749278631847813581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197306499519087898542387 3295959749278631847813581)
                  ·
                    refine ⟨1235984905979486942930093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3295959749278631847813581 1235984905979486942930093)
                    ·
                      refine ⟨463494339742307603598785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1235984905979486942930093 463494339742307603598785)
                      ·
                        rfl

theorem cell23_902652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_902652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902652 prefixEnd_902652 := by exact prefixLift 902652
  have htrace : WordTrace (prefixWord ++ tailWord_902652) baseStart_902652 baseEnd_902652 := by
    simpa [prefixWord, tailWord_902652, baseEnd_902652] using wordTrace_append hprefix tailTrace_902652
  have hstable : (prefixWord ++ tailWord_902652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902652).length < 2 ^ (prefixWord ++ tailWord_902652).sum := by decide
  have hdescent : baseEnd_902652 < baseStart_902652 := by decide
  rcases family_descends (prefixWord ++ tailWord_902652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902670 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_902670 : Nat := 118140960795 + 902670 * 2 ^ 59
def prefixEnd_902670 : Nat := 4983230072969 + 3 ^ 40 * 902670 * 2
def baseEnd_902670 : Nat := 463503582394088533173703

theorem tailTrace_902670 : CollatzResearch.WordTrace tailWord_902670 prefixEnd_902670 463503582394088533173703 := by
  unfold tailWord_902670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115384954973528575938183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21948719759858819071670309 4115384954973528575938183)
  ·
    refine ⟨6173077432460292863907275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4115384954973528575938183 6173077432460292863907275)
    ·
      refine ⟨9259616148690439295860913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173077432460292863907275 9259616148690439295860913)
      ·
        refine ⟨6944712111517829471895685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9259616148690439295860913 6944712111517829471895685)
        ·
          refine ⟨1302133520909593025980441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6944712111517829471895685 1302133520909593025980441)
          ·
            refine ⟨976600140682194769485331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302133520909593025980441 976600140682194769485331)
            ·
              refine ⟨1464900211023292154227997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976600140682194769485331 1464900211023292154227997)
              ·
                refine ⟨549337579133734557835499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464900211023292154227997 549337579133734557835499)
                ·
                  refine ⟨824006368700601836753249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549337579133734557835499 824006368700601836753249)
                  ·
                    refine ⟨618004776525451377564937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824006368700601836753249 618004776525451377564937)
                    ·
                      refine ⟨463503582394088533173703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618004776525451377564937 463503582394088533173703)
                      ·
                        rfl

theorem cell23_902670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_902670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902670 prefixEnd_902670 := by exact prefixLift 902670
  have htrace : WordTrace (prefixWord ++ tailWord_902670) baseStart_902670 baseEnd_902670 := by
    simpa [prefixWord, tailWord_902670, baseEnd_902670] using wordTrace_append hprefix tailTrace_902670
  have hstable : (prefixWord ++ tailWord_902670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902670).length < 2 ^ (prefixWord ++ tailWord_902670).sum := by decide
  have hdescent : baseEnd_902670 < baseStart_902670 := by decide
  rcases family_descends (prefixWord ++ tailWord_902670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902705 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_902705 : Nat := 118140960795 + 902705 * 2 ^ 59
def prefixEnd_902705 : Nat := 4983230072969 + 3 ^ 40 * 902705 * 2
def baseEnd_902705 : Nat := 463521554216995896236041

theorem tailTrace_902705 : CollatzResearch.WordTrace tailWord_902705 prefixEnd_902705 463521554216995896236041 := by
  unfold tailWord_902705
  simp only [CollatzResearch.WordTrace]
  refine ⟨32924356194661429585029569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21949570796440953056686379 32924356194661429585029569)
  ·
    refine ⟨24693267145996072188772177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32924356194661429585029569 24693267145996072188772177)
    ·
      refine ⟨18519950359497054141579133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24693267145996072188772177 18519950359497054141579133)
      ·
        refine ⟨6944981384811395303092175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18519950359497054141579133 6944981384811395303092175)
        ·
          refine ⟨10417472077217092954638263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944981384811395303092175 10417472077217092954638263)
          ·
            refine ⟨15626208115825639431957395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10417472077217092954638263 15626208115825639431957395)
            ·
              refine ⟨23439312173738459147936093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15626208115825639431957395 23439312173738459147936093)
              ·
                refine ⟨8789742065151922180476035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23439312173738459147936093 8789742065151922180476035)
                ·
                  refine ⟨13184613097727883270714053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789742065151922180476035 13184613097727883270714053)
                  ·
                    refine ⟨2472114955823978113258885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13184613097727883270714053 2472114955823978113258885)
                    ·
                      refine ⟨463521554216995896236041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2472114955823978113258885 463521554216995896236041)
                      ·
                        rfl

theorem cell23_902705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_902705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902705 prefixEnd_902705 := by exact prefixLift 902705
  have htrace : WordTrace (prefixWord ++ tailWord_902705) baseStart_902705 baseEnd_902705 := by
    simpa [prefixWord, tailWord_902705, baseEnd_902705] using wordTrace_append hprefix tailTrace_902705
  have hstable : (prefixWord ++ tailWord_902705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902705).length < 2 ^ (prefixWord ++ tailWord_902705).sum := by decide
  have hdescent : baseEnd_902705 < baseStart_902705 := by decide
  rcases family_descends (prefixWord ++ tailWord_902705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902795 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_902795 : Nat := 118140960795 + 902795 * 2 ^ 59
def prefixEnd_902795 : Nat := 4983230072969 + 3 ^ 40 * 902795 * 2
def baseEnd_902795 : Nat := 463567767475900544110627

theorem tailTrace_902795 : CollatzResearch.WordTrace tailWord_902795 prefixEnd_902795 463567767475900544110627 := by
  unfold tailWord_902795
  simp only [CollatzResearch.WordTrace]
  refine ⟨32927638764335374955805839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21951759176223583303870559 32927638764335374955805839)
  ·
    refine ⟨49391458146503062433708759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32927638764335374955805839 49391458146503062433708759)
    ·
      refine ⟨74087187219754593650563139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49391458146503062433708759 74087187219754593650563139)
      ·
        refine ⟨111130780829631890475844709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74087187219754593650563139 111130780829631890475844709)
        ·
          refine ⟨20837021405555979464220883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111130780829631890475844709 20837021405555979464220883)
          ·
            refine ⟨31255532108333969196331325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837021405555979464220883 31255532108333969196331325)
            ·
              refine ⟨11720824540625238448624247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31255532108333969196331325 11720824540625238448624247)
              ·
                refine ⟨17581236810937857672936371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11720824540625238448624247 17581236810937857672936371)
                ·
                  refine ⟨26371855216406786509404557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17581236810937857672936371 26371855216406786509404557)
                  ·
                    refine ⟨9889445706152544941026709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26371855216406786509404557 9889445706152544941026709)
                    ·
                      refine ⟨463567767475900544110627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9889445706152544941026709 463567767475900544110627)
                      ·
                        rfl

theorem cell23_902795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_902795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902795 prefixEnd_902795 := by exact prefixLift 902795
  have htrace : WordTrace (prefixWord ++ tailWord_902795) baseStart_902795 baseEnd_902795 := by
    simpa [prefixWord, tailWord_902795, baseEnd_902795] using wordTrace_append hprefix tailTrace_902795
  have hstable : (prefixWord ++ tailWord_902795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902795).length < 2 ^ (prefixWord ++ tailWord_902795).sum := by decide
  have hdescent : baseEnd_902795 < baseStart_902795 := by decide
  rcases family_descends (prefixWord ++ tailWord_902795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902825 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_902825 : Nat := 118140960795 + 902825 * 2 ^ 59
def prefixEnd_902825 : Nat := 4983230072969 + 3 ^ 40 * 902825 * 2
def baseEnd_902825 : Nat := 463583171895535426735489

theorem tailTrace_902825 : CollatzResearch.WordTrace tailWord_902825 prefixEnd_902825 463583171895535426735489 := by
  unfold tailWord_902825
  simp only [CollatzResearch.WordTrace]
  refine ⟨32928732954226690079397929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21952488636151126719598619 32928732954226690079397929)
  ·
    refine ⟨24696549715670017559548447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32928732954226690079397929 24696549715670017559548447)
    ·
      refine ⟨37044824573505026339322671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24696549715670017559548447 37044824573505026339322671)
      ·
        refine ⟨55567236860257539508984007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37044824573505026339322671 55567236860257539508984007)
        ·
          refine ⟨83350855290386309263476011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55567236860257539508984007 83350855290386309263476011)
          ·
            refine ⟨125026282935579463895214017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83350855290386309263476011 125026282935579463895214017)
            ·
              refine ⟨93769712201684597921410513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125026282935579463895214017 93769712201684597921410513)
              ·
                refine ⟨70327284151263448441057885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93769712201684597921410513 70327284151263448441057885)
                ·
                  refine ⟨26372731556723793165396707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70327284151263448441057885 26372731556723793165396707)
                  ·
                    refine ⟨39559097335085689748095061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26372731556723793165396707 39559097335085689748095061)
                    ·
                      refine ⟨463583171895535426735489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 39559097335085689748095061 463583171895535426735489)
                      ·
                        rfl

theorem cell23_902825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_902825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902825 prefixEnd_902825 := by exact prefixLift 902825
  have htrace : WordTrace (prefixWord ++ tailWord_902825) baseStart_902825 baseEnd_902825 := by
    simpa [prefixWord, tailWord_902825, baseEnd_902825] using wordTrace_append hprefix tailTrace_902825
  have hstable : (prefixWord ++ tailWord_902825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902825).length < 2 ^ (prefixWord ++ tailWord_902825).sum := by decide
  have hdescent : baseEnd_902825 < baseStart_902825 := by decide
  rcases family_descends (prefixWord ++ tailWord_902825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902850 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_902850 : Nat := 118140960795 + 902850 * 2 ^ 59
def prefixEnd_902850 : Nat := 4983230072969 + 3 ^ 40 * 902850 * 2
def baseEnd_902850 : Nat := 463596008911897828922875

theorem tailTrace_902850 : CollatzResearch.WordTrace tailWord_902850 prefixEnd_902850 463596008911897828922875 := by
  unfold tailWord_902850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232411194784029837264501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21953096519424079566038669 8232411194784029837264501)
  ·
    refine ⟨771788549511002797243547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8232411194784029837264501 771788549511002797243547)
    ·
      refine ⟨1157682824266504195865321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771788549511002797243547 1157682824266504195865321)
      ·
        refine ⟨868262118199878146898991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157682824266504195865321 868262118199878146898991)
        ·
          refine ⟨1302393177299817220348487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868262118199878146898991 1302393177299817220348487)
          ·
            refine ⟨1953589765949725830522731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302393177299817220348487 1953589765949725830522731)
            ·
              refine ⟨2930384648924588745784097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953589765949725830522731 2930384648924588745784097)
              ·
                refine ⟨2197788486693441559338073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930384648924588745784097 2197788486693441559338073)
                ·
                  refine ⟨1648341365020081169503555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197788486693441559338073 1648341365020081169503555)
                  ·
                    refine ⟨2472512047530121754255333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1648341365020081169503555 2472512047530121754255333)
                    ·
                      refine ⟨463596008911897828922875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2472512047530121754255333 463596008911897828922875)
                      ·
                        rfl

theorem cell23_902850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_902850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902850 prefixEnd_902850 := by exact prefixLift 902850
  have htrace : WordTrace (prefixWord ++ tailWord_902850) baseStart_902850 baseEnd_902850 := by
    simpa [prefixWord, tailWord_902850, baseEnd_902850] using wordTrace_append hprefix tailTrace_902850
  have hstable : (prefixWord ++ tailWord_902850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902850).length < 2 ^ (prefixWord ++ tailWord_902850).sum := by decide
  have hdescent : baseEnd_902850 < baseStart_902850 := by decide
  rcases family_descends (prefixWord ++ tailWord_902850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902860 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_902860 : Nat := 118140960795 + 902860 * 2 ^ 59
def prefixEnd_902860 : Nat := 4983230072969 + 3 ^ 40 * 902860 * 2
def baseEnd_902860 : Nat := 154533714572814263265943

theorem tailTrace_902860 : CollatzResearch.WordTrace tailWord_902860 prefixEnd_902860 154533714572814263265943 := by
  unfold tailWord_902860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465004754549945528461017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21953339672733260704614689 16465004754549945528461017)
  ·
    refine ⟨12348753565912459146345763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16465004754549945528461017 12348753565912459146345763)
    ·
      refine ⟨18523130348868688719518645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348753565912459146345763 18523130348868688719518645)
      ·
        refine ⟨1736543470206439567454873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18523130348868688719518645 1736543470206439567454873)
        ·
          refine ⟨1302407602654829675591155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1736543470206439567454873 1302407602654829675591155)
          ·
            refine ⟨1953611403982244513386733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302407602654829675591155 1953611403982244513386733)
            ·
              refine ⟨732604276493341692520025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953611403982244513386733 732604276493341692520025)
              ·
                refine ⟨549453207370006269390019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732604276493341692520025 549453207370006269390019)
                ·
                  refine ⟨824179811055009404085029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549453207370006269390019 824179811055009404085029)
                  ·
                    refine ⟨154533714572814263265943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824179811055009404085029 154533714572814263265943)
                    ·
                      rfl

theorem cell23_902860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_902860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902860 prefixEnd_902860 := by exact prefixLift 902860
  have htrace : WordTrace (prefixWord ++ tailWord_902860) baseStart_902860 baseEnd_902860 := by
    simpa [prefixWord, tailWord_902860, baseEnd_902860] using wordTrace_append hprefix tailTrace_902860
  have hstable : (prefixWord ++ tailWord_902860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902860).length < 2 ^ (prefixWord ++ tailWord_902860).sum := by decide
  have hdescent : baseEnd_902860 < baseStart_902860 := by decide
  rcases family_descends (prefixWord ++ tailWord_902860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902892 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_902892 : Nat := 118140960795 + 902892 * 2 ^ 59
def prefixEnd_902892 : Nat := 4983230072969 + 3 ^ 40 * 902892 * 2
def baseEnd_902892 : Nat := 463617575099386664597681

theorem tailTrace_902892 : CollatzResearch.WordTrace tailWord_902892 prefixEnd_902892 463617575099386664597681 := by
  unfold tailWord_902892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16465588322491980261043465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21954117763322640348057953 16465588322491980261043465)
  ·
    refine ⟨12349191241868985195782599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16465588322491980261043465 12349191241868985195782599)
    ·
      refine ⟨18523786862803477793673899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12349191241868985195782599 18523786862803477793673899)
      ·
        refine ⟨27785680294205216690510849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523786862803477793673899 27785680294205216690510849)
        ·
          refine ⟨20839260220653912517883137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27785680294205216690510849 20839260220653912517883137)
          ·
            refine ⟨15629445165490434388412353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20839260220653912517883137 15629445165490434388412353)
            ·
              refine ⟨11722083874117825791309265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15629445165490434388412353 11722083874117825791309265)
              ·
                refine ⟨8791562905588369343481949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722083874117825791309265 8791562905588369343481949)
                ·
                  refine ⟨3296836089595638503805731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8791562905588369343481949 3296836089595638503805731)
                  ·
                    refine ⟨4945254134393457755708597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296836089595638503805731 4945254134393457755708597)
                    ·
                      refine ⟨463617575099386664597681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4945254134393457755708597 463617575099386664597681)
                      ·
                        rfl

theorem cell23_902892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_902892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902892 prefixEnd_902892 := by exact prefixLift 902892
  have htrace : WordTrace (prefixWord ++ tailWord_902892) baseStart_902892 baseEnd_902892 := by
    simpa [prefixWord, tailWord_902892, baseEnd_902892] using wordTrace_append hprefix tailTrace_902892
  have hstable : (prefixWord ++ tailWord_902892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902892).length < 2 ^ (prefixWord ++ tailWord_902892).sum := by decide
  have hdescent : baseEnd_902892 < baseStart_902892 := by decide
  rcases family_descends (prefixWord ++ tailWord_902892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902893 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_902893 : Nat := 118140960795 + 902893 * 2 ^ 59
def prefixEnd_902893 : Nat := 4983230072969 + 3 ^ 40 * 902893 * 2
def baseEnd_902893 : Nat := 463618088580041160685177

theorem tailTrace_902893 : CollatzResearch.WordTrace tailWord_902893 prefixEnd_902893 463618088580041160685177 := by
  unfold tailWord_902893
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931213117980337692873333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21954142078653558461915555 32931213117980337692873333)
  ·
    refine ⟨3087301229810656658706875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32931213117980337692873333 3087301229810656658706875)
    ·
      refine ⟨4630951844715984988060313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3087301229810656658706875 4630951844715984988060313)
      ·
        refine ⟨3473213883536988741045235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4630951844715984988060313 3473213883536988741045235)
        ·
          refine ⟨5209820825305483111567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473213883536988741045235 5209820825305483111567853)
          ·
            refine ⟨1953682809489556166837945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5209820825305483111567853 1953682809489556166837945)
            ·
              refine ⟨1465262107117167125128459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1953682809489556166837945 1465262107117167125128459)
              ·
                refine ⟨2197893160675750687692689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465262107117167125128459 2197893160675750687692689)
                ·
                  refine ⟨1648419870506813015769517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2197893160675750687692689 1648419870506813015769517)
                  ·
                    refine ⟨618157451440054880913569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1648419870506813015769517 618157451440054880913569)
                    ·
                      refine ⟨463618088580041160685177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618157451440054880913569 463618088580041160685177)
                      ·
                        rfl

theorem cell23_902893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_902893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902893 prefixEnd_902893 := by exact prefixLift 902893
  have htrace : WordTrace (prefixWord ++ tailWord_902893) baseStart_902893 baseEnd_902893 := by
    simpa [prefixWord, tailWord_902893, baseEnd_902893] using wordTrace_append hprefix tailTrace_902893
  have hstable : (prefixWord ++ tailWord_902893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902893).length < 2 ^ (prefixWord ++ tailWord_902893).sum := by decide
  have hdescent : baseEnd_902893 < baseStart_902893 := by decide
  rcases family_descends (prefixWord ++ tailWord_902893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902916 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_902916 : Nat := 118140960795 + 902916 * 2 ^ 59
def prefixEnd_902916 : Nat := 4983230072969 + 3 ^ 40 * 902916 * 2
def baseEnd_902916 : Nat := 154543299545031523565857

theorem tailTrace_902916 : CollatzResearch.WordTrace tailWord_902916 prefixEnd_902916 154543299545031523565857 := by
  unfold tailWord_902916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16466025998448506310480301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21954701331264675080640401 16466025998448506310480301)
  ·
    refine ⟨6174759749418189866430113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16466025998448506310480301 6174759749418189866430113)
    ·
      refine ⟨4631069812063642399822585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6174759749418189866430113 4631069812063642399822585)
      ·
        refine ⟨3473302359047731799866939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4631069812063642399822585 3473302359047731799866939)
        ·
          refine ⟨5209953538571597699800409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473302359047731799866939 5209953538571597699800409)
          ·
            refine ⟨3907465153928698274850307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209953538571597699800409 3907465153928698274850307)
            ·
              refine ⟨5861197730893047412275461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907465153928698274850307 5861197730893047412275461)
              ·
                refine ⟨1098974574542446389801649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5861197730893047412275461 1098974574542446389801649)
                ·
                  refine ⟨824230930906834792351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1098974574542446389801649 824230930906834792351237)
                  ·
                    refine ⟨154543299545031523565857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824230930906834792351237 154543299545031523565857)
                    ·
                      rfl

theorem cell23_902916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_902916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902916 prefixEnd_902916 := by exact prefixLift 902916
  have htrace : WordTrace (prefixWord ++ tailWord_902916) baseStart_902916 baseEnd_902916 := by
    simpa [prefixWord, tailWord_902916, baseEnd_902916] using wordTrace_append hprefix tailTrace_902916
  have hstable : (prefixWord ++ tailWord_902916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902916).length < 2 ^ (prefixWord ++ tailWord_902916).sum := by decide
  have hdescent : baseEnd_902916 < baseStart_902916 := by decide
  rcases family_descends (prefixWord ++ tailWord_902916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902973 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_902973 : Nat := 118140960795 + 902973 * 2 ^ 59
def prefixEnd_902973 : Nat := 4983230072969 + 3 ^ 40 * 902973 * 2
def baseEnd_902973 : Nat := 463659167032400847684809

theorem tailTrace_902973 : CollatzResearch.WordTrace tailWord_902973 prefixEnd_902973 463659167032400847684809 := by
  unfold tailWord_902973
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934130957690511355785573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21956087305127007570523715 32934130957690511355785573)
  ·
    refine ⟨6175149554566970879209795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32934130957690511355785573 6175149554566970879209795)
    ·
      refine ⟨9262724331850456318814693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175149554566970879209795 9262724331850456318814693)
      ·
        refine ⟨1736760812221960559777755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9262724331850456318814693 1736760812221960559777755)
        ·
          refine ⟨2605141218332940839666633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1736760812221960559777755 2605141218332940839666633)
          ·
            refine ⟨1953855913749705629749975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605141218332940839666633 1953855913749705629749975)
            ·
              refine ⟨2930783870624558444624963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953855913749705629749975 2930783870624558444624963)
              ·
                refine ⟨4396175805936837666937445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930783870624558444624963 4396175805936837666937445)
                ·
                  refine ⟨824282963613157062550771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4396175805936837666937445 824282963613157062550771)
                  ·
                    refine ⟨1236424445419735593826157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824282963613157062550771 1236424445419735593826157)
                    ·
                      refine ⟨463659167032400847684809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1236424445419735593826157 463659167032400847684809)
                      ·
                        rfl

theorem cell23_902973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_902973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_902973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_902973 prefixEnd_902973 := by exact prefixLift 902973
  have htrace : WordTrace (prefixWord ++ tailWord_902973) baseStart_902973 baseEnd_902973 := by
    simpa [prefixWord, tailWord_902973, baseEnd_902973] using wordTrace_append hprefix tailTrace_902973
  have hstable : (prefixWord ++ tailWord_902973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902973).length < 2 ^ (prefixWord ++ tailWord_902973).sum := by decide
  have hdescent : baseEnd_902973 < baseStart_902973 := by decide
  rcases family_descends (prefixWord ++ tailWord_902973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903029 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_903029 : Nat := 118140960795 + 903029 * 2 ^ 59
def prefixEnd_903029 : Nat := 4983230072969 + 3 ^ 40 * 903029 * 2
def baseEnd_903029 : Nat := 463687921949052628584551

theorem tailTrace_903029 : CollatzResearch.WordTrace tailWord_903029 prefixEnd_903029 463687921949052628584551 := by
  unfold tailWord_903029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936173445487632919824141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21957448963658421946549427 32936173445487632919824141)
  ·
    refine ⟨12351065042057862344934053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32936173445487632919824141 12351065042057862344934053)
    ·
      refine ⟨2315824695385849189675135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12351065042057862344934053 2315824695385849189675135)
      ·
        refine ⟨3473737043078773784512703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315824695385849189675135 3473737043078773784512703)
        ·
          refine ⟨5210605564618160676769055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473737043078773784512703 5210605564618160676769055)
          ·
            refine ⟨7815908346927241015153583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210605564618160676769055 7815908346927241015153583)
            ·
              refine ⟨11723862520390861522730375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815908346927241015153583 11723862520390861522730375)
              ·
                refine ⟨17585793780586292284095563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723862520390861522730375 17585793780586292284095563)
                ·
                  refine ⟨26378690670879438426143345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17585793780586292284095563 26378690670879438426143345)
                  ·
                    refine ⟨19784018003159578819607509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26378690670879438426143345 19784018003159578819607509)
                    ·
                      refine ⟨463687921949052628584551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 19784018003159578819607509 463687921949052628584551)
                      ·
                        rfl

theorem cell23_903029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_903029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903029 prefixEnd_903029 := by exact prefixLift 903029
  have htrace : WordTrace (prefixWord ++ tailWord_903029) baseStart_903029 baseEnd_903029 := by
    simpa [prefixWord, tailWord_903029, baseEnd_903029] using wordTrace_append hprefix tailTrace_903029
  have hstable : (prefixWord ++ tailWord_903029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903029).length < 2 ^ (prefixWord ++ tailWord_903029).sum := by decide
  have hdescent : baseEnd_903029 < baseStart_903029 := by decide
  rcases family_descends (prefixWord ++ tailWord_903029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903049 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_903049 : Nat := 118140960795 + 903049 * 2 ^ 59
def prefixEnd_903049 : Nat := 4983230072969 + 3 ^ 40 * 903049 * 2
def baseEnd_903049 : Nat := 154566063854047516778153

theorem tailTrace_903049 : CollatzResearch.WordTrace tailWord_903049 prefixEnd_903049 154566063854047516778153 := by
  unfold tailWord_903049
  simp only [CollatzResearch.WordTrace]
  refine ⟨32936902905415176335552201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21957935270276784223701467 32936902905415176335552201)
  ·
    refine ⟨24702677179061382251664151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32936902905415176335552201 24702677179061382251664151)
    ·
      refine ⟨37054015768592073377496227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24702677179061382251664151 37054015768592073377496227)
      ·
        refine ⟨55581023652888110066244341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37054015768592073377496227 55581023652888110066244341)
        ·
          refine ⟨5210720967458260318710407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55581023652888110066244341 5210720967458260318710407)
          ·
            refine ⟨7816081451187390478065611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210720967458260318710407 7816081451187390478065611)
            ·
              refine ⟨11724122176781085717098417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816081451187390478065611 11724122176781085717098417)
              ·
                refine ⟨8793091632585814287823813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11724122176781085717098417 8793091632585814287823813)
                ·
                  refine ⟨1648704681109840178966965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8793091632585814287823813 1648704681109840178966965)
                  ·
                    refine ⟨154566063854047516778153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1648704681109840178966965 154566063854047516778153)
                    ·
                      rfl

theorem cell23_903049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_903049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903049 prefixEnd_903049 := by exact prefixLift 903049
  have htrace : WordTrace (prefixWord ++ tailWord_903049) baseStart_903049 baseEnd_903049 := by
    simpa [prefixWord, tailWord_903049, baseEnd_903049] using wordTrace_append hprefix tailTrace_903049
  have hstable : (prefixWord ++ tailWord_903049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903049).length < 2 ^ (prefixWord ++ tailWord_903049).sum := by decide
  have hdescent : baseEnd_903049 < baseStart_903049 := by decide
  rcases family_descends (prefixWord ++ tailWord_903049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903066 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_903066 : Nat := 118140960795 + 903066 * 2 ^ 59
def prefixEnd_903066 : Nat := 4983230072969 + 3 ^ 40 * 903066 * 2
def baseEnd_903066 : Nat := 154568973577756327940627

theorem tailTrace_903066 : CollatzResearch.WordTrace tailWord_903066 prefixEnd_903066 154568973577756327940627 := by
  unfold tailWord_903066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234380736588397059730263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21958348630902392159280701 8234380736588397059730263)
  ·
    refine ⟨12351571104882595589595395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8234380736588397059730263 12351571104882595589595395)
    ·
      refine ⟨18527356657323893384393093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351571104882595589595395 18527356657323893384393093)
      ·
        refine ⟨3473879373248230009573705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18527356657323893384393093 3473879373248230009573705)
        ·
          refine ⟨2605409529936172507180279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473879373248230009573705 2605409529936172507180279)
          ·
            refine ⟨3908114294904258760770419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605409529936172507180279 3908114294904258760770419)
            ·
              refine ⟨5862171442356388141155629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908114294904258760770419 5862171442356388141155629)
              ·
                refine ⟨2198314290883645552933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862171442356388141155629 2198314290883645552933361)
                ·
                  refine ⟨1648735718162734164700021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2198314290883645552933361 1648735718162734164700021)
                  ·
                    refine ⟨154568973577756327940627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1648735718162734164700021 154568973577756327940627)
                    ·
                      rfl

theorem cell23_903066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_903066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903066 prefixEnd_903066 := by exact prefixLift 903066
  have htrace : WordTrace (prefixWord ++ tailWord_903066) baseStart_903066 baseEnd_903066 := by
    simpa [prefixWord, tailWord_903066, baseEnd_903066] using wordTrace_append hprefix tailTrace_903066
  have hstable : (prefixWord ++ tailWord_903066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903066).length < 2 ^ (prefixWord ++ tailWord_903066).sum := by decide
  have hdescent : baseEnd_903066 < baseStart_903066 := by decide
  rcases family_descends (prefixWord ++ tailWord_903066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903096 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_903096 : Nat := 118140960795 + 903096 * 2 ^ 59
def prefixEnd_903096 : Nat := 4983230072969 + 3 ^ 40 * 903096 * 2
def baseEnd_903096 : Nat := 154574108384301288815581

theorem tailTrace_903096 : CollatzResearch.WordTrace tailWord_903096 prefixEnd_903096 154574108384301288815581 := by
  unfold tailWord_903096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469308568122451681256571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21959078090829935575008761 16469308568122451681256571)
  ·
    refine ⟨24703962852183677521884857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469308568122451681256571 24703962852183677521884857)
    ·
      refine ⟨18527972139137758141413643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24703962852183677521884857 18527972139137758141413643)
      ·
        refine ⟨27791958208706637212120465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18527972139137758141413643 27791958208706637212120465)
        ·
          refine ⟨20843968656529977909090349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27791958208706637212120465 20843968656529977909090349)
          ·
            refine ⟨7816488246198741715908881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20843968656529977909090349 7816488246198741715908881)
            ·
              refine ⟨5862366184649056286931661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816488246198741715908881 5862366184649056286931661)
              ·
                refine ⟨2198387319243396107599373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5862366184649056286931661 2198387319243396107599373)
                ·
                  refine ⟨824395244716273540349765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2198387319243396107599373 824395244716273540349765)
                  ·
                    refine ⟨154574108384301288815581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824395244716273540349765 154574108384301288815581)
                    ·
                      rfl

theorem cell23_903096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_903096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903096 prefixEnd_903096 := by exact prefixLift 903096
  have htrace : WordTrace (prefixWord ++ tailWord_903096) baseStart_903096 baseEnd_903096 := by
    simpa [prefixWord, tailWord_903096, baseEnd_903096] using wordTrace_append hprefix tailTrace_903096
  have hstable : (prefixWord ++ tailWord_903096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903096).length < 2 ^ (prefixWord ++ tailWord_903096).sum := by decide
  have hdescent : baseEnd_903096 < baseStart_903096 := by decide
  rcases family_descends (prefixWord ++ tailWord_903096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903173 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_903173 : Nat := 118140960795 + 903173 * 2 ^ 59
def prefixEnd_903173 : Nat := 4983230072969 + 3 ^ 40 * 903173 * 2
def baseEnd_903173 : Nat := 154587287721100021727963

theorem tailTrace_903173 : CollatzResearch.WordTrace tailWord_903173 prefixEnd_903173 154587287721100021727963 := by
  unfold tailWord_903173
  simp only [CollatzResearch.WordTrace]
  refine ⟨32941425556965945513066173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21960950371310630342044115 32941425556965945513066173)
  ·
    refine ⟨12353034583862229567399815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32941425556965945513066173 12353034583862229567399815)
    ·
      refine ⟨18529551875793344351099723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12353034583862229567399815 18529551875793344351099723)
      ·
        refine ⟨27794327813690016526649585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18529551875793344351099723 27794327813690016526649585)
        ·
          refine ⟨20845745860267512394987189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27794327813690016526649585 20845745860267512394987189)
          ·
            refine ⟨1954288674400079287030049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20845745860267512394987189 1954288674400079287030049)
            ·
              refine ⟨1465716505800059465272537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954288674400079287030049 1465716505800059465272537)
              ·
                refine ⟨1099287379350044598954403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465716505800059465272537 1099287379350044598954403)
                ·
                  refine ⟨1648931069025066898431605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099287379350044598954403 1648931069025066898431605)
                  ·
                    refine ⟨154587287721100021727963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1648931069025066898431605 154587287721100021727963)
                    ·
                      rfl

theorem cell23_903173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_903173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903173 prefixEnd_903173 := by exact prefixLift 903173
  have htrace : WordTrace (prefixWord ++ tailWord_903173) baseStart_903173 baseEnd_903173 := by
    simpa [prefixWord, tailWord_903173, baseEnd_903173] using wordTrace_append hprefix tailTrace_903173
  have hstable : (prefixWord ++ tailWord_903173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903173).length < 2 ^ (prefixWord ++ tailWord_903173).sum := by decide
  have hdescent : baseEnd_903173 < baseStart_903173 := by decide
  rcases family_descends (prefixWord ++ tailWord_903173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903203 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 2, 4]
def baseStart_903203 : Nat := 118140960795 + 903203 * 2 ^ 59
def prefixEnd_903203 : Nat := 4983230072969 + 3 ^ 40 * 903203 * 2
def baseEnd_903203 : Nat := 154592422527644982602917

theorem tailTrace_903203 : CollatzResearch.WordTrace tailWord_903203 prefixEnd_903203 154592422527644982602917 := by
  unfold tailWord_903203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32942519746857260636658263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21961679831238173757772175 32942519746857260636658263)
  ·
    refine ⟨49413779620285890954987395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32942519746857260636658263 49413779620285890954987395)
    ·
      refine ⟨74120669430428836432481093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49413779620285890954987395 74120669430428836432481093)
      ·
        refine ⟨13897625518205406831090205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74120669430428836432481093 13897625518205406831090205)
        ·
          refine ⟨5211609569327027561658827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13897625518205406831090205 5211609569327027561658827)
          ·
            refine ⟨7817414353990541342488241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211609569327027561658827 7817414353990541342488241)
            ·
              refine ⟨5863060765492906006866181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817414353990541342488241 5863060765492906006866181)
              ·
                refine ⟨1099323893529919876287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5863060765492906006866181 1099323893529919876287409)
                ·
                  refine ⟨824492920147439907215557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099323893529919876287409 824492920147439907215557)
                  ·
                    refine ⟨154592422527644982602917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824492920147439907215557 154592422527644982602917)
                    ·
                      rfl

theorem cell23_903203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 4].length) (baseStart_903203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903203 prefixEnd_903203 := by exact prefixLift 903203
  have htrace : WordTrace (prefixWord ++ tailWord_903203) baseStart_903203 baseEnd_903203 := by
    simpa [prefixWord, tailWord_903203, baseEnd_903203] using wordTrace_append hprefix tailTrace_903203
  have hstable : (prefixWord ++ tailWord_903203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903203).length < 2 ^ (prefixWord ++ tailWord_903203).sum := by decide
  have hdescent : baseEnd_903203 < baseStart_903203 := by decide
  rcases family_descends (prefixWord ++ tailWord_903203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903204 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_903204 : Nat := 118140960795 + 903204 * 2 ^ 59
def prefixEnd_903204 : Nat := 4983230072969 + 3 ^ 40 * 903204 * 2
def baseEnd_903204 : Nat := 463777781063589443896247

theorem tailTrace_903204 : CollatzResearch.WordTrace tailWord_903204 prefixEnd_903204 463777781063589443896247 := by
  unfold tailWord_903204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471278109926818903722333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21961704146569091871629777 16471278109926818903722333)
  ·
    refine ⟨6176729291222557088895875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16471278109926818903722333 6176729291222557088895875)
    ·
      refine ⟨9265093936833835633343813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6176729291222557088895875 9265093936833835633343813)
      ·
        refine ⟨1737205113156344181251965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9265093936833835633343813 1737205113156344181251965)
        ·
          refine ⟨651451917433629067969487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1737205113156344181251965 651451917433629067969487)
          ·
            refine ⟨977177876150443601954231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651451917433629067969487 977177876150443601954231)
            ·
              refine ⟨1465766814225665402931347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977177876150443601954231 1465766814225665402931347)
              ·
                refine ⟨2198650221338498104397021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465766814225665402931347 2198650221338498104397021)
                ·
                  refine ⟨824493833001936789148883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2198650221338498104397021 824493833001936789148883)
                  ·
                    refine ⟨1236740749502905183723325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824493833001936789148883 1236740749502905183723325)
                    ·
                      refine ⟨463777781063589443896247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1236740749502905183723325 463777781063589443896247)
                      ·
                        rfl

theorem cell23_903204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_903204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903204 prefixEnd_903204 := by exact prefixLift 903204
  have htrace : WordTrace (prefixWord ++ tailWord_903204) baseStart_903204 baseEnd_903204 := by
    simpa [prefixWord, tailWord_903204, baseEnd_903204] using wordTrace_append hprefix tailTrace_903204
  have hstable : (prefixWord ++ tailWord_903204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903204).length < 2 ^ (prefixWord ++ tailWord_903204).sum := by decide
  have hdescent : baseEnd_903204 < baseStart_903204 := by decide
  rcases family_descends (prefixWord ++ tailWord_903204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903216 : List Nat := [2, 1, 1, 1, 2, 6, 2, 8]
def baseStart_903216 : Nat := 118140960795 + 903216 * 2 ^ 59
def prefixEnd_903216 : Nat := 4983230072969 + 3 ^ 40 * 903216 * 2
def baseEnd_903216 : Nat := 17177183067831236923933

theorem tailTrace_903216 : CollatzResearch.WordTrace tailWord_903216 prefixEnd_903216 17177183067831236923933 := by
  unfold tailWord_903216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16471496947905081928440751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21961995930540109237921001 16471496947905081928440751)
  ·
    refine ⟨24707245421857622892661127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16471496947905081928440751 24707245421857622892661127)
    ·
      refine ⟨37060868132786434338991691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24707245421857622892661127 37060868132786434338991691)
      ·
        refine ⟨55591302199179651508487537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37060868132786434338991691 55591302199179651508487537)
        ·
          refine ⟨41693476649384738631365653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55591302199179651508487537 41693476649384738631365653)
          ·
            refine ⟨1954381717939909623345265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41693476649384738631365653 1954381717939909623345265)
            ·
              refine ⟨1465786288454932217508949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954381717939909623345265 1465786288454932217508949)
              ·
                refine ⟨17177183067831236923933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1465786288454932217508949 17177183067831236923933)
                ·
                  rfl

theorem cell23_903216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_903216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903216 prefixEnd_903216 := by exact prefixLift 903216
  have htrace : WordTrace (prefixWord ++ tailWord_903216) baseStart_903216 baseEnd_903216 := by
    simpa [prefixWord, tailWord_903216, baseEnd_903216] using wordTrace_append hprefix tailTrace_903216
  have hstable : (prefixWord ++ tailWord_903216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903216).length < 2 ^ (prefixWord ++ tailWord_903216).sum := by decide
  have hdescent : baseEnd_903216 < baseStart_903216 := by decide
  rcases family_descends (prefixWord ++ tailWord_903216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903254 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_903254 : Nat := 118140960795 + 903254 * 2 ^ 59
def prefixEnd_903254 : Nat := 4983230072969 + 3 ^ 40 * 903254 * 2
def baseEnd_903254 : Nat := 154601151698771416090339

theorem tailTrace_903254 : CollatzResearch.WordTrace tailWord_903254 prefixEnd_903254 154601151698771416090339 := by
  unfold tailWord_903254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059023741854531021672801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21962919913114997564509877 2059023741854531021672801)
  ·
    refine ⟨1544267806390898266254601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2059023741854531021672801 1544267806390898266254601)
    ·
      refine ⟨1158200854793173699690951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544267806390898266254601 1158200854793173699690951)
      ·
        refine ⟨1737301282189760549536427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158200854793173699690951 1737301282189760549536427)
        ·
          refine ⟨2605951923284640824304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737301282189760549536427 2605951923284640824304641)
          ·
            refine ⟨1954463942463480618228481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605951923284640824304641 1954463942463480618228481)
            ·
              refine ⟨1465847956847610463671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954463942463480618228481 1465847956847610463671361)
              ·
                refine ⟨1099385967635707847753521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1465847956847610463671361 1099385967635707847753521)
                ·
                  refine ⟨824539475726780885815141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099385967635707847753521 824539475726780885815141)
                  ·
                    refine ⟨154601151698771416090339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824539475726780885815141 154601151698771416090339)
                    ·
                      rfl

theorem cell23_903254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_903254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903254 prefixEnd_903254 := by exact prefixLift 903254
  have htrace : WordTrace (prefixWord ++ tailWord_903254) baseStart_903254 baseEnd_903254 := by
    simpa [prefixWord, tailWord_903254, baseEnd_903254] using wordTrace_append hprefix tailTrace_903254
  have hstable : (prefixWord ++ tailWord_903254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903254).length < 2 ^ (prefixWord ++ tailWord_903254).sum := by decide
  have hdescent : baseEnd_903254 < baseStart_903254 := by decide
  rcases family_descends (prefixWord ++ tailWord_903254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903261 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_903261 : Nat := 118140960795 + 903261 * 2 ^ 59
def prefixEnd_903261 : Nat := 4983230072969 + 3 ^ 40 * 903261 * 2
def baseEnd_903261 : Nat := 463807049460895720883485

theorem tailTrace_903261 : CollatzResearch.WordTrace tailWord_903261 prefixEnd_903261 463807049460895720883485 := by
  unfold tailWord_903261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32944635180647136542269637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21963090120431424361513091 32944635180647136542269637)
  ·
    refine ⟨6177119096371338101675557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32944635180647136542269637 6177119096371338101675557)
    ·
      refine ⟨1158209830569625894064167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6177119096371338101675557 1158209830569625894064167)
      ·
        refine ⟨1737314745854438841096251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158209830569625894064167 1737314745854438841096251)
        ·
          refine ⟨2605972118781658261644377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737314745854438841096251 2605972118781658261644377)
          ·
            refine ⟨1954479089086243696233283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605972118781658261644377 1954479089086243696233283)
            ·
              refine ⟨2931718633629365544349925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954479089086243696233283 2931718633629365544349925)
              ·
                refine ⟨549697243805506039565611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2931718633629365544349925 549697243805506039565611)
                ·
                  refine ⟨824545865708259059348417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549697243805506039565611 824545865708259059348417)
                  ·
                    refine ⟨618409399281194294511313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 824545865708259059348417 618409399281194294511313)
                    ·
                      refine ⟨463807049460895720883485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618409399281194294511313 463807049460895720883485)
                      ·
                        rfl

theorem cell23_903261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_903261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903261 prefixEnd_903261 := by exact prefixLift 903261
  have htrace : WordTrace (prefixWord ++ tailWord_903261) baseStart_903261 baseEnd_903261 := by
    simpa [prefixWord, tailWord_903261, baseEnd_903261] using wordTrace_append hprefix tailTrace_903261
  have hstable : (prefixWord ++ tailWord_903261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903261).length < 2 ^ (prefixWord ++ tailWord_903261).sum := by decide
  have hdescent : baseEnd_903261 < baseStart_903261 := by decide
  rcases family_descends (prefixWord ++ tailWord_903261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903276 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_903276 : Nat := 118140960795 + 903276 * 2 ^ 59
def prefixEnd_903276 : Nat := 4983230072969 + 3 ^ 40 * 903276 * 2
def baseEnd_903276 : Nat := 154604917223571054065305

theorem tailTrace_903276 : CollatzResearch.WordTrace tailWord_903276 prefixEnd_903276 154604917223571054065305 := by
  unfold tailWord_903276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472591137796397052032841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21963454850395196069377121 16472591137796397052032841)
  ·
    refine ⟨12354443353347297789024631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16472591137796397052032841 12354443353347297789024631)
    ·
      refine ⟨18531665030020946683536947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12354443353347297789024631 18531665030020946683536947)
      ·
        refine ⟨27797497545031420025305421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531665030020946683536947 27797497545031420025305421)
        ·
          refine ⟨10424061579386782509489533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27797497545031420025305421 10424061579386782509489533)
          ·
            refine ⟨3909023092270043441058575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10424061579386782509489533 3909023092270043441058575)
            ·
              refine ⟨5863534638405065161587863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909023092270043441058575 5863534638405065161587863)
              ·
                refine ⟨8795301957607597742381795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863534638405065161587863 8795301957607597742381795)
                ·
                  refine ⟨13192952936411396613572693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8795301957607597742381795 13192952936411396613572693)
                  ·
                    refine ⟨154604917223571054065305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13192952936411396613572693 154604917223571054065305)
                    ·
                      rfl

theorem cell23_903276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_903276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903276 prefixEnd_903276 := by exact prefixLift 903276
  have htrace : WordTrace (prefixWord ++ tailWord_903276) baseStart_903276 baseEnd_903276 := by
    simpa [prefixWord, tailWord_903276, baseEnd_903276] using wordTrace_append hprefix tailTrace_903276
  have hstable : (prefixWord ++ tailWord_903276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903276).length < 2 ^ (prefixWord ++ tailWord_903276).sum := by decide
  have hdescent : baseEnd_903276 < baseStart_903276 := by decide
  rcases family_descends (prefixWord ++ tailWord_903276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903296 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_903296 : Nat := 118140960795 + 903296 * 2 ^ 59
def prefixEnd_903296 : Nat := 4983230072969 + 3 ^ 40 * 903296 * 2
def baseEnd_903296 : Nat := 463825021283803083945823

theorem tailTrace_903296 : CollatzResearch.WordTrace tailWord_903296 prefixEnd_903296 463825021283803083945823 := by
  unfold tailWord_903296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472955867760168759896871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21963941157013558346529161 16472955867760168759896871)
  ·
    refine ⟨24709433801640253139845307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472955867760168759896871 24709433801640253139845307)
    ·
      refine ⟨37064150702460379709767961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24709433801640253139845307 37064150702460379709767961)
      ·
        refine ⟨27798113026845284782325971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37064150702460379709767961 27798113026845284782325971)
        ·
          refine ⟨41697169540267927173488957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27798113026845284782325971 41697169540267927173488957)
          ·
            refine ⟨15636438577600472690058359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41697169540267927173488957 15636438577600472690058359)
            ·
              refine ⟨23454657866400709035087539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15636438577600472690058359 23454657866400709035087539)
              ·
                refine ⟨35181986799601063552631309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23454657866400709035087539 35181986799601063552631309)
                ·
                  refine ⟨13193245049850398832236741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35181986799601063552631309 13193245049850398832236741)
                  ·
                    refine ⟨2473733446846949781044389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13193245049850398832236741 2473733446846949781044389)
                    ·
                      refine ⟨463825021283803083945823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2473733446846949781044389 463825021283803083945823)
                      ·
                        rfl

theorem cell23_903296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_903296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903296 prefixEnd_903296 := by exact prefixLift 903296
  have htrace : WordTrace (prefixWord ++ tailWord_903296) baseStart_903296 baseEnd_903296 := by
    simpa [prefixWord, tailWord_903296, baseEnd_903296] using wordTrace_append hprefix tailTrace_903296
  have hstable : (prefixWord ++ tailWord_903296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903296).length < 2 ^ (prefixWord ++ tailWord_903296).sum := by decide
  have hdescent : baseEnd_903296 < baseStart_903296 := by decide
  rcases family_descends (prefixWord ++ tailWord_903296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903300 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_903300 : Nat := 118140960795 + 903300 * 2 ^ 59
def prefixEnd_903300 : Nat := 4983230072969 + 3 ^ 40 * 903300 * 2
def baseEnd_903300 : Nat := 463827075206421068295805

theorem tailTrace_903300 : CollatzResearch.WordTrace tailWord_903300 prefixEnd_903300 463827075206421068295805 := by
  unfold tailWord_903300
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473028813752923101469677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21964038418337230801959569 16473028813752923101469677)
  ·
    refine ⟨6177385805157346163051129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16473028813752923101469677 6177385805157346163051129)
    ·
      refine ⟨4633039353868009622288347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6177385805157346163051129 4633039353868009622288347)
      ·
        refine ⟨6949559030802014433432521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633039353868009622288347 6949559030802014433432521)
        ·
          refine ⟨5212169273101510825074391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6949559030802014433432521 5212169273101510825074391)
          ·
            refine ⟨7818253909652266237611587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212169273101510825074391 7818253909652266237611587)
            ·
              refine ⟨11727380864478399356417381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818253909652266237611587 11727380864478399356417381)
              ·
                refine ⟨2198883912089699879328259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11727380864478399356417381 2198883912089699879328259)
                ·
                  refine ⟨3298325868134549818992389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198883912089699879328259 3298325868134549818992389)
                  ·
                    refine ⟨618436100275228091061073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298325868134549818992389 618436100275228091061073)
                    ·
                      refine ⟨463827075206421068295805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618436100275228091061073 463827075206421068295805)
                      ·
                        rfl

theorem cell23_903300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_903300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903300 prefixEnd_903300 := by exact prefixLift 903300
  have htrace : WordTrace (prefixWord ++ tailWord_903300) baseStart_903300 baseEnd_903300 := by
    simpa [prefixWord, tailWord_903300, baseEnd_903300] using wordTrace_append hprefix tailTrace_903300
  have hstable : (prefixWord ++ tailWord_903300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903300).length < 2 ^ (prefixWord ++ tailWord_903300).sum := by decide
  have hdescent : baseEnd_903300 < baseStart_903300 := by decide
  rcases family_descends (prefixWord ++ tailWord_903300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903304 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_903304 : Nat := 118140960795 + 903304 * 2 ^ 59
def prefixEnd_903304 : Nat := 4983230072969 + 3 ^ 40 * 903304 * 2
def baseEnd_903304 : Nat := 463829129129039052645787

theorem tailTrace_903304 : CollatzResearch.WordTrace tailWord_903304 prefixEnd_903304 463829129129039052645787 := by
  unfold tailWord_903304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473101759745677443042483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21964135679660903257389977 16473101759745677443042483)
  ·
    refine ⟨24709652639618516164563725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16473101759745677443042483 24709652639618516164563725)
    ·
      refine ⟨9266119739856943561711397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24709652639618516164563725 9266119739856943561711397)
      ·
        refine ⟨1737397451223176917820887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9266119739856943561711397 1737397451223176917820887)
        ·
          refine ⟨2606096176834765376731331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737397451223176917820887 2606096176834765376731331)
          ·
            refine ⟨3909144265252148065096997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606096176834765376731331 3909144265252148065096997)
            ·
              refine ⟨732964549734777762205687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3909144265252148065096997 732964549734777762205687)
              ·
                refine ⟨1099446824602166643308531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732964549734777762205687 1099446824602166643308531)
                ·
                  refine ⟨1649170236903249964962797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099446824602166643308531 1649170236903249964962797)
                  ·
                    refine ⟨618438838838718736861049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649170236903249964962797 618438838838718736861049)
                    ·
                      refine ⟨463829129129039052645787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618438838838718736861049 463829129129039052645787)
                      ·
                        rfl

theorem cell23_903304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_903304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903304 prefixEnd_903304 := by exact prefixLift 903304
  have htrace : WordTrace (prefixWord ++ tailWord_903304) baseStart_903304 baseEnd_903304 := by
    simpa [prefixWord, tailWord_903304, baseEnd_903304] using wordTrace_append hprefix tailTrace_903304
  have hstable : (prefixWord ++ tailWord_903304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903304).length < 2 ^ (prefixWord ++ tailWord_903304).sum := by decide
  have hdescent : baseEnd_903304 < baseStart_903304 := by decide
  rcases family_descends (prefixWord ++ tailWord_903304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903323 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 5]
def baseStart_903323 : Nat := 118140960795 + 903323 * 2 ^ 59
def prefixEnd_903323 : Nat := 4983230072969 + 3 ^ 40 * 903323 * 2
def baseEnd_903323 : Nat := 51537653917941608700911

theorem tailTrace_903323 : CollatzResearch.WordTrace tailWord_903323 prefixEnd_903323 51537653917941608700911 := by
  unfold tailWord_903323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32946896506422521131026623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21964597670948347420684415 32946896506422521131026623)
  ·
    refine ⟨49420344759633781696539935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32946896506422521131026623 49420344759633781696539935)
    ·
      refine ⟨74130517139450672544809903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49420344759633781696539935 74130517139450672544809903)
      ·
        refine ⟨111195775709176008817214855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74130517139450672544809903 111195775709176008817214855)
        ·
          refine ⟨166793663563764013225822283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111195775709176008817214855 166793663563764013225822283)
          ·
            refine ⟨250190495345646019838733425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166793663563764013225822283 250190495345646019838733425)
            ·
              refine ⟨187642871509234514879050069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250190495345646019838733425 187642871509234514879050069)
              ·
                refine ⟨549734975124710492809717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 187642871509234514879050069 549734975124710492809717)
                ·
                  refine ⟨51537653917941608700911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 549734975124710492809717 51537653917941608700911)
                  ·
                    rfl

theorem cell23_903323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 5].length) (baseStart_903323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903323 prefixEnd_903323 := by exact prefixLift 903323
  have htrace : WordTrace (prefixWord ++ tailWord_903323) baseStart_903323 baseEnd_903323 := by
    simpa [prefixWord, tailWord_903323, baseEnd_903323] using wordTrace_append hprefix tailTrace_903323
  have hstable : (prefixWord ++ tailWord_903323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903323).length < 2 ^ (prefixWord ++ tailWord_903323).sum := by decide
  have hdescent : baseEnd_903323 < baseStart_903323 := by decide
  rcases family_descends (prefixWord ++ tailWord_903323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903330 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_903330 : Nat := 118140960795 + 903330 * 2 ^ 59
def prefixEnd_903330 : Nat := 4983230072969 + 3 ^ 40 * 903330 * 2
def baseEnd_903330 : Nat := 463842479626055950920667

theorem tailTrace_903330 : CollatzResearch.WordTrace tailWord_903330 prefixEnd_903330 463842479626055950920667 := by
  unfold tailWord_903330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236787954349290331632861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21964767878264774217687629 8236787954349290331632861)
  ·
    refine ⟨3088795482880983874362323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8236787954349290331632861 3088795482880983874362323)
    ·
      refine ⟨4633193224321475811543485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088795482880983874362323 4633193224321475811543485)
      ·
        refine ⟨1737447459120553429328807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4633193224321475811543485 1737447459120553429328807)
        ·
          refine ⟨2606171188680830143993211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737447459120553429328807 2606171188680830143993211)
          ·
            refine ⟨3909256783021245215989817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606171188680830143993211 3909256783021245215989817)
            ·
              refine ⟨2931942587265933911992363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909256783021245215989817 2931942587265933911992363)
              ·
                refine ⟨4397913880898900867988545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931942587265933911992363 4397913880898900867988545)
                ·
                  refine ⟨3298435410674175650991409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397913880898900867988545 3298435410674175650991409)
                  ·
                    refine ⟨2473826558005631738243557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298435410674175650991409 2473826558005631738243557)
                    ·
                      refine ⟨463842479626055950920667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2473826558005631738243557 463842479626055950920667)
                      ·
                        rfl

theorem cell23_903330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_903330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903330 prefixEnd_903330 := by exact prefixLift 903330
  have htrace : WordTrace (prefixWord ++ tailWord_903330) baseStart_903330 baseEnd_903330 := by
    simpa [prefixWord, tailWord_903330, baseEnd_903330] using wordTrace_append hprefix tailTrace_903330
  have hstable : (prefixWord ++ tailWord_903330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903330).length < 2 ^ (prefixWord ++ tailWord_903330).sum := by decide
  have hdescent : baseEnd_903330 < baseStart_903330 := by decide
  rcases family_descends (prefixWord ++ tailWord_903330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903333 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_903333 : Nat := 118140960795 + 903333 * 2 ^ 59
def prefixEnd_903333 : Nat := 4983230072969 + 3 ^ 40 * 903333 * 2
def baseEnd_903333 : Nat := 463844020068019439183153

theorem tailTrace_903333 : CollatzResearch.WordTrace tailWord_903333 prefixEnd_903333 463844020068019439183153 := by
  unfold tailWord_903333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947261236386292838890653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21964840824257528559260435 32947261236386292838890653)
  ·
    refine ⟨12355222963644859814583995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32947261236386292838890653 12355222963644859814583995)
    ·
      refine ⟨18532834445467289721875993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12355222963644859814583995 18532834445467289721875993)
      ·
        refine ⟨13899625834100467291406995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18532834445467289721875993 13899625834100467291406995)
        ·
          refine ⟨20849438751150700937110493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13899625834100467291406995 20849438751150700937110493)
          ·
            refine ⟨7818539531681512851416435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20849438751150700937110493 7818539531681512851416435)
            ·
              refine ⟨11727809297522269277124653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818539531681512851416435 11727809297522269277124653)
              ·
                refine ⟨4397928486570850978921745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727809297522269277124653 4397928486570850978921745)
                ·
                  refine ⟨3298446364928138234191309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397928486570850978921745 3298446364928138234191309)
                  ·
                    refine ⟨1236917386848051837821741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3298446364928138234191309 1236917386848051837821741)
                    ·
                      refine ⟨463844020068019439183153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1236917386848051837821741 463844020068019439183153)
                      ·
                        rfl

theorem cell23_903333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_903333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903333 prefixEnd_903333 := by exact prefixLift 903333
  have htrace : WordTrace (prefixWord ++ tailWord_903333) baseStart_903333 baseEnd_903333 := by
    simpa [prefixWord, tailWord_903333, baseEnd_903333] using wordTrace_append hprefix tailTrace_903333
  have hstable : (prefixWord ++ tailWord_903333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903333).length < 2 ^ (prefixWord ++ tailWord_903333).sum := by decide
  have hdescent : baseEnd_903333 < baseStart_903333 := by decide
  rcases family_descends (prefixWord ++ tailWord_903333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903353 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_903353 : Nat := 118140960795 + 903353 * 2 ^ 59
def prefixEnd_903353 : Nat := 4983230072969 + 3 ^ 40 * 903353 * 2
def baseEnd_903353 : Nat := 154618096560369786977687

theorem tailTrace_903353 : CollatzResearch.WordTrace tailWord_903353 prefixEnd_903353 154618096560369786977687 := by
  unfold tailWord_903353
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947990696313836254618713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21965327130875890836412475 32947990696313836254618713)
  ·
    refine ⟨24710993022235377190964035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32947990696313836254618713 24710993022235377190964035)
    ·
      refine ⟨37066489533353065786446053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710993022235377190964035 37066489533353065786446053)
      ·
        refine ⟨6949966787503699834958635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37066489533353065786446053 6949966787503699834958635)
        ·
          refine ⟨10424950181255549752437953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949966787503699834958635 10424950181255549752437953)
          ·
            refine ⟨7818712635941662314328465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10424950181255549752437953 7818712635941662314328465)
            ·
              refine ⟨5864034476956246735746349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818712635941662314328465 5864034476956246735746349)
              ·
                refine ⟨2199012928858592525904881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864034476956246735746349 2199012928858592525904881)
                ·
                  refine ⟨1649259696643944394428661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2199012928858592525904881 1649259696643944394428661)
                  ·
                    refine ⟨154618096560369786977687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1649259696643944394428661 154618096560369786977687)
                    ·
                      rfl

theorem cell23_903353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_903353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903353 prefixEnd_903353 := by exact prefixLift 903353
  have htrace : WordTrace (prefixWord ++ tailWord_903353) baseStart_903353 baseEnd_903353 := by
    simpa [prefixWord, tailWord_903353, baseEnd_903353] using wordTrace_append hprefix tailTrace_903353
  have hstable : (prefixWord ++ tailWord_903353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903353).length < 2 ^ (prefixWord ++ tailWord_903353).sum := by decide
  have hdescent : baseEnd_903353 < baseStart_903353 := by decide
  rcases family_descends (prefixWord ++ tailWord_903353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903434 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_903434 : Nat := 118140960795 + 903434 * 2 ^ 59
def prefixEnd_903434 : Nat := 4983230072969 + 3 ^ 40 * 903434 * 2
def baseEnd_903434 : Nat := 154631960538041181340063

theorem tailTrace_903434 : CollatzResearch.WordTrace tailWord_903434 prefixEnd_903434 154631960538041181340063 := by
  unfold tailWord_903434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237736252255096772079339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21967296672680258058878237 8237736252255096772079339)
  ·
    refine ⟨12356604378382645158119009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8237736252255096772079339 12356604378382645158119009)
    ·
      refine ⟨9267453283786983868589257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12356604378382645158119009 9267453283786983868589257)
      ·
        refine ⟨6950589962840237901441943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9267453283786983868589257 6950589962840237901441943)
        ·
          refine ⟨10425884944260356852162915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950589962840237901441943 10425884944260356852162915)
          ·
            refine ⟨15638827416390535278244373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425884944260356852162915 15638827416390535278244373)
            ·
              refine ⟨733070035143306341167705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15638827416390535278244373 733070035143306341167705)
              ·
                refine ⟨549802526357479755875779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733070035143306341167705 549802526357479755875779)
                ·
                  refine ⟨824703789536219633813669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549802526357479755875779 824703789536219633813669)
                  ·
                    refine ⟨154631960538041181340063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 824703789536219633813669 154631960538041181340063)
                    ·
                      rfl

theorem cell23_903434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_903434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903434 prefixEnd_903434 := by exact prefixLift 903434
  have htrace : WordTrace (prefixWord ++ tailWord_903434) baseStart_903434 baseEnd_903434 := by
    simpa [prefixWord, tailWord_903434, baseEnd_903434] using wordTrace_append hprefix tailTrace_903434
  have hstable : (prefixWord ++ tailWord_903434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903434).length < 2 ^ (prefixWord ++ tailWord_903434).sum := by decide
  have hdescent : baseEnd_903434 < baseStart_903434 := by decide
  rcases family_descends (prefixWord ++ tailWord_903434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903460 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_903460 : Nat := 118140960795 + 903460 * 2 ^ 59
def prefixEnd_903460 : Nat := 4983230072969 + 3 ^ 40 * 903460 * 2
def baseEnd_903460 : Nat := 154636410703713480765023

theorem tailTrace_903460 : CollatzResearch.WordTrace tailWord_903460 prefixEnd_903460 154636410703713480765023 := by
  unfold tailWord_903460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475946653463096764381917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21967928871284129019175889 16475946653463096764381917)
  ·
    refine ⟨6178479995048661286643219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16475946653463096764381917 6178479995048661286643219)
    ·
      refine ⟨9267719992572991929964829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6178479995048661286643219 9267719992572991929964829)
      ·
        refine ⟨3475394997214871973736811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9267719992572991929964829 3475394997214871973736811)
        ·
          refine ⟨5213092495822307960605217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475394997214871973736811 5213092495822307960605217)
          ·
            refine ⟨3909819371866730970453913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213092495822307960605217 3909819371866730970453913)
            ·
              refine ⟨2932364528900048227840435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3909819371866730970453913 2932364528900048227840435)
              ·
                refine ⟨4398546793350072341760653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932364528900048227840435 4398546793350072341760653)
                ·
                  refine ⟨1649455047506277128160245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4398546793350072341760653 1649455047506277128160245)
                  ·
                    refine ⟨154636410703713480765023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1649455047506277128160245 154636410703713480765023)
                    ·
                      rfl

theorem cell23_903460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_903460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903460 prefixEnd_903460 := by exact prefixLift 903460
  have htrace : WordTrace (prefixWord ++ tailWord_903460) baseStart_903460 baseEnd_903460 := by
    simpa [prefixWord, tailWord_903460, baseEnd_903460] using wordTrace_append hprefix tailTrace_903460
  have hstable : (prefixWord ++ tailWord_903460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903460).length < 2 ^ (prefixWord ++ tailWord_903460).sum := by decide
  have hdescent : baseEnd_903460 < baseStart_903460 := by decide
  rcases family_descends (prefixWord ++ tailWord_903460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903493 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_903493 : Nat := 118140960795 + 903493 * 2 ^ 59
def prefixEnd_903493 : Nat := 4983230072969 + 3 ^ 40 * 903493 * 2
def baseEnd_903493 : Nat := 463926176972738813182417

theorem tailTrace_903493 : CollatzResearch.WordTrace tailWord_903493 prefixEnd_903493 463926176972738813182417 := by
  unfold tailWord_903493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32953096915806640164715133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21968731277204426776476755 32953096915806640164715133)
  ·
    refine ⟨12357411343427490061768175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32953096915806640164715133 12357411343427490061768175)
    ·
      refine ⟨18536117015141235092652263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12357411343427490061768175 18536117015141235092652263)
      ·
        refine ⟨27804175522711852638978395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18536117015141235092652263 27804175522711852638978395)
        ·
          refine ⟨41706263284067778958467593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27804175522711852638978395 41706263284067778958467593)
          ·
            refine ⟨31279697463050834218850695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41706263284067778958467593 31279697463050834218850695)
            ·
              refine ⟨46919546194576251328276043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31279697463050834218850695 46919546194576251328276043)
              ·
                refine ⟨70379319291864376992414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46919546194576251328276043 70379319291864376992414065)
                ·
                  refine ⟨52784489468898282744310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70379319291864376992414065 52784489468898282744310549)
                  ·
                    refine ⟨2474272943854607003639557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52784489468898282744310549 2474272943854607003639557)
                    ·
                      refine ⟨463926176972738813182417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2474272943854607003639557 463926176972738813182417)
                      ·
                        rfl

theorem cell23_903493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_903493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903493 prefixEnd_903493 := by exact prefixLift 903493
  have htrace : WordTrace (prefixWord ++ tailWord_903493) baseStart_903493 baseEnd_903493 := by
    simpa [prefixWord, tailWord_903493, baseEnd_903493] using wordTrace_append hprefix tailTrace_903493
  have hstable : (prefixWord ++ tailWord_903493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903493).length < 2 ^ (prefixWord ++ tailWord_903493).sum := by decide
  have hdescent : baseEnd_903493 < baseStart_903493 := by decide
  rcases family_descends (prefixWord ++ tailWord_903493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903500 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_903500 : Nat := 118140960795 + 903500 * 2 ^ 59
def prefixEnd_903500 : Nat := 4983230072969 + 3 ^ 40 * 903500 * 2
def baseEnd_903500 : Nat := 463929771337320285794885

theorem tailTrace_903500 : CollatzResearch.WordTrace tailWord_903500 prefixEnd_903500 463929771337320285794885 := by
  unfold tailWord_903500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476676113390640180109977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21968901484520853573479969 16476676113390640180109977)
  ·
    refine ⟨12357507085042980135082483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16476676113390640180109977 12357507085042980135082483)
    ·
      refine ⟨18536260627564470202623725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12357507085042980135082483 18536260627564470202623725)
      ·
        refine ⟨6951097735336676325983897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18536260627564470202623725 6951097735336676325983897)
        ·
          refine ⟨5213323301502507244487923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6951097735336676325983897 5213323301502507244487923)
          ·
            refine ⟨7819984952253760866731885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213323301502507244487923 7819984952253760866731885)
            ·
              refine ⟨2932494357095160325024457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7819984952253760866731885 2932494357095160325024457)
              ·
                refine ⟨2199370767821370243768343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2932494357095160325024457 2199370767821370243768343)
                ·
                  refine ⟨3299056151732055365652515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2199370767821370243768343 3299056151732055365652515)
                  ·
                    refine ⟨4948584227598083048478773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3299056151732055365652515 4948584227598083048478773)
                    ·
                      refine ⟨463929771337320285794885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4948584227598083048478773 463929771337320285794885)
                      ·
                        rfl

theorem cell23_903500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_903500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903500 prefixEnd_903500 := by exact prefixLift 903500
  have htrace : WordTrace (prefixWord ++ tailWord_903500) baseStart_903500 baseEnd_903500 := by
    simpa [prefixWord, tailWord_903500, baseEnd_903500] using wordTrace_append hprefix tailTrace_903500
  have hstable : (prefixWord ++ tailWord_903500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903500).length < 2 ^ (prefixWord ++ tailWord_903500).sum := by decide
  have hdescent : baseEnd_903500 < baseStart_903500 := by decide
  rcases family_descends (prefixWord ++ tailWord_903500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903520 : List Nat := [2, 1, 1, 3, 5, 1, 1, 9]
def baseStart_903520 : Nat := 118140960795 + 903520 * 2 ^ 59
def prefixEnd_903520 : Nat := 4983230072969 + 3 ^ 40 * 903520 * 2
def baseEnd_903520 : Nat := 17182964479644822501659

theorem tailTrace_903520 : CollatzResearch.WordTrace tailWord_903520 prefixEnd_903520 17182964479644822501659 := by
  unfold tailWord_903520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477040843354411887974007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21969387791139215850632009 16477040843354411887974007)
  ·
    refine ⟨24715561265031617831961011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477040843354411887974007 24715561265031617831961011)
    ·
      refine ⟨37073341897547426747941517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715561265031617831961011 37073341897547426747941517)
      ·
        refine ⟨13902503211580285030478069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37073341897547426747941517 13902503211580285030478069)
        ·
          refine ⟨1303359676085651721607319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13902503211580285030478069 1303359676085651721607319)
          ·
            refine ⟨1955039514128477582410979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303359676085651721607319 1955039514128477582410979)
            ·
              refine ⟨2932559271192716373616469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955039514128477582410979 2932559271192716373616469)
              ·
                refine ⟨17182964479644822501659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2932559271192716373616469 17182964479644822501659)
                ·
                  rfl

theorem cell23_903520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_903520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903520 prefixEnd_903520 := by exact prefixLift 903520
  have htrace : WordTrace (prefixWord ++ tailWord_903520) baseStart_903520 baseEnd_903520 := by
    simpa [prefixWord, tailWord_903520, baseEnd_903520] using wordTrace_append hprefix tailTrace_903520
  have hstable : (prefixWord ++ tailWord_903520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903520).length < 2 ^ (prefixWord ++ tailWord_903520).sum := by decide
  have hdescent : baseEnd_903520 < baseStart_903520 := by decide
  rcases family_descends (prefixWord ++ tailWord_903520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903547 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 3]
def baseStart_903547 : Nat := 118140960795 + 903547 * 2 ^ 59
def prefixEnd_903547 : Nat := 4983230072969 + 3 ^ 40 * 903547 * 2
def baseEnd_903547 : Nat := 463953904928081601907169

theorem tailTrace_903547 : CollatzResearch.WordTrace tailWord_903547 prefixEnd_903547 463953904928081601907169 := by
  unfold tailWord_903547
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955066457611007387180895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21970044305074004924787263 32955066457611007387180895)
  ·
    refine ⟨49432599686416511080771343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32955066457611007387180895 49432599686416511080771343)
    ·
      refine ⟨74148899529624766621157015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49432599686416511080771343 74148899529624766621157015)
      ·
        refine ⟨111223349294437149931735523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74148899529624766621157015 111223349294437149931735523)
        ·
          refine ⟨166835023941655724897603285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111223349294437149931735523 166835023941655724897603285)
          ·
            refine ⟨3910195873632556052287577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166835023941655724897603285 3910195873632556052287577)
            ·
              refine ⟨2932646905224417039215683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910195873632556052287577 2932646905224417039215683)
              ·
                refine ⟨4398970357836625558823525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2932646905224417039215683 4398970357836625558823525)
                ·
                  refine ⟨824806942094367292279411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4398970357836625558823525 824806942094367292279411)
                  ·
                    refine ⟨1237210413141550938419117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824806942094367292279411 1237210413141550938419117)
                    ·
                      refine ⟨463953904928081601907169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1237210413141550938419117 463953904928081601907169)
                      ·
                        rfl

theorem cell23_903547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 3].length) (baseStart_903547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903547 prefixEnd_903547 := by exact prefixLift 903547
  have htrace : WordTrace (prefixWord ++ tailWord_903547) baseStart_903547 baseEnd_903547 := by
    simpa [prefixWord, tailWord_903547, baseEnd_903547] using wordTrace_append hprefix tailTrace_903547
  have hstable : (prefixWord ++ tailWord_903547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903547).length < 2 ^ (prefixWord ++ tailWord_903547).sum := by decide
  have hdescent : baseEnd_903547 < baseStart_903547 := by decide
  rcases family_descends (prefixWord ++ tailWord_903547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903554 : List Nat := [3, 4, 2, 1, 2, 1, 2, 8]
def baseStart_903554 : Nat := 118140960795 + 903554 * 2 ^ 59
def prefixEnd_903554 : Nat := 4983230072969 + 3 ^ 40 * 903554 * 2
def baseEnd_903554 : Nat := 17183611084913447204431

theorem tailTrace_903554 : CollatzResearch.WordTrace tailWord_903554 prefixEnd_903554 17183611084913447204431 := by
  unfold tailWord_903554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8238830442146411895671429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21970214512390431721790477 8238830442146411895671429)
  ·
    refine ⟨1544780707902452230438393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8238830442146411895671429 1544780707902452230438393)
    ·
      refine ⟨1158585530926839172828795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544780707902452230438393 1158585530926839172828795)
      ·
        refine ⟨1737878296390258759243193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158585530926839172828795 1737878296390258759243193)
        ·
          refine ⟨1303408722292694069432395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1737878296390258759243193 1303408722292694069432395)
          ·
            refine ⟨1955113083439041104148593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303408722292694069432395 1955113083439041104148593)
            ·
              refine ⟨1466334812579280828111445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955113083439041104148593 1466334812579280828111445)
              ·
                refine ⟨17183611084913447204431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1466334812579280828111445 17183611084913447204431)
                ·
                  rfl

theorem cell23_903554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_903554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903554 prefixEnd_903554 := by exact prefixLift 903554
  have htrace : WordTrace (prefixWord ++ tailWord_903554) baseStart_903554 baseEnd_903554 := by
    simpa [prefixWord, tailWord_903554, baseEnd_903554] using wordTrace_append hprefix tailTrace_903554
  have hstable : (prefixWord ++ tailWord_903554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903554).length < 2 ^ (prefixWord ++ tailWord_903554).sum := by decide
  have hdescent : baseEnd_903554 < baseStart_903554 := by decide
  rcases family_descends (prefixWord ++ tailWord_903554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_903557 : Nat := 118140960795 + 903557 * 2 ^ 59
def prefixEnd_903557 : Nat := 4983230072969 + 3 ^ 40 * 903557 * 2
def baseEnd_903557 : Nat := 463959039734626562782123

theorem tailTrace_903557 : CollatzResearch.WordTrace tailWord_903557 prefixEnd_903557 463959039734626562782123 := by
  unfold tailWord_903557
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955431187574779095044925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21970287458383186063363283 32955431187574779095044925)
  ·
    refine ⟨12358286695340542160641847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32955431187574779095044925 12358286695340542160641847)
    ·
      refine ⟨18537430043010813240962771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358286695340542160641847 18537430043010813240962771)
      ·
        refine ⟨27806145064516219861444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18537430043010813240962771 27806145064516219861444157)
        ·
          refine ⟨10427304399193582448041559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27806145064516219861444157 10427304399193582448041559)
          ·
            refine ⟨15640956598790373672062339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427304399193582448041559 15640956598790373672062339)
            ·
              refine ⟨23461434898185560508093509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640956598790373672062339 23461434898185560508093509)
              ·
                refine ⟨4399019043409792595267533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23461434898185560508093509 4399019043409792595267533)
                ·
                  refine ⟨1649632141278672223225325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4399019043409792595267533 1649632141278672223225325)
                  ·
                    refine ⟨618612052979502083709497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1649632141278672223225325 618612052979502083709497)
                    ·
                      refine ⟨463959039734626562782123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618612052979502083709497 463959039734626562782123)
                      ·
                        rfl

theorem cell23_903557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_903557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903557 prefixEnd_903557 := by exact prefixLift 903557
  have htrace : WordTrace (prefixWord ++ tailWord_903557) baseStart_903557 baseEnd_903557 := by
    simpa [prefixWord, tailWord_903557, baseEnd_903557] using wordTrace_append hprefix tailTrace_903557
  have hstable : (prefixWord ++ tailWord_903557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903557).length < 2 ^ (prefixWord ++ tailWord_903557).sum := by decide
  have hdescent : baseEnd_903557 < baseStart_903557 := by decide
  rcases family_descends (prefixWord ++ tailWord_903557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903564 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_903564 : Nat := 118140960795 + 903564 * 2 ^ 59
def prefixEnd_903564 : Nat := 4983230072969 + 3 ^ 40 * 903564 * 2
def baseEnd_903564 : Nat := 463962634099208035394591

theorem tailTrace_903564 : CollatzResearch.WordTrace tailWord_903564 prefixEnd_903564 463962634099208035394591 := by
  unfold tailWord_903564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477843249274709645274873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21970457665699612860366497 16477843249274709645274873)
  ·
    refine ⟨12358382436956032233956155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16477843249274709645274873 12358382436956032233956155)
    ·
      refine ⟨18537573655434048350934233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358382436956032233956155 18537573655434048350934233)
      ·
        refine ⟨13903180241575536263200675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18537573655434048350934233 13903180241575536263200675)
        ·
          refine ⟨20854770362363304394801013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903180241575536263200675 20854770362363304394801013)
          ·
            refine ⟨1955134721471559787012595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20854770362363304394801013 1955134721471559787012595)
            ·
              refine ⟨2932702082207339680518893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955134721471559787012595 2932702082207339680518893)
              ·
                refine ⟨1099763280827752380194585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932702082207339680518893 1099763280827752380194585)
                ·
                  refine ⟨824822460620814285145939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1099763280827752380194585 824822460620814285145939)
                  ·
                    refine ⟨1237233690931221427718909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824822460620814285145939 1237233690931221427718909)
                    ·
                      refine ⟨463962634099208035394591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1237233690931221427718909 463962634099208035394591)
                      ·
                        rfl

theorem cell23_903564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_903564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903564 prefixEnd_903564 := by exact prefixLift 903564
  have htrace : WordTrace (prefixWord ++ tailWord_903564) baseStart_903564 baseEnd_903564 := by
    simpa [prefixWord, tailWord_903564, baseEnd_903564] using wordTrace_append hprefix tailTrace_903564
  have hstable : (prefixWord ++ tailWord_903564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903564).length < 2 ^ (prefixWord ++ tailWord_903564).sum := by decide
  have hdescent : baseEnd_903564 < baseStart_903564 := by decide
  rcases family_descends (prefixWord ++ tailWord_903564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903587 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 3, 4, 2]
def baseStart_903587 : Nat := 118140960795 + 903587 * 2 ^ 59
def prefixEnd_903587 : Nat := 4983230072969 + 3 ^ 40 * 903587 * 2
def baseEnd_903587 : Nat := 463974444154261445406985

theorem tailTrace_903587 : CollatzResearch.WordTrace tailWord_903587 prefixEnd_903587 463974444154261445406985 := by
  unfold tailWord_903587
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956525377466094218637015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21971016918310729479091343 32956525377466094218637015)
  ·
    refine ⟨49434788066199141327955523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32956525377466094218637015 49434788066199141327955523)
    ·
      refine ⟨74152182099298711991933285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49434788066199141327955523 74152182099298711991933285)
      ·
        refine ⟨13903534143618508498487491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74152182099298711991933285 13903534143618508498487491)
        ·
          refine ⟨20855301215427762747731237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903534143618508498487491 20855301215427762747731237)
          ·
            refine ⟨3910368977892705515199607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20855301215427762747731237 3910368977892705515199607)
            ·
              refine ⟨5865553466839058272799411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910368977892705515199607 5865553466839058272799411)
              ·
                refine ⟨8798330200258587409199117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865553466839058272799411 8798330200258587409199117)
                ·
                  refine ⟨3299373825096970278449669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8798330200258587409199117 3299373825096970278449669)
                  ·
                    refine ⟨618632592205681927209313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3299373825096970278449669 618632592205681927209313)
                    ·
                      refine ⟨463974444154261445406985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618632592205681927209313 463974444154261445406985)
                      ·
                        rfl

theorem cell23_903587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_903587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903587 prefixEnd_903587 := by exact prefixLift 903587
  have htrace : WordTrace (prefixWord ++ tailWord_903587) baseStart_903587 baseEnd_903587 := by
    simpa [prefixWord, tailWord_903587, baseEnd_903587] using wordTrace_append hprefix tailTrace_903587
  have hstable : (prefixWord ++ tailWord_903587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903587).length < 2 ^ (prefixWord ++ tailWord_903587).sum := by decide
  have hdescent : baseEnd_903587 < baseStart_903587 := by decide
  rcases family_descends (prefixWord ++ tailWord_903587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903744 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_903744 : Nat := 118140960795 + 903744 * 2 ^ 59
def prefixEnd_903744 : Nat := 4983230072969 + 3 ^ 40 * 903744 * 2
def baseEnd_903744 : Nat := 464055060617017331143763

theorem tailTrace_903744 : CollatzResearch.WordTrace tailWord_903744 prefixEnd_903744 464055060617017331143763 := by
  unfold tailWord_903744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481125818948655016051143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21974834425264873354734857 16481125818948655016051143)
  ·
    refine ⟨24721688728422982524076715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16481125818948655016051143 24721688728422982524076715)
    ·
      refine ⟨37082533092634473786115073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24721688728422982524076715 37082533092634473786115073)
      ·
        refine ⟨27811899819475855339586305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37082533092634473786115073 27811899819475855339586305)
        ·
          refine ⟨20858924864606891504689729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27811899819475855339586305 20858924864606891504689729)
          ·
            refine ⟨15644193648455168628517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20858924864606891504689729 15644193648455168628517297)
            ·
              refine ⟨11733145236341376471387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15644193648455168628517297 11733145236341376471387973)
              ·
                refine ⟨2199964731814008088385245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11733145236341376471387973 2199964731814008088385245)
                ·
                  refine ⟨824986774430253033144467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2199964731814008088385245 824986774430253033144467)
                  ·
                    refine ⟨1237480161645379549716701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 824986774430253033144467 1237480161645379549716701)
                    ·
                      refine ⟨464055060617017331143763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1237480161645379549716701 464055060617017331143763)
                      ·
                        rfl

theorem cell23_903744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_903744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903744 prefixEnd_903744 := by exact prefixLift 903744
  have htrace : WordTrace (prefixWord ++ tailWord_903744) baseStart_903744 baseEnd_903744 := by
    simpa [prefixWord, tailWord_903744, baseEnd_903744] using wordTrace_append hprefix tailTrace_903744
  have hstable : (prefixWord ++ tailWord_903744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903744).length < 2 ^ (prefixWord ++ tailWord_903744).sum := by decide
  have hdescent : baseEnd_903744 < baseStart_903744 := by decide
  rcases family_descends (prefixWord ++ tailWord_903744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903772 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_903772 : Nat := 118140960795 + 903772 * 2 ^ 59
def prefixEnd_903772 : Nat := 4983230072969 + 3 ^ 40 * 903772 * 2
def baseEnd_903772 : Nat := 154689812691781073864545

theorem tailTrace_903772 : CollatzResearch.WordTrace tailWord_903772 prefixEnd_903772 154689812691781073864545 := by
  unfold tailWord_903772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481636440897935407060785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21975515254530580542747713 16481636440897935407060785)
  ·
    refine ⟨12361227330673451555295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16481636440897935407060785 12361227330673451555295589)
    ·
      refine ⟨2317730124501272166617923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12361227330673451555295589 2317730124501272166617923)
      ·
        refine ⟨3476595186751908249926885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2317730124501272166617923 3476595186751908249926885)
        ·
          refine ⟨651861597515982796861291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3476595186751908249926885 651861597515982796861291)
          ·
            refine ⟨977792396273974195291937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651861597515982796861291 977792396273974195291937)
            ·
              refine ⟨733344297205480646468953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977792396273974195291937 733344297205480646468953)
              ·
                refine ⟨550008222904110484851715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733344297205480646468953 550008222904110484851715)
                ·
                  refine ⟨825012334356165727277573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550008222904110484851715 825012334356165727277573)
                  ·
                    refine ⟨154689812691781073864545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825012334356165727277573 154689812691781073864545)
                    ·
                      rfl

theorem cell23_903772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_903772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903772 prefixEnd_903772 := by exact prefixLift 903772
  have htrace : WordTrace (prefixWord ++ tailWord_903772) baseStart_903772 baseEnd_903772 := by
    simpa [prefixWord, tailWord_903772, baseEnd_903772] using wordTrace_append hprefix tailTrace_903772
  have hstable : (prefixWord ++ tailWord_903772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903772).length < 2 ^ (prefixWord ++ tailWord_903772).sum := by decide
  have hdescent : baseEnd_903772 < baseStart_903772 := by decide
  rcases family_descends (prefixWord ++ tailWord_903772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903801 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 5, 2, 2]
def baseStart_903801 : Nat := 118140960795 + 903801 * 2 ^ 59
def prefixEnd_903801 : Nat := 4983230072969 + 3 ^ 40 * 903801 * 2
def baseEnd_903801 : Nat := 464084329014323608131001

theorem tailTrace_903801 : CollatzResearch.WordTrace tailWord_903801 prefixEnd_903801 464084329014323608131001 := by
  unfold tailWord_903801
  simp only [CollatzResearch.WordTrace]
  refine ⟨32964330598690808766927257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21976220399127205844618171 32964330598690808766927257)
  ·
    refine ⟨24723247949018106575195443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32964330598690808766927257 24723247949018106575195443)
    ·
      refine ⟨37084871923527159862793165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24723247949018106575195443 37084871923527159862793165)
      ·
        refine ⟨13906826971322684948547437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37084871923527159862793165 13906826971322684948547437)
        ·
          refine ⟨5215060114246006855705289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13906826971322684948547437 5215060114246006855705289)
          ·
            refine ⟨3911295085684505141778967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5215060114246006855705289 3911295085684505141778967)
            ·
              refine ⟨5866942628526757712668451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3911295085684505141778967 5866942628526757712668451)
              ·
                refine ⟨8800413942790136569002677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5866942628526757712668451 8800413942790136569002677)
                ·
                  refine ⟨825038807136575303344001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8800413942790136569002677 825038807136575303344001)
                  ·
                    refine ⟨618779105352431477508001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825038807136575303344001 618779105352431477508001)
                    ·
                      refine ⟨464084329014323608131001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618779105352431477508001 464084329014323608131001)
                      ·
                        rfl

theorem cell23_903801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_903801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903801 prefixEnd_903801 := by exact prefixLift 903801
  have htrace : WordTrace (prefixWord ++ tailWord_903801) baseStart_903801 baseEnd_903801 := by
    simpa [prefixWord, tailWord_903801, baseEnd_903801] using wordTrace_append hprefix tailTrace_903801
  have hstable : (prefixWord ++ tailWord_903801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903801).length < 2 ^ (prefixWord ++ tailWord_903801).sum := by decide
  have hdescent : baseEnd_903801 < baseStart_903801 := by decide
  rcases family_descends (prefixWord ++ tailWord_903801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903804 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_903804 : Nat := 118140960795 + 903804 * 2 ^ 59
def prefixEnd_903804 : Nat := 4983230072969 + 3 ^ 40 * 903804 * 2
def baseEnd_903804 : Nat := 464085869456287096393487

theorem tailTrace_903804 : CollatzResearch.WordTrace tailWord_903804 prefixEnd_903804 464085869456287096393487 := by
  unfold tailWord_903804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482220008839970139643233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21976293345119960186190977 16482220008839970139643233)
  ·
    refine ⟨12361665006629977604732425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16482220008839970139643233 12361665006629977604732425)
    ·
      refine ⟨9271248754972483203549319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12361665006629977604732425 9271248754972483203549319)
      ·
        refine ⟨13906873132458724805323979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271248754972483203549319 13906873132458724805323979)
        ·
          refine ⟨20860309698688087207985969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13906873132458724805323979 20860309698688087207985969)
          ·
            refine ⟨15645232274016065405989477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20860309698688087207985969 15645232274016065405989477)
            ·
              refine ⟨2933481051378012263623027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15645232274016065405989477 2933481051378012263623027)
              ·
                refine ⟨4400221577067018395434541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2933481051378012263623027 4400221577067018395434541)
                ·
                  refine ⟨1650083091400131898287953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4400221577067018395434541 1650083091400131898287953)
                  ·
                    refine ⟨1237562318550098923715965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1650083091400131898287953 1237562318550098923715965)
                    ·
                      refine ⟨464085869456287096393487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1237562318550098923715965 464085869456287096393487)
                      ·
                        rfl

theorem cell23_903804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_903804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903804 prefixEnd_903804 := by exact prefixLift 903804
  have htrace : WordTrace (prefixWord ++ tailWord_903804) baseStart_903804 baseEnd_903804 := by
    simpa [prefixWord, tailWord_903804, baseEnd_903804] using wordTrace_append hprefix tailTrace_903804
  have hstable : (prefixWord ++ tailWord_903804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903804).length < 2 ^ (prefixWord ++ tailWord_903804).sum := by decide
  have hdescent : baseEnd_903804 < baseStart_903804 := by decide
  rcases family_descends (prefixWord ++ tailWord_903804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903805 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_903805 : Nat := 118140960795 + 903805 * 2 ^ 59
def prefixEnd_903805 : Nat := 4983230072969 + 3 ^ 40 * 903805 * 2
def baseEnd_903805 : Nat := 464086382936941592480983

theorem tailTrace_903805 : CollatzResearch.WordTrace tailWord_903805 prefixEnd_903805 464086382936941592480983 := by
  unfold tailWord_903805
  simp only [CollatzResearch.WordTrace]
  refine ⟨32964476490676317450072869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21976317660450878300048579 32964476490676317450072869)
  ·
    refine ⟨6180839342001809521888663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32964476490676317450072869 6180839342001809521888663)
    ·
      refine ⟨9271259013002714282832995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180839342001809521888663 9271259013002714282832995)
      ·
        refine ⟨13906888519504071424249493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9271259013002714282832995 13906888519504071424249493)
        ·
          refine ⟨651885399351753348011695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13906888519504071424249493 651885399351753348011695)
          ·
            refine ⟨977828099027630022017543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651885399351753348011695 977828099027630022017543)
            ·
              refine ⟨1466742148541445033026315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977828099027630022017543 1466742148541445033026315)
              ·
                refine ⟨2200113222812167549539473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466742148541445033026315 2200113222812167549539473)
                ·
                  refine ⟨1650084917109125662154605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200113222812167549539473 1650084917109125662154605)
                  ·
                    refine ⟨618781843915922123307977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650084917109125662154605 618781843915922123307977)
                    ·
                      refine ⟨464086382936941592480983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618781843915922123307977 464086382936941592480983)
                      ·
                        rfl

theorem cell23_903805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_903805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903805 prefixEnd_903805 := by exact prefixLift 903805
  have htrace : WordTrace (prefixWord ++ tailWord_903805) baseStart_903805 baseEnd_903805 := by
    simpa [prefixWord, tailWord_903805, baseEnd_903805] using wordTrace_append hprefix tailTrace_903805
  have hstable : (prefixWord ++ tailWord_903805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903805).length < 2 ^ (prefixWord ++ tailWord_903805).sum := by decide
  have hdescent : baseEnd_903805 < baseStart_903805 := by decide
  rcases family_descends (prefixWord ++ tailWord_903805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903828 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_903828 : Nat := 118140960795 + 903828 * 2 ^ 59
def prefixEnd_903828 : Nat := 4983230072969 + 3 ^ 40 * 903828 * 2
def baseEnd_903828 : Nat := 154699397663998334164459

theorem tailTrace_903828 : CollatzResearch.WordTrace tailWord_903828 prefixEnd_903828 154699397663998334164459 := by
  unfold tailWord_903828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16482657684796496189080069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21976876913061994918773425 16482657684796496189080069)
  ·
    refine ⟨3090498315899343035452513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16482657684796496189080069 3090498315899343035452513)
    ·
      refine ⟨2317873736924507276589385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3090498315899343035452513 2317873736924507276589385)
      ·
        refine ⟨1738405302693380457442039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317873736924507276589385 1738405302693380457442039)
        ·
          refine ⟨2607607954040070686163059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738405302693380457442039 2607607954040070686163059)
          ·
            refine ⟨3911411931060106029244589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2607607954040070686163059 3911411931060106029244589)
            ·
              refine ⟨1466779474147539760966721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3911411931060106029244589 1466779474147539760966721)
              ·
                refine ⟨1100084605610654820725041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466779474147539760966721 1100084605610654820725041)
                ·
                  refine ⟨825063454207991115543781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100084605610654820725041 825063454207991115543781)
                  ·
                    refine ⟨154699397663998334164459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825063454207991115543781 154699397663998334164459)
                    ·
                      rfl

theorem cell23_903828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_903828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903828 prefixEnd_903828 := by exact prefixLift 903828
  have htrace : WordTrace (prefixWord ++ tailWord_903828) baseStart_903828 baseEnd_903828 := by
    simpa [prefixWord, tailWord_903828, baseEnd_903828] using wordTrace_append hprefix tailTrace_903828
  have hstable : (prefixWord ++ tailWord_903828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903828).length < 2 ^ (prefixWord ++ tailWord_903828).sum := by decide
  have hdescent : baseEnd_903828 < baseStart_903828 := by decide
  rcases family_descends (prefixWord ++ tailWord_903828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903837 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_903837 : Nat := 118140960795 + 903837 * 2 ^ 59
def prefixEnd_903837 : Nat := 4983230072969 + 3 ^ 40 * 903837 * 2
def baseEnd_903837 : Nat := 154700938105961822426945

theorem tailTrace_903837 : CollatzResearch.WordTrace tailWord_903837 prefixEnd_903837 154700938105961822426945 := by
  unfold tailWord_903837
  simp only [CollatzResearch.WordTrace]
  refine ⟨32965643626560386915237765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21977095751040257943491843 32965643626560386915237765)
  ·
    refine ⟨6181058179980072546607081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32965643626560386915237765 6181058179980072546607081)
    ·
      refine ⟨4635793634985054409955311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6181058179980072546607081 4635793634985054409955311)
      ·
        refine ⟨6953690452477581614932967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4635793634985054409955311 6953690452477581614932967)
        ·
          refine ⟨10430535678716372422399451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6953690452477581614932967 10430535678716372422399451)
          ·
            refine ⟨15645803518074558633599177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10430535678716372422399451 15645803518074558633599177)
            ·
              refine ⟨11734352638555918975199383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15645803518074558633599177 11734352638555918975199383)
              ·
                refine ⟨17601528957833878462799075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11734352638555918975199383 17601528957833878462799075)
                ·
                  refine ⟨26402293436750817694198613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17601528957833878462799075 26402293436750817694198613)
                  ·
                    refine ⟨154700938105961822426945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26402293436750817694198613 154700938105961822426945)
                    ·
                      rfl

theorem cell23_903837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_903837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903837 prefixEnd_903837 := by exact prefixLift 903837
  have htrace : WordTrace (prefixWord ++ tailWord_903837) baseStart_903837 baseEnd_903837 := by
    simpa [prefixWord, tailWord_903837, baseEnd_903837] using wordTrace_append hprefix tailTrace_903837
  have hstable : (prefixWord ++ tailWord_903837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903837).length < 2 ^ (prefixWord ++ tailWord_903837).sum := by decide
  have hdescent : baseEnd_903837 < baseStart_903837 := by decide
  rcases family_descends (prefixWord ++ tailWord_903837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903912 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_903912 : Nat := 118140960795 + 903912 * 2 ^ 59
def prefixEnd_903912 : Nat := 4983230072969 + 3 ^ 40 * 903912 * 2
def baseEnd_903912 : Nat := 464141325366972673842991

theorem tailTrace_903912 : CollatzResearch.WordTrace tailWord_903912 prefixEnd_903912 464141325366972673842991 := by
  unfold tailWord_903912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484189550644337362108995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21978919400859116482811993 16484189550644337362108995)
  ·
    refine ⟨24726284325966506043163493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16484189550644337362108995 24726284325966506043163493)
    ·
      refine ⟨4636178311118719883093155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24726284325966506043163493 4636178311118719883093155)
      ·
        refine ⟨6954267466678079824639733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636178311118719883093155 6954267466678079824639733)
        ·
          refine ⟨651962575001069983559975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6954267466678079824639733 651962575001069983559975)
          ·
            refine ⟨977943862501604975339963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651962575001069983559975 977943862501604975339963)
            ·
              refine ⟨1466915793752407463009945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977943862501604975339963 1466915793752407463009945)
              ·
                refine ⟨1100186845314305597257459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1466915793752407463009945 1100186845314305597257459)
                ·
                  refine ⟨1650280267971458395886189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100186845314305597257459 1650280267971458395886189)
                  ·
                    refine ⟨618855100489296898457321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650280267971458395886189 618855100489296898457321)
                    ·
                      refine ⟨464141325366972673842991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618855100489296898457321 464141325366972673842991)
                      ·
                        rfl

theorem cell23_903912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_903912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903912 prefixEnd_903912 := by exact prefixLift 903912
  have htrace : WordTrace (prefixWord ++ tailWord_903912) baseStart_903912 baseEnd_903912 := by
    simpa [prefixWord, tailWord_903912, baseEnd_903912] using wordTrace_append hprefix tailTrace_903912
  have hstable : (prefixWord ++ tailWord_903912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903912).length < 2 ^ (prefixWord ++ tailWord_903912).sum := by decide
  have hdescent : baseEnd_903912 < baseStart_903912 := by decide
  rcases family_descends (prefixWord ++ tailWord_903912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903978 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_903978 : Nat := 118140960795 + 903978 * 2 ^ 59
def prefixEnd_903978 : Nat := 4983230072969 + 3 ^ 40 * 903978 * 2
def baseEnd_903978 : Nat := 154725071696723138539229

theorem tailTrace_903978 : CollatzResearch.WordTrace tailWord_903978 prefixEnd_903978 154725071696723138539229 := by
  unfold tailWord_903978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8242696579762391999030147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21980524212699711997413725 8242696579762391999030147)
  ·
    refine ⟨12364044869643587998545221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8242696579762391999030147 12364044869643587998545221)
    ·
      refine ⟨2318258413058172749727229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12364044869643587998545221 2318258413058172749727229)
      ·
        refine ⟨869346904896814781147711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2318258413058172749727229 869346904896814781147711)
        ·
          refine ⟨1304020357345222171721567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869346904896814781147711 1304020357345222171721567)
          ·
            refine ⟨1956030536017833257582351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304020357345222171721567 1956030536017833257582351)
            ·
              refine ⟨2934045804026749886373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956030536017833257582351 2934045804026749886373527)
              ·
                refine ⟨4401068706040124829560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2934045804026749886373527 4401068706040124829560291)
                ·
                  refine ⟨6601603059060187244340437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4401068706040124829560291 6601603059060187244340437)
                  ·
                    refine ⟨154725071696723138539229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6601603059060187244340437 154725071696723138539229)
                    ·
                      rfl

theorem cell23_903978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_903978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_903978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_903978 prefixEnd_903978 := by exact prefixLift 903978
  have htrace : WordTrace (prefixWord ++ tailWord_903978) baseStart_903978 baseEnd_903978 := by
    simpa [prefixWord, tailWord_903978, baseEnd_903978] using wordTrace_append hprefix tailTrace_903978
  have hstable : (prefixWord ++ tailWord_903978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903978).length < 2 ^ (prefixWord ++ tailWord_903978).sum := by decide
  have hdescent : baseEnd_903978 < baseStart_903978 := by decide
  rcases family_descends (prefixWord ++ tailWord_903978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904008 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 1, 4]
def baseStart_904008 : Nat := 118140960795 + 904008 * 2 ^ 59
def prefixEnd_904008 : Nat := 4983230072969 + 3 ^ 40 * 904008 * 2
def baseEnd_904008 : Nat := 154730206503268099414183

theorem tailTrace_904008 : CollatzResearch.WordTrace tailWord_904008 prefixEnd_904008 154730206503268099414183 := by
  unfold tailWord_904008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16485940254470441559856339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21981253672627255413141785 16485940254470441559856339)
  ·
    refine ⟨24728910381705662339784509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16485940254470441559856339 24728910381705662339784509)
    ·
      refine ⟨9273341393139623377419191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24728910381705662339784509 9273341393139623377419191)
      ·
        refine ⟨13910012089709435066128787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9273341393139623377419191 13910012089709435066128787)
        ·
          refine ⟨20865018134564152599193181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13910012089709435066128787 20865018134564152599193181)
          ·
            refine ⟨7824381800461557224697443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20865018134564152599193181 7824381800461557224697443)
            ·
              refine ⟨11736572700692335837046165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7824381800461557224697443 11736572700692335837046165)
              ·
                refine ⟨550151845344953242361539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11736572700692335837046165 550151845344953242361539)
                ·
                  refine ⟨825227768017429863542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550151845344953242361539 825227768017429863542309)
                  ·
                    refine ⟨154730206503268099414183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825227768017429863542309 154730206503268099414183)
                    ·
                      rfl

theorem cell23_904008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_904008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904008 prefixEnd_904008 := by exact prefixLift 904008
  have htrace : WordTrace (prefixWord ++ tailWord_904008) baseStart_904008 baseEnd_904008 := by
    simpa [prefixWord, tailWord_904008, baseEnd_904008] using wordTrace_append hprefix tailTrace_904008
  have hstable : (prefixWord ++ tailWord_904008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904008).length < 2 ^ (prefixWord ++ tailWord_904008).sum := by decide
  have hdescent : baseEnd_904008 < baseStart_904008 := by decide
  rcases family_descends (prefixWord ++ tailWord_904008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904051 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 1, 5]
def baseStart_904051 : Nat := 118140960795 + 904051 * 2 ^ 59
def prefixEnd_904051 : Nat := 4983230072969 + 3 ^ 40 * 904051 * 2
def baseEnd_904051 : Nat := 154737566392649210001617

theorem tailTrace_904051 : CollatzResearch.WordTrace tailWord_904051 prefixEnd_904051 154737566392649210001617 := by
  unfold tailWord_904051
  simp only [CollatzResearch.WordTrace]
  refine ⟨32973448847785101463528007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21982299231856734309018671 32973448847785101463528007)
  ·
    refine ⟨49460173271677652195292011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32973448847785101463528007 49460173271677652195292011)
    ·
      refine ⟨74190259907516478292938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49460173271677652195292011 74190259907516478292938017)
      ·
        refine ⟨55642694930637358719703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74190259907516478292938017 55642694930637358719703513)
        ·
          refine ⟨41732021197978019039777635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55642694930637358719703513 41732021197978019039777635)
          ·
            refine ⟨62598031796967028559666453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41732021197978019039777635 62598031796967028559666453)
            ·
              refine ⟨2934282740482829463734365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62598031796967028559666453 2934282740482829463734365)
              ·
                refine ⟨1100356027681061048900387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2934282740482829463734365 1100356027681061048900387)
                ·
                  refine ⟨1650534041521591573350581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100356027681061048900387 1650534041521591573350581)
                  ·
                    refine ⟨154737566392649210001617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1650534041521591573350581 154737566392649210001617)
                    ·
                      rfl

theorem cell23_904051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 5].length) (baseStart_904051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904051 prefixEnd_904051 := by exact prefixLift 904051
  have htrace : WordTrace (prefixWord ++ tailWord_904051) baseStart_904051 baseEnd_904051 := by
    simpa [prefixWord, tailWord_904051, baseEnd_904051] using wordTrace_append hprefix tailTrace_904051
  have hstable : (prefixWord ++ tailWord_904051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904051).length < 2 ^ (prefixWord ++ tailWord_904051).sum := by decide
  have hdescent : baseEnd_904051 < baseStart_904051 := by decide
  rcases family_descends (prefixWord ++ tailWord_904051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904064 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_904064 : Nat := 118140960795 + 904064 * 2 ^ 59
def prefixEnd_904064 : Nat := 4983230072969 + 3 ^ 40 * 904064 * 2
def baseEnd_904064 : Nat := 154739791475485359714097

theorem tailTrace_904064 : CollatzResearch.WordTrace tailWord_904064 prefixEnd_904064 154739791475485359714097 := by
  unfold tailWord_904064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16486961498369002341875623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21982615331158669789167497 16486961498369002341875623)
  ·
    refine ⟨24730442247553503512813435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16486961498369002341875623 24730442247553503512813435)
    ·
      refine ⟨37095663371330255269220153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24730442247553503512813435 37095663371330255269220153)
      ·
        refine ⟨27821747528497691451915115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37095663371330255269220153 27821747528497691451915115)
        ·
          refine ⟨41732621292746537177872673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27821747528497691451915115 41732621292746537177872673)
          ·
            refine ⟨31299465969559902883404505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41732621292746537177872673 31299465969559902883404505)
            ·
              refine ⟨23474599477169927162553379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31299465969559902883404505 23474599477169927162553379)
              ·
                refine ⟨35211899215754890743830069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23474599477169927162553379 35211899215754890743830069)
                ·
                  refine ⟨3301115551477021007234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35211899215754890743830069 3301115551477021007234069)
                  ·
                    refine ⟨154739791475485359714097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3301115551477021007234069 154739791475485359714097)
                    ·
                      rfl

theorem cell23_904064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_904064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904064 prefixEnd_904064 := by exact prefixLift 904064
  have htrace : WordTrace (prefixWord ++ tailWord_904064) baseStart_904064 baseEnd_904064 := by
    simpa [prefixWord, tailWord_904064, baseEnd_904064] using wordTrace_append hprefix tailTrace_904064
  have hstable : (prefixWord ++ tailWord_904064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904064).length < 2 ^ (prefixWord ++ tailWord_904064).sum := by decide
  have hdescent : baseEnd_904064 < baseStart_904064 := by decide
  rcases family_descends (prefixWord ++ tailWord_904064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904092 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_904092 : Nat := 118140960795 + 904092 * 2 ^ 59
def prefixEnd_904092 : Nat := 4983230072969 + 3 ^ 40 * 904092 * 2
def baseEnd_904092 : Nat := 464233751884781969592163

theorem tailTrace_904092 : CollatzResearch.WordTrace tailWord_904092 prefixEnd_904092 464233751884781969592163 := by
  unfold tailWord_904092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16487472120318282732885265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21983296160424376977180353 16487472120318282732885265)
  ·
    refine ⟨12365604090238712049663949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16487472120318282732885265 12365604090238712049663949)
    ·
      refine ⟨4637101533839517018623981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12365604090238712049663949 4637101533839517018623981)
      ·
        refine ⟨1738913075189818881983993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4637101533839517018623981 1738913075189818881983993)
        ·
          refine ⟨1304184806392364161487995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1738913075189818881983993 1304184806392364161487995)
          ·
            refine ⟨1956277209588546242231993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304184806392364161487995 1956277209588546242231993)
            ·
              refine ⟨1467207907191409681673995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956277209588546242231993 1467207907191409681673995)
              ·
                refine ⟨2200811860787114522510993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467207907191409681673995 2200811860787114522510993)
                ·
                  refine ⟨1650608895590335891883245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2200811860787114522510993 1650608895590335891883245)
                  ·
                    refine ⟨618978335846375959456217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1650608895590335891883245 618978335846375959456217)
                    ·
                      refine ⟨464233751884781969592163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618978335846375959456217 464233751884781969592163)
                      ·
                        rfl

theorem cell23_904092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_904092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904092 prefixEnd_904092 := by exact prefixLift 904092
  have htrace : WordTrace (prefixWord ++ tailWord_904092) baseStart_904092 baseEnd_904092 := by
    simpa [prefixWord, tailWord_904092, baseEnd_904092] using wordTrace_append hprefix tailTrace_904092
  have hstable : (prefixWord ++ tailWord_904092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904092).length < 2 ^ (prefixWord ++ tailWord_904092).sum := by decide
  have hdescent : baseEnd_904092 < baseStart_904092 := by decide
  rcases family_descends (prefixWord ++ tailWord_904092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904098 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_904098 : Nat := 118140960795 + 904098 * 2 ^ 59
def prefixEnd_904098 : Nat := 4983230072969 + 3 ^ 40 * 904098 * 2
def baseEnd_904098 : Nat := 154745610922902982039045

theorem tailTrace_904098 : CollatzResearch.WordTrace tailWord_904098 prefixEnd_904098 154745610922902982039045 := by
  unfold tailWord_904098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8243790769653707122622237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21983442052409885660325965 8243790769653707122622237)
  ·
    refine ⟨3091421538620140170983339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8243790769653707122622237 3091421538620140170983339)
    ·
      refine ⟨4637132307930210256475009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091421538620140170983339 4637132307930210256475009)
      ·
        refine ⟨3477849230947657692356257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4637132307930210256475009 3477849230947657692356257)
        ·
          refine ⟨2608386923210743269267193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3477849230947657692356257 2608386923210743269267193)
          ·
            refine ⟨1956290192408057451950395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608386923210743269267193 1956290192408057451950395)
            ·
              refine ⟨2934435288612086177925593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956290192408057451950395 2934435288612086177925593)
              ·
                refine ⟨2200826466459064633444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2934435288612086177925593 2200826466459064633444195)
                ·
                  refine ⟨3301239699688596950166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200826466459064633444195 3301239699688596950166293)
                  ·
                    refine ⟨154745610922902982039045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3301239699688596950166293 154745610922902982039045)
                    ·
                      rfl

theorem cell23_904098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_904098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904098 prefixEnd_904098 := by exact prefixLift 904098
  have htrace : WordTrace (prefixWord ++ tailWord_904098) baseStart_904098 baseEnd_904098 := by
    simpa [prefixWord, tailWord_904098, baseEnd_904098] using wordTrace_append hprefix tailTrace_904098
  have hstable : (prefixWord ++ tailWord_904098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904098).length < 2 ^ (prefixWord ++ tailWord_904098).sum := by decide
  have hdescent : baseEnd_904098 < baseStart_904098 := by decide
  rcases family_descends (prefixWord ++ tailWord_904098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904116 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_904116 : Nat := 118140960795 + 904116 * 2 ^ 59
def prefixEnd_904116 : Nat := 4983230072969 + 3 ^ 40 * 904116 * 2
def baseEnd_904116 : Nat := 464246075420489875692053

theorem tailTrace_904116 : CollatzResearch.WordTrace tailWord_904116 prefixEnd_904116 464246075420489875692053 := by
  unfold tailWord_904116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16487909796274808782322101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21983879728366411709762801 16487909796274808782322101)
  ·
    refine ⟨1545741543400763323342697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16487909796274808782322101 1545741543400763323342697)
    ·
      refine ⟨1159306157550572492507023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1545741543400763323342697 1159306157550572492507023)
      ·
        refine ⟨1738959236325858738760535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159306157550572492507023 1738959236325858738760535)
        ·
          refine ⟨2608438854488788108140803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738959236325858738760535 2608438854488788108140803)
          ·
            refine ⟨3912658281733182162211205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608438854488788108140803 3912658281733182162211205)
            ·
              refine ⟨733623427824971655414601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3912658281733182162211205 733623427824971655414601)
              ·
                refine ⟨550217570868728741560951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733623427824971655414601 550217570868728741560951)
                ·
                  refine ⟨825326356303093112341427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550217570868728741560951 825326356303093112341427)
                  ·
                    refine ⟨1237989534454639668512141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825326356303093112341427 1237989534454639668512141)
                    ·
                      refine ⟨464246075420489875692053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1237989534454639668512141 464246075420489875692053)
                      ·
                        rfl

theorem cell23_904116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_904116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904116 prefixEnd_904116 := by exact prefixLift 904116
  have htrace : WordTrace (prefixWord ++ tailWord_904116) baseStart_904116 baseEnd_904116 := by
    simpa [prefixWord, tailWord_904116, baseEnd_904116] using wordTrace_append hprefix tailTrace_904116
  have hstable : (prefixWord ++ tailWord_904116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904116).length < 2 ^ (prefixWord ++ tailWord_904116).sum := by decide
  have hdescent : baseEnd_904116 < baseStart_904116 := by decide
  rcases family_descends (prefixWord ++ tailWord_904116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904122 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_904122 : Nat := 118140960795 + 904122 * 2 ^ 59
def prefixEnd_904122 : Nat := 4983230072969 + 3 ^ 40 * 904122 * 2
def baseEnd_904122 : Nat := 464249156304416852217025

theorem tailTrace_904122 : CollatzResearch.WordTrace tailWord_904122 prefixEnd_904122 464249156304416852217025 := by
  unfold tailWord_904122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244009607631970147340655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21984025620351920392908413 8244009607631970147340655)
  ·
    refine ⟨12366014411447955221010983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8244009607631970147340655 12366014411447955221010983)
    ·
      refine ⟨18549021617171932831516475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12366014411447955221010983 18549021617171932831516475)
      ·
        refine ⟨27823532425757899247274713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18549021617171932831516475 27823532425757899247274713)
        ·
          refine ⟨20867649319318424435456035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27823532425757899247274713 20867649319318424435456035)
          ·
            refine ⟨31301473978977636653184053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20867649319318424435456035 31301473978977636653184053)
            ·
              refine ⟨2934513185529153436236005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31301473978977636653184053 2934513185529153436236005)
              ·
                refine ⟨550221222286716269294251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2934513185529153436236005 550221222286716269294251)
                ·
                  refine ⟨825331833430074403941377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 550221222286716269294251 825331833430074403941377)
                  ·
                    refine ⟨618998875072555802956033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825331833430074403941377 618998875072555802956033)
                    ·
                      refine ⟨464249156304416852217025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 618998875072555802956033 464249156304416852217025)
                      ·
                        rfl

theorem cell23_904122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_904122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904122 prefixEnd_904122 := by exact prefixLift 904122
  have htrace : WordTrace (prefixWord ++ tailWord_904122) baseStart_904122 baseEnd_904122 := by
    simpa [prefixWord, tailWord_904122, baseEnd_904122] using wordTrace_append hprefix tailTrace_904122
  have hstable : (prefixWord ++ tailWord_904122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904122).length < 2 ^ (prefixWord ++ tailWord_904122).sum := by decide
  have hdescent : baseEnd_904122 < baseStart_904122 := by decide
  rcases family_descends (prefixWord ++ tailWord_904122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904138 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_904138 : Nat := 118140960795 + 904138 * 2 ^ 59
def prefixEnd_904138 : Nat := 4983230072969 + 3 ^ 40 * 904138 * 2
def baseEnd_904138 : Nat := 464257371994888789616951

theorem tailTrace_904138 : CollatzResearch.WordTrace tailWord_904138 prefixEnd_904138 464257371994888789616951 := by
  unfold tailWord_904138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8244155499617478830486267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21984414665646610214630045 8244155499617478830486267)
  ·
    refine ⟨12366233249426218245729401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8244155499617478830486267 12366233249426218245729401)
    ·
      refine ⟨9274674937069663684297051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12366233249426218245729401 9274674937069663684297051)
      ·
        refine ⟨13912012405604495526445577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9274674937069663684297051 13912012405604495526445577)
        ·
          refine ⟨10434009304203371644834183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13912012405604495526445577 10434009304203371644834183)
          ·
            refine ⟨15651013956305057467251275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10434009304203371644834183 15651013956305057467251275)
            ·
              refine ⟨23476520934457586200876913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15651013956305057467251275 23476520934457586200876913)
              ·
                refine ⟨17607390700843189650657685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23476520934457586200876913 17607390700843189650657685)
                ·
                  refine ⟨825346439102024514874579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17607390700843189650657685 825346439102024514874579)
                  ·
                    refine ⟨1238019658653036772311869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825346439102024514874579 1238019658653036772311869)
                    ·
                      refine ⟨464257371994888789616951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238019658653036772311869 464257371994888789616951)
                      ·
                        rfl

theorem cell23_904138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_904138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904138 prefixEnd_904138 := by exact prefixLift 904138
  have htrace : WordTrace (prefixWord ++ tailWord_904138) baseStart_904138 baseEnd_904138 := by
    simpa [prefixWord, tailWord_904138, baseEnd_904138] using wordTrace_append hprefix tailTrace_904138
  have hstable : (prefixWord ++ tailWord_904138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904138).length < 2 ^ (prefixWord ++ tailWord_904138).sum := by decide
  have hdescent : baseEnd_904138 < baseStart_904138 := by decide
  rcases family_descends (prefixWord ++ tailWord_904138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904159 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 1, 2, 3]
def baseStart_904159 : Nat := 118140960795 + 904159 * 2 ^ 59
def prefixEnd_904159 : Nat := 4983230072969 + 3 ^ 40 * 904159 * 2
def baseEnd_904159 : Nat := 464268155088633207454355

theorem tailTrace_904159 : CollatzResearch.WordTrace tailWord_904159 prefixEnd_904159 464268155088633207454355 := by
  unfold tailWord_904159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977387931393835908459531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21984925287595890605639687 32977387931393835908459531)
  ·
    refine ⟨49466081897090753862689297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977387931393835908459531 49466081897090753862689297)
    ·
      refine ⟨37099561422818065397016973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49466081897090753862689297 37099561422818065397016973)
      ·
        refine ⟨13912335533556774523881365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37099561422818065397016973 13912335533556774523881365)
        ·
          refine ⟨652140728135473805806939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13912335533556774523881365 652140728135473805806939)
          ·
            refine ⟨978211092203210708710409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652140728135473805806939 978211092203210708710409)
            ·
              refine ⟨733658319152408031532807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 978211092203210708710409 733658319152408031532807)
              ·
                refine ⟨1100487478728612047299211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733658319152408031532807 1100487478728612047299211)
                ·
                  refine ⟨1650731218092918070948817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100487478728612047299211 1650731218092918070948817)
                  ·
                    refine ⟨1238048413569688553211613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1650731218092918070948817 1238048413569688553211613)
                    ·
                      refine ⟨464268155088633207454355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238048413569688553211613 464268155088633207454355)
                      ·
                        rfl

theorem cell23_904159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_904159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904159 prefixEnd_904159 := by exact prefixLift 904159
  have htrace : WordTrace (prefixWord ++ tailWord_904159) baseStart_904159 baseEnd_904159 := by
    simpa [prefixWord, tailWord_904159, baseEnd_904159] using wordTrace_append hprefix tailTrace_904159
  have hstable : (prefixWord ++ tailWord_904159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904159).length < 2 ^ (prefixWord ++ tailWord_904159).sum := by decide
  have hdescent : baseEnd_904159 < baseStart_904159 := by decide
  rcases family_descends (prefixWord ++ tailWord_904159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904235 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 5]
def baseStart_904235 : Nat := 118140960795 + 904235 * 2 ^ 59
def prefixEnd_904235 : Nat := 4983230072969 + 3 ^ 40 * 904235 * 2
def baseEnd_904235 : Nat := 51589686624263878900445

theorem tailTrace_904235 : CollatzResearch.WordTrace tailWord_904235 prefixEnd_904235 51589686624263878900445 := by
  unfold tailWord_904235
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980159879118500888226159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21986773252745667258817439 32980159879118500888226159)
  ·
    refine ⟨49470239818677751332339239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32980159879118500888226159 49470239818677751332339239)
    ·
      refine ⟨74205359728016626998508859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49470239818677751332339239 74205359728016626998508859)
      ·
        refine ⟨111308039592024940497763289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74205359728016626998508859 111308039592024940497763289)
        ·
          refine ⟨83481029694018705373322467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111308039592024940497763289 83481029694018705373322467)
          ·
            refine ⟨125221544541028058059983701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83481029694018705373322467 125221544541028058059983701)
            ·
              refine ⟨733719987545086277695217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 125221544541028058059983701 733719987545086277695217)
              ·
                refine ⟨550289990658814708271413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733719987545086277695217 550289990658814708271413)
                ·
                  refine ⟨51589686624263878900445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 550289990658814708271413 51589686624263878900445)
                  ·
                    rfl

theorem cell23_904235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 5].length) (baseStart_904235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904235 prefixEnd_904235 := by exact prefixLift 904235
  have htrace : WordTrace (prefixWord ++ tailWord_904235) baseStart_904235 baseEnd_904235 := by
    simpa [prefixWord, tailWord_904235, baseEnd_904235] using wordTrace_append hprefix tailTrace_904235
  have hstable : (prefixWord ++ tailWord_904235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904235).length < 2 ^ (prefixWord ++ tailWord_904235).sum := by decide
  have hdescent : baseEnd_904235 < baseStart_904235 := by decide
  rcases family_descends (prefixWord ++ tailWord_904235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904246 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_904246 : Nat := 118140960795 + 904246 * 2 ^ 59
def prefixEnd_904246 : Nat := 4983230072969 + 3 ^ 40 * 904246 * 2
def baseEnd_904246 : Nat := 464312827905574367066455

theorem tailTrace_904246 : CollatzResearch.WordTrace tailWord_904246 prefixEnd_904246 464312827905574367066455 := by
  unfold tailWord_904246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061285067629915610429787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21987040721385766511251061 2061285067629915610429787)
  ·
    refine ⟨3091927601444873415644681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2061285067629915610429787 3091927601444873415644681)
    ·
      refine ⟨2318945701083655061733511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3091927601444873415644681 2318945701083655061733511)
      ·
        refine ⟨3478418551625482592600267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2318945701083655061733511 3478418551625482592600267)
        ·
          refine ⟨5217627827438223888900401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478418551625482592600267 5217627827438223888900401)
          ·
            refine ⟨3913220870578667916675301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217627827438223888900401 3913220870578667916675301)
            ·
              refine ⟨733728913233500234376619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3913220870578667916675301 733728913233500234376619)
              ·
                refine ⟨1100593369850250351564929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733728913233500234376619 1100593369850250351564929)
                ·
                  refine ⟨825445027387687763673697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100593369850250351564929 825445027387687763673697)
                  ·
                    refine ⟨619083770540765822755273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825445027387687763673697 619083770540765822755273)
                    ·
                      refine ⟨464312827905574367066455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619083770540765822755273 464312827905574367066455)
                      ·
                        rfl

theorem cell23_904246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_904246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904246 prefixEnd_904246 := by exact prefixLift 904246
  have htrace : WordTrace (prefixWord ++ tailWord_904246) baseStart_904246 baseEnd_904246 := by
    simpa [prefixWord, tailWord_904246, baseEnd_904246] using wordTrace_append hprefix tailTrace_904246
  have hstable : (prefixWord ++ tailWord_904246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904246).length < 2 ^ (prefixWord ++ tailWord_904246).sum := by decide
  have hdescent : baseEnd_904246 < baseStart_904246 := by decide
  rcases family_descends (prefixWord ++ tailWord_904246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904261 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_904261 : Nat := 118140960795 + 904261 * 2 ^ 59
def prefixEnd_904261 : Nat := 4983230072969 + 3 ^ 40 * 904261 * 2
def baseEnd_904261 : Nat := 154773510038463936126295

theorem tailTrace_904261 : CollatzResearch.WordTrace tailWord_904261 prefixEnd_904261 154773510038463936126295 := by
  unfold tailWord_904261
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981108177024307328672637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21987405451349538219115091 32981108177024307328672637)
  ·
    refine ⟨12367915566384115248252239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32981108177024307328672637 12367915566384115248252239)
    ·
      refine ⟨18551873349576172872378359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12367915566384115248252239 18551873349576172872378359)
      ·
        refine ⟨27827810024364259308567539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18551873349576172872378359 27827810024364259308567539)
        ·
          refine ⟨41741715036546388962851309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27827810024364259308567539 41741715036546388962851309)
          ·
            refine ⟨15653143138704895861069241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41741715036546388962851309 15653143138704895861069241)
            ·
              refine ⟨11739857354028671895801931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15653143138704895861069241 11739857354028671895801931)
              ·
                refine ⟨17609786031043007843702897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11739857354028671895801931 17609786031043007843702897)
                ·
                  refine ⟨13207339523282255882777173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17609786031043007843702897 13207339523282255882777173)
                  ·
                    refine ⟨154773510038463936126295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13207339523282255882777173 154773510038463936126295)
                    ·
                      rfl

theorem cell23_904261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_904261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904261 prefixEnd_904261 := by exact prefixLift 904261
  have htrace : WordTrace (prefixWord ++ tailWord_904261) baseStart_904261 baseEnd_904261 := by
    simpa [prefixWord, tailWord_904261, baseEnd_904261] using wordTrace_append hprefix tailTrace_904261
  have hstable : (prefixWord ++ tailWord_904261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904261).length < 2 ^ (prefixWord ++ tailWord_904261).sum := by decide
  have hdescent : baseEnd_904261 < baseStart_904261 := by decide
  rcases family_descends (prefixWord ++ tailWord_904261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904271 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_904271 : Nat := 118140960795 + 904271 * 2 ^ 59
def prefixEnd_904271 : Nat := 4983230072969 + 3 ^ 40 * 904271 * 2
def baseEnd_904271 : Nat := 464325664921936769253839

theorem tailTrace_904271 : CollatzResearch.WordTrace tailWord_904271 prefixEnd_904271 464325664921936769253839 := by
  unfold tailWord_904271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32981472906988079036536667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21987648604658719357691111 32981472906988079036536667)
  ·
    refine ⟨49472209360482118554805001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32981472906988079036536667 49472209360482118554805001)
    ·
      refine ⟨37104157020361588916103751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49472209360482118554805001 37104157020361588916103751)
      ·
        refine ⟨55656235530542383374155627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37104157020361588916103751 55656235530542383374155627)
        ·
          refine ⟨83484353295813575061233441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55656235530542383374155627 83484353295813575061233441)
          ·
            refine ⟨62613264971860181295925081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83484353295813575061233441 62613264971860181295925081)
            ·
              refine ⟨46959948728895135971943811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62613264971860181295925081 46959948728895135971943811)
              ·
                refine ⟨70439923093342703957915717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46959948728895135971943811 70439923093342703957915717)
                ·
                  refine ⟨13207485580001756992109197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70439923093342703957915717 13207485580001756992109197)
                  ·
                    refine ⟨4952807092500658872040949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13207485580001756992109197 4952807092500658872040949)
                    ·
                      refine ⟨464325664921936769253839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4952807092500658872040949 464325664921936769253839)
                      ·
                        rfl

theorem cell23_904271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_904271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904271 prefixEnd_904271 := by exact prefixLift 904271
  have htrace : WordTrace (prefixWord ++ tailWord_904271) baseStart_904271 baseEnd_904271 := by
    simpa [prefixWord, tailWord_904271, baseEnd_904271] using wordTrace_append hprefix tailTrace_904271
  have hstable : (prefixWord ++ tailWord_904271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904271).length < 2 ^ (prefixWord ++ tailWord_904271).sum := by decide
  have hdescent : baseEnd_904271 < baseStart_904271 := by decide
  rcases family_descends (prefixWord ++ tailWord_904271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904286 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_904286 : Nat := 118140960795 + 904286 * 2 ^ 59
def prefixEnd_904286 : Nat := 4983230072969 + 3 ^ 40 * 904286 * 2
def baseEnd_904286 : Nat := 51592596347972690062919

theorem tailTrace_904286 : CollatzResearch.WordTrace tailWord_904286 prefixEnd_904286 51592596347972690062919 := by
  unfold tailWord_904286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122752500241717074791589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21988013334622491065555141 4122752500241717074791589)
  ·
    refine ⟨773016093795321951523423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4122752500241717074791589 773016093795321951523423)
    ·
      refine ⟨1159524140692982927285135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773016093795321951523423 1159524140692982927285135)
      ·
        refine ⟨1739286211039474390927703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159524140692982927285135 1739286211039474390927703)
        ·
          refine ⟨2608929316559211586391555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739286211039474390927703 2608929316559211586391555)
          ·
            refine ⟨3913393974838817379587333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2608929316559211586391555 3913393974838817379587333)
            ·
              refine ⟨733761370282278258672625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3913393974838817379587333 733761370282278258672625)
              ·
                refine ⟨550321027711708694004469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733761370282278258672625 550321027711708694004469)
                ·
                  refine ⟨51592596347972690062919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 550321027711708694004469 51592596347972690062919)
                  ·
                    rfl

theorem cell23_904286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_904286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904286 prefixEnd_904286 := by exact prefixLift 904286
  have htrace : WordTrace (prefixWord ++ tailWord_904286) baseStart_904286 baseEnd_904286 := by
    simpa [prefixWord, tailWord_904286, baseEnd_904286] using wordTrace_append hprefix tailTrace_904286
  have hstable : (prefixWord ++ tailWord_904286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904286).length < 2 ^ (prefixWord ++ tailWord_904286).sum := by decide
  have hdescent : baseEnd_904286 < baseStart_904286 := by decide
  rcases family_descends (prefixWord ++ tailWord_904286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904302 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_904302 : Nat := 118140960795 + 904302 * 2 ^ 59
def prefixEnd_904302 : Nat := 4983230072969 + 3 ^ 40 * 904302 * 2
def baseEnd_904302 : Nat := 464341582822226147966197

theorem tailTrace_904302 : CollatzResearch.WordTrace tailWord_904302 prefixEnd_904302 464341582822226147966197 := by
  unfold tailWord_904302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4122825446234471416364395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21988402379917180887276773 4122825446234471416364395)
  ·
    refine ⟨6184238169351707124546593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4122825446234471416364395 6184238169351707124546593)
    ·
      refine ⟨4638178627013780343409945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184238169351707124546593 4638178627013780343409945)
      ·
        refine ⟨3478633970260335257557459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638178627013780343409945 3478633970260335257557459)
        ·
          refine ⟨5217950955390502886336189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478633970260335257557459 5217950955390502886336189)
          ·
            refine ⟨1956731608271438582376071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5217950955390502886336189 1956731608271438582376071)
            ·
              refine ⟨2935097412407157873564107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956731608271438582376071 2935097412407157873564107)
              ·
                refine ⟨4402646118610736810346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2935097412407157873564107 4402646118610736810346161)
                ·
                  refine ⟨3301984588958052607759621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4402646118610736810346161 3301984588958052607759621)
                  ·
                    refine ⟨619122110429634863954929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3301984588958052607759621 619122110429634863954929)
                    ·
                      refine ⟨464341582822226147966197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619122110429634863954929 464341582822226147966197)
                      ·
                        rfl

theorem cell23_904302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_904302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904302 prefixEnd_904302 := by exact prefixLift 904302
  have htrace : WordTrace (prefixWord ++ tailWord_904302) baseStart_904302 baseEnd_904302 := by
    simpa [prefixWord, tailWord_904302, baseEnd_904302] using wordTrace_append hprefix tailTrace_904302
  have hstable : (prefixWord ++ tailWord_904302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904302).length < 2 ^ (prefixWord ++ tailWord_904302).sum := by decide
  have hdescent : baseEnd_904302 < baseStart_904302 := by decide
  rcases family_descends (prefixWord ++ tailWord_904302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904352 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3]
def baseStart_904352 : Nat := 118140960795 + 904352 * 2 ^ 59
def prefixEnd_904352 : Nat := 4983230072969 + 3 ^ 40 * 904352 * 2
def baseEnd_904352 : Nat := 464367256854950952340967

theorem tailTrace_904352 : CollatzResearch.WordTrace tailWord_904352 prefixEnd_904352 464367256854950952340967 := by
  unfold tailWord_904352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492213609847314935117655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21989618146463086580156873 16492213609847314935117655)
  ·
    refine ⟨24738320414770972402676483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492213609847314935117655 24738320414770972402676483)
    ·
      refine ⟨37107480622156458604014725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24738320414770972402676483 37107480622156458604014725)
      ·
        refine ⟨6957652616654335988252761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37107480622156458604014725 6957652616654335988252761)
        ·
          refine ⟨5218239462490751991189571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957652616654335988252761 5218239462490751991189571)
          ·
            refine ⟨7827359193736127986784357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218239462490751991189571 7827359193736127986784357)
            ·
              refine ⟨1467629848825523997522067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7827359193736127986784357 1467629848825523997522067)
              ·
                refine ⟨2201444773238285996283101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467629848825523997522067 2201444773238285996283101)
                ·
                  refine ⟨825541789964357248606163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2201444773238285996283101 825541789964357248606163)
                  ·
                    refine ⟨1238312684946535872909245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825541789964357248606163 1238312684946535872909245)
                    ·
                      refine ⟨464367256854950952340967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238312684946535872909245 464367256854950952340967)
                      ·
                        rfl

theorem cell23_904352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_904352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904352 prefixEnd_904352 := by exact prefixLift 904352
  have htrace : WordTrace (prefixWord ++ tailWord_904352) baseStart_904352 baseEnd_904352 := by
    simpa [prefixWord, tailWord_904352, baseEnd_904352] using wordTrace_append hprefix tailTrace_904352
  have hstable : (prefixWord ++ tailWord_904352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904352).length < 2 ^ (prefixWord ++ tailWord_904352).sum := by decide
  have hdescent : baseEnd_904352 < baseStart_904352 := by decide
  rcases family_descends (prefixWord ++ tailWord_904352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904375 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_904375 : Nat := 118140960795 + 904375 * 2 ^ 59
def prefixEnd_904375 : Nat := 4983230072969 + 3 ^ 40 * 904375 * 2
def baseEnd_904375 : Nat := 464379066910004362353361

theorem tailTrace_904375 : CollatzResearch.WordTrace tailWord_904375 prefixEnd_904375 464379066910004362353361 := by
  unfold tailWord_904375
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985266098611304798322579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21990177399074203198881719 32985266098611304798322579)
  ·
    refine ⟨49477899147916957197483869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32985266098611304798322579 49477899147916957197483869)
    ·
      refine ⟨18554212180468858949056451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49477899147916957197483869 18554212180468858949056451)
      ·
        refine ⟨27831318270703288423584677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18554212180468858949056451 27831318270703288423584677)
        ·
          refine ⟨5218372175756866579422127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27831318270703288423584677 5218372175756866579422127)
          ·
            refine ⟨7827558263635299869133191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218372175756866579422127 7827558263635299869133191)
            ·
              refine ⟨11741337395452949803699787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7827558263635299869133191 11741337395452949803699787)
              ·
                refine ⟨17612006093179424705549681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11741337395452949803699787 17612006093179424705549681)
                ·
                  refine ⟨13209004569884568529162261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17612006093179424705549681 13209004569884568529162261)
                  ·
                    refine ⟨619172089213339149804481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13209004569884568529162261 619172089213339149804481)
                    ·
                      refine ⟨464379066910004362353361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619172089213339149804481 464379066910004362353361)
                      ·
                        rfl

theorem cell23_904375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_904375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904375 prefixEnd_904375 := by exact prefixLift 904375
  have htrace : WordTrace (prefixWord ++ tailWord_904375) baseStart_904375 baseEnd_904375 := by
    simpa [prefixWord, tailWord_904375, baseEnd_904375] using wordTrace_append hprefix tailTrace_904375
  have hstable : (prefixWord ++ tailWord_904375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904375).length < 2 ^ (prefixWord ++ tailWord_904375).sum := by decide
  have hdescent : baseEnd_904375 < baseStart_904375 := by decide
  rcases family_descends (prefixWord ++ tailWord_904375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904378 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_904378 : Nat := 118140960795 + 904378 * 2 ^ 59
def prefixEnd_904378 : Nat := 4983230072969 + 3 ^ 40 * 904378 * 2
def baseEnd_904378 : Nat := 464380607351967850615847

theorem tailTrace_904378 : CollatzResearch.WordTrace tailWord_904378 prefixEnd_904378 464380607351967850615847 := by
  unfold tailWord_904378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246343879400109077670447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21990250345066957540454525 8246343879400109077670447)
  ·
    refine ⟨12369515819100163616505671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8246343879400109077670447 12369515819100163616505671)
    ·
      refine ⟨18554273728650245424758507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12369515819100163616505671 18554273728650245424758507)
      ·
        refine ⟨27831410592975368137137761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18554273728650245424758507 27831410592975368137137761)
        ·
          refine ⟨20873557944731526102853321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27831410592975368137137761 20873557944731526102853321)
          ·
            refine ⟨15655168458548644577139991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20873557944731526102853321 15655168458548644577139991)
            ·
              refine ⟨23482752687822966865709987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15655168458548644577139991 23482752687822966865709987)
              ·
                refine ⟨35224129031734450298564981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23482752687822966865709987 35224129031734450298564981)
                ·
                  refine ⟨3302262096725104715490467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35224129031734450298564981 3302262096725104715490467)
                  ·
                    refine ⟨4953393145087657073235701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3302262096725104715490467 4953393145087657073235701)
                    ·
                      refine ⟨464380607351967850615847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4953393145087657073235701 464380607351967850615847)
                      ·
                        rfl

theorem cell23_904378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_904378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904378 prefixEnd_904378 := by exact prefixLift 904378
  have htrace : WordTrace (prefixWord ++ tailWord_904378) baseStart_904378 baseEnd_904378 := by
    simpa [prefixWord, tailWord_904378, baseEnd_904378] using wordTrace_append hprefix tailTrace_904378
  have hstable : (prefixWord ++ tailWord_904378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904378).length < 2 ^ (prefixWord ++ tailWord_904378).sum := by decide
  have hdescent : baseEnd_904378 < baseStart_904378 := by decide
  rcases family_descends (prefixWord ++ tailWord_904378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904392 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_904392 : Nat := 118140960795 + 904392 * 2 ^ 59
def prefixEnd_904392 : Nat := 4983230072969 + 3 ^ 40 * 904392 * 2
def baseEnd_904392 : Nat := 464387796081130795840783

theorem tailTrace_904392 : CollatzResearch.WordTrace tailWord_904392 prefixEnd_904392 464387796081130795840783 := by
  unfold tailWord_904392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16492943069774858350845715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21990590759699811134460953 16492943069774858350845715)
  ·
    refine ⟨24739414604662287526268573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16492943069774858350845715 24739414604662287526268573)
    ·
      refine ⟨9277280476748357822350715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24739414604662287526268573 9277280476748357822350715)
      ·
        refine ⟨13915920715122536733526073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9277280476748357822350715 13915920715122536733526073)
        ·
          refine ⟨10436940536341902550144555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13915920715122536733526073 10436940536341902550144555)
          ·
            refine ⟨15655410804512853825216833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10436940536341902550144555 15655410804512853825216833)
            ·
              refine ⟨11741558103384640368912625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15655410804512853825216833 11741558103384640368912625)
              ·
                refine ⟨8806168577538480276684469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11741558103384640368912625 8806168577538480276684469)
                ·
                  refine ⟨825578304144232525939169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8806168577538480276684469 825578304144232525939169)
                  ·
                    refine ⟨619183728108174394454377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825578304144232525939169 619183728108174394454377)
                    ·
                      refine ⟨464387796081130795840783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619183728108174394454377 464387796081130795840783)
                      ·
                        rfl

theorem cell23_904392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_904392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904392 prefixEnd_904392 := by exact prefixLift 904392
  have htrace : WordTrace (prefixWord ++ tailWord_904392) baseStart_904392 baseEnd_904392 := by
    simpa [prefixWord, tailWord_904392, baseEnd_904392] using wordTrace_append hprefix tailTrace_904392
  have hstable : (prefixWord ++ tailWord_904392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904392).length < 2 ^ (prefixWord ++ tailWord_904392).sum := by decide
  have hdescent : baseEnd_904392 < baseStart_904392 := by decide
  rcases family_descends (prefixWord ++ tailWord_904392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904402 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_904402 : Nat := 118140960795 + 904402 * 2 ^ 59
def prefixEnd_904402 : Nat := 4983230072969 + 3 ^ 40 * 904402 * 2
def baseEnd_904402 : Nat := 154797643629225252238579

theorem tailTrace_904402 : CollatzResearch.WordTrace tailWord_904402 prefixEnd_904402 154797643629225252238579 := by
  unfold tailWord_904402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8246562717378372102388865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21990833913008992273036973 8246562717378372102388865)
  ·
    refine ⟨6184922038033779076791649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8246562717378372102388865 6184922038033779076791649)
    ·
      refine ⟨4638691528525334307593737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6184922038033779076791649 4638691528525334307593737)
      ·
        refine ⟨3479018646394000730695303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638691528525334307593737 3479018646394000730695303)
        ·
          refine ⟨5218527969591001096042955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479018646394000730695303 5218527969591001096042955)
          ·
            refine ⟨7827791954386501644064433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218527969591001096042955 7827791954386501644064433)
            ·
              refine ⟨5870843965789876233048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7827791954386501644064433 5870843965789876233048325)
              ·
                refine ⟨1100783243585601793696561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5870843965789876233048325 1100783243585601793696561)
                ·
                  refine ⟨825587432689201345272421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100783243585601793696561 825587432689201345272421)
                  ·
                    refine ⟨154797643629225252238579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 825587432689201345272421 154797643629225252238579)
                    ·
                      rfl

theorem cell23_904402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_904402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904402 prefixEnd_904402 := by exact prefixLift 904402
  have htrace : WordTrace (prefixWord ++ tailWord_904402) baseStart_904402 baseEnd_904402 := by
    simpa [prefixWord, tailWord_904402, baseEnd_904402] using wordTrace_append hprefix tailTrace_904402
  have hstable : (prefixWord ++ tailWord_904402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904402).length < 2 ^ (prefixWord ++ tailWord_904402).sum := by decide
  have hdescent : baseEnd_904402 < baseStart_904402 := by decide
  rcases family_descends (prefixWord ++ tailWord_904402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904405 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_904405 : Nat := 118140960795 + 904405 * 2 ^ 59
def prefixEnd_904405 : Nat := 4983230072969 + 3 ^ 40 * 904405 * 2
def baseEnd_904405 : Nat := 464394471329639244978223

theorem tailTrace_904405 : CollatzResearch.WordTrace tailWord_904405 prefixEnd_904405 464394471329639244978223 := by
  unfold tailWord_904405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32986360288502619921914669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21990906859001746614609779 32986360288502619921914669)
  ·
    refine ⟨12369885108188482470718001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32986360288502619921914669 12369885108188482470718001)
    ·
      refine ⟨9277413831141361853038501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12369885108188482470718001 9277413831141361853038501)
      ·
        refine ⟨1739515093339005347444719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9277413831141361853038501 1739515093339005347444719)
        ·
          refine ⟨2609272640008508021167079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739515093339005347444719 2609272640008508021167079)
          ·
            refine ⟨3913908960012762031750619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609272640008508021167079 3913908960012762031750619)
            ·
              refine ⟨5870863440019143047625929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3913908960012762031750619 5870863440019143047625929)
              ·
                refine ⟨4403147580014357285719447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5870863440019143047625929 4403147580014357285719447)
                ·
                  refine ⟨6604721370021535928579171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403147580014357285719447 6604721370021535928579171)
                  ·
                    refine ⟨9907082055032303892868757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6604721370021535928579171 9907082055032303892868757)
                    ·
                      refine ⟨464394471329639244978223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9907082055032303892868757 464394471329639244978223)
                      ·
                        rfl

theorem cell23_904405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_904405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904405 prefixEnd_904405 := by exact prefixLift 904405
  have htrace : WordTrace (prefixWord ++ tailWord_904405) baseStart_904405 baseEnd_904405 := by
    simpa [prefixWord, tailWord_904405, baseEnd_904405] using wordTrace_append hprefix tailTrace_904405
  have hstable : (prefixWord ++ tailWord_904405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904405).length < 2 ^ (prefixWord ++ tailWord_904405).sum := by decide
  have hdescent : baseEnd_904405 < baseStart_904405 := by decide
  rcases family_descends (prefixWord ++ tailWord_904405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904429 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_904429 : Nat := 118140960795 + 904429 * 2 ^ 59
def prefixEnd_904429 : Nat := 4983230072969 + 3 ^ 40 * 904429 * 2
def baseEnd_904429 : Nat := 464406794865347151078113

theorem tailTrace_904429 : CollatzResearch.WordTrace tailWord_904429 prefixEnd_904429 464406794865347151078113 := by
  unfold tailWord_904429
  simp only [CollatzResearch.WordTrace]
  refine ⟨32987235640415672020788341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21991490426943781347192227 32987235640415672020788341)
  ·
    refine ⟨3092553341288969251948907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32987235640415672020788341 3092553341288969251948907)
    ·
      refine ⟨4638830011933453877923361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092553341288969251948907 4638830011933453877923361)
      ·
        refine ⟨3479122508950090408442521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638830011933453877923361 3479122508950090408442521)
        ·
          refine ⟨2609341881712567806331891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3479122508950090408442521 2609341881712567806331891)
          ·
            refine ⟨3914012822568851709497837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609341881712567806331891 3914012822568851709497837)
            ·
              refine ⟨1467754808463319391061689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914012822568851709497837 1467754808463319391061689)
              ·
                refine ⟨1100816106347489543296267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467754808463319391061689 1100816106347489543296267)
                ·
                  refine ⟨1651224159521234314944401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100816106347489543296267 1651224159521234314944401)
                  ·
                    refine ⟨1238418119640925736208301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1651224159521234314944401 1238418119640925736208301)
                    ·
                      refine ⟨464406794865347151078113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238418119640925736208301 464406794865347151078113)
                      ·
                        rfl

theorem cell23_904429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_904429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904429 prefixEnd_904429 := by exact prefixLift 904429
  have htrace : WordTrace (prefixWord ++ tailWord_904429) baseStart_904429 baseEnd_904429 := by
    simpa [prefixWord, tailWord_904429, baseEnd_904429] using wordTrace_append hprefix tailTrace_904429
  have hstable : (prefixWord ++ tailWord_904429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904429).length < 2 ^ (prefixWord ++ tailWord_904429).sum := by decide
  have hdescent : baseEnd_904429 < baseStart_904429 := by decide
  rcases family_descends (prefixWord ++ tailWord_904429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904436 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_904436 : Nat := 118140960795 + 904436 * 2 ^ 59
def prefixEnd_904436 : Nat := 4983230072969 + 3 ^ 40 * 904436 * 2
def baseEnd_904436 : Nat := 154803463076642874563527

theorem tailTrace_904436 : CollatzResearch.WordTrace tailWord_904436 prefixEnd_904436 154803463076642874563527 := by
  unfold tailWord_904436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16493745475695156108146581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21991660634260208144195441 16493745475695156108146581)
  ·
    refine ⟨773144319173210442569371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16493745475695156108146581 773144319173210442569371)
    ·
      refine ⟨1159716478759815663854057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773144319173210442569371 1159716478759815663854057)
      ·
        refine ⟨869787359069861747890543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159716478759815663854057 869787359069861747890543)
        ·
          refine ⟨1304681038604792621835815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869787359069861747890543 1304681038604792621835815)
          ·
            refine ⟨1957021557907188932753723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304681038604792621835815 1957021557907188932753723)
            ·
              refine ⟨2935532336860783399130585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1957021557907188932753723 2935532336860783399130585)
              ·
                refine ⟨2201649252645587549347939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935532336860783399130585 2201649252645587549347939)
                ·
                  refine ⟨3302473878968381324021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2201649252645587549347939 3302473878968381324021909)
                  ·
                    refine ⟨154803463076642874563527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3302473878968381324021909 154803463076642874563527)
                    ·
                      rfl

theorem cell23_904436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_904436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904436 prefixEnd_904436 := by exact prefixLift 904436
  have htrace : WordTrace (prefixWord ++ tailWord_904436) baseStart_904436 baseEnd_904436 := by
    simpa [prefixWord, tailWord_904436, baseEnd_904436] using wordTrace_append hprefix tailTrace_904436
  have hstable : (prefixWord ++ tailWord_904436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904436).length < 2 ^ (prefixWord ++ tailWord_904436).sum := by decide
  have hdescent : baseEnd_904436 < baseStart_904436 := by decide
  rcases family_descends (prefixWord ++ tailWord_904436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904446 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_904446 : Nat := 118140960795 + 904446 * 2 ^ 59
def prefixEnd_904446 : Nat := 4983230072969 + 3 ^ 40 * 904446 * 2
def baseEnd_904446 : Nat := 464415524036473584565535

theorem tailTrace_904446 : CollatzResearch.WordTrace tailWord_904446 prefixEnd_904446 464415524036473584565535 := by
  unfold tailWord_904446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123481960169260490519649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21991903787569389282771461 4123481960169260490519649)
  ·
    refine ⟨3092611470126945367889737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123481960169260490519649 3092611470126945367889737)
    ·
      refine ⟨2319458602595209025917303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3092611470126945367889737 2319458602595209025917303)
      ·
        refine ⟨3479187903892813538875955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2319458602595209025917303 3479187903892813538875955)
        ·
          refine ⟨5218781855839220308313933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3479187903892813538875955 5218781855839220308313933)
          ·
            refine ⟨1957043195939707615617725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5218781855839220308313933 1957043195939707615617725)
            ·
              refine ⟨733891198477390355856647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957043195939707615617725 733891198477390355856647)
              ·
                refine ⟨1100836797716085533784971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733891198477390355856647 1100836797716085533784971)
                ·
                  refine ⟨1651255196574128300677457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1100836797716085533784971 1651255196574128300677457)
                  ·
                    refine ⟨1238441397430596225508093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1651255196574128300677457 1238441397430596225508093)
                    ·
                      refine ⟨464415524036473584565535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238441397430596225508093 464415524036473584565535)
                      ·
                        rfl

theorem cell23_904446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_904446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904446 prefixEnd_904446 := by exact prefixLift 904446
  have htrace : WordTrace (prefixWord ++ tailWord_904446) baseStart_904446 baseEnd_904446 := by
    simpa [prefixWord, tailWord_904446, baseEnd_904446] using wordTrace_append hprefix tailTrace_904446
  have hstable : (prefixWord ++ tailWord_904446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904446).length < 2 ^ (prefixWord ++ tailWord_904446).sum := by decide
  have hdescent : baseEnd_904446 < baseStart_904446 := by decide
  rcases family_descends (prefixWord ++ tailWord_904446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904459 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 3]
def baseStart_904459 : Nat := 118140960795 + 904459 * 2 ^ 59
def prefixEnd_904459 : Nat := 4983230072969 + 3 ^ 40 * 904459 * 2
def baseEnd_904459 : Nat := 464422199284982033702975

theorem tailTrace_904459 : CollatzResearch.WordTrace tailWord_904459 prefixEnd_904459 464422199284982033702975 := by
  unfold tailWord_904459
  simp only [CollatzResearch.WordTrace]
  refine ⟨32988329830306987144380431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21992219886871324762920287 32988329830306987144380431)
  ·
    refine ⟨49482494745460480716570647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32988329830306987144380431 49482494745460480716570647)
    ·
      refine ⟨74223742118190721074855971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49482494745460480716570647 74223742118190721074855971)
      ·
        refine ⟨111335613177286081612283957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74223742118190721074855971 111335613177286081612283957)
        ·
          refine ⟨10437713735370570151151621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111335613177286081612283957 10437713735370570151151621)
          ·
            refine ⟨1957071325381981903340929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10437713735370570151151621 1957071325381981903340929)
            ·
              refine ⟨1467803494036486427505697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957071325381981903340929 1467803494036486427505697)
              ·
                refine ⟨1100852620527364820629273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1467803494036486427505697 1100852620527364820629273)
                ·
                  refine ⟨825639465395523615471955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100852620527364820629273 825639465395523615471955)
                  ·
                    refine ⟨1238459198093285423207933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 825639465395523615471955 1238459198093285423207933)
                    ·
                      refine ⟨464422199284982033702975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238459198093285423207933 464422199284982033702975)
                      ·
                        rfl

theorem cell23_904459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 3].length) (baseStart_904459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904459 prefixEnd_904459 := by exact prefixLift 904459
  have htrace : WordTrace (prefixWord ++ tailWord_904459) baseStart_904459 baseEnd_904459 := by
    simpa [prefixWord, tailWord_904459, baseEnd_904459] using wordTrace_append hprefix tailTrace_904459
  have hstable : (prefixWord ++ tailWord_904459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904459).length < 2 ^ (prefixWord ++ tailWord_904459).sum := by decide
  have hdescent : baseEnd_904459 < baseStart_904459 := by decide
  rcases family_descends (prefixWord ++ tailWord_904459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904466 : List Nat := [3, 2, 4, 2, 2, 1, 1, 8]
def baseStart_904466 : Nat := 118140960795 + 904466 * 2 ^ 59
def prefixEnd_904466 : Nat := 4983230072969 + 3 ^ 40 * 904466 * 2
def baseEnd_904466 : Nat := 17200955320354203937609

theorem tailTrace_904466 : CollatzResearch.WordTrace tailWord_904466 prefixEnd_904466 17200955320354203937609 := by
  unfold tailWord_904466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247146285320406834971313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21992390094187751559923501 8247146285320406834971313)
  ·
    refine ⟨6185359713990305126228485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8247146285320406834971313 6185359713990305126228485)
    ·
      refine ⟨1159754946373182211167841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6185359713990305126228485 1159754946373182211167841)
      ·
        refine ⟨869816209779886658375881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159754946373182211167841 869816209779886658375881)
        ·
          refine ⟨652362157334914993781911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869816209779886658375881 652362157334914993781911)
          ·
            refine ⟨978543236002372490672867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652362157334914993781911 978543236002372490672867)
            ·
              refine ⟨1467814854003558736009301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978543236002372490672867 1467814854003558736009301)
              ·
                refine ⟨17200955320354203937609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1467814854003558736009301 17200955320354203937609)
                ·
                  rfl

theorem cell23_904466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_904466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904466 prefixEnd_904466 := by exact prefixLift 904466
  have htrace : WordTrace (prefixWord ++ tailWord_904466) baseStart_904466 baseEnd_904466 := by
    simpa [prefixWord, tailWord_904466, baseEnd_904466] using wordTrace_append hprefix tailTrace_904466
  have hstable : (prefixWord ++ tailWord_904466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904466).length < 2 ^ (prefixWord ++ tailWord_904466).sum := by decide
  have hdescent : baseEnd_904466 < baseStart_904466 := by decide
  rcases family_descends (prefixWord ++ tailWord_904466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904532 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_904532 : Nat := 118140960795 + 904532 * 2 ^ 59
def prefixEnd_904532 : Nat := 4983230072969 + 3 ^ 40 * 904532 * 2
def baseEnd_904532 : Nat := 464459683372760248090139

theorem tailTrace_904532 : CollatzResearch.WordTrace tailWord_904532 prefixEnd_904532 464459683372760248090139 := by
  unfold tailWord_904532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495496179521260305893925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21993994906028347074525233 16495496179521260305893925)
  ·
    refine ⟨3092905533660236307355111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16495496179521260305893925 3092905533660236307355111)
    ·
      refine ⟨4639358300490354461032667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092905533660236307355111 4639358300490354461032667)
      ·
        refine ⟨6959037450735531691549001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639358300490354461032667 6959037450735531691549001)
        ·
          refine ⟨5219278088051648768661751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959037450735531691549001 5219278088051648768661751)
          ·
            refine ⟨7828917132077473152992627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219278088051648768661751 7828917132077473152992627)
            ·
              refine ⟨11743375698116209729488941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828917132077473152992627 11743375698116209729488941)
              ·
                refine ⟨4403765886793578648558353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11743375698116209729488941 4403765886793578648558353)
                ·
                  refine ⟨3302824415095183986418765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4403765886793578648558353 3302824415095183986418765)
                  ·
                    refine ⟨1238559155660693994907037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3302824415095183986418765 1238559155660693994907037)
                    ·
                      refine ⟨464459683372760248090139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1238559155660693994907037 464459683372760248090139)
                      ·
                        rfl

theorem cell23_904532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_904532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904532 prefixEnd_904532 := by exact prefixLift 904532
  have htrace : WordTrace (prefixWord ++ tailWord_904532) baseStart_904532 baseEnd_904532 := by
    simpa [prefixWord, tailWord_904532, baseEnd_904532] using wordTrace_append hprefix tailTrace_904532
  have hstable : (prefixWord ++ tailWord_904532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904532).length < 2 ^ (prefixWord ++ tailWord_904532).sum := by decide
  have hdescent : baseEnd_904532 < baseStart_904532 := by decide
  rcases family_descends (prefixWord ++ tailWord_904532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904533 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_904533 : Nat := 118140960795 + 904533 * 2 ^ 59
def prefixEnd_904533 : Nat := 4983230072969 + 3 ^ 40 * 904533 * 2
def baseEnd_904533 : Nat := 464460196853414744177635

theorem tailTrace_904533 : CollatzResearch.WordTrace tailWord_904533 prefixEnd_904533 464460196853414744177635 := by
  unfold tailWord_904533
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991028832038897782574253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21994019221359265188382835 32991028832038897782574253)
  ·
    refine ⟨12371635812014586668465345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32991028832038897782574253 12371635812014586668465345)
    ·
      refine ⟨9278726859010940001349009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12371635812014586668465345 9278726859010940001349009)
      ·
        refine ⟨6959045144258205001011757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278726859010940001349009 6959045144258205001011757)
        ·
          refine ⟨2609641929096826875379409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6959045144258205001011757 2609641929096826875379409)
          ·
            refine ⟨1957231446822620156534557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2609641929096826875379409 1957231446822620156534557)
            ·
              refine ⟨733961792558482558700459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957231446822620156534557 733961792558482558700459)
              ·
                refine ⟨1100942688837723838050689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733961792558482558700459 1100942688837723838050689)
                ·
                  refine ⟨825707016628292878538017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1100942688837723838050689 825707016628292878538017)
                  ·
                    refine ⟨619280262471219658903513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 825707016628292878538017 619280262471219658903513)
                    ·
                      refine ⟨464460196853414744177635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 619280262471219658903513 464460196853414744177635)
                      ·
                        rfl

theorem cell23_904533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_904533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904533 prefixEnd_904533 := by exact prefixLift 904533
  have htrace : WordTrace (prefixWord ++ tailWord_904533) baseStart_904533 baseEnd_904533 := by
    simpa [prefixWord, tailWord_904533, baseEnd_904533] using wordTrace_append hprefix tailTrace_904533
  have hstable : (prefixWord ++ tailWord_904533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904533).length < 2 ^ (prefixWord ++ tailWord_904533).sum := by decide
  have hdescent : baseEnd_904533 < baseStart_904533 := by decide
  rcases family_descends (prefixWord ++ tailWord_904533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904535 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 7]
def baseStart_904535 : Nat := 118140960795 + 904535 * 2 ^ 59
def prefixEnd_904535 : Nat := 4983230072969 + 3 ^ 40 * 904535 * 2
def baseEnd_904535 : Nat := 154820407938241245450875

theorem tailTrace_904535 : CollatzResearch.WordTrace tailWord_904535 prefixEnd_904535 154820407938241245450875 := by
  unfold tailWord_904535
  simp only [CollatzResearch.WordTrace]
  refine ⟨32991101778031652124147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21994067852021101416098039 32991101778031652124147059)
  ·
    refine ⟨49486652667047478186220589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32991101778031652124147059 49486652667047478186220589)
    ·
      refine ⟨18557494750142804319832721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49486652667047478186220589 18557494750142804319832721)
      ·
        refine ⟨13918121062607103239874541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18557494750142804319832721 13918121062607103239874541)
        ·
          refine ⟨5219295398477663714952953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13918121062607103239874541 5219295398477663714952953)
          ·
            refine ⟨3914471548858247786214715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5219295398477663714952953 3914471548858247786214715)
            ·
              refine ⟨5871707323287371679322073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3914471548858247786214715 5871707323287371679322073)
              ·
                refine ⟨4403780492465528759491555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871707323287371679322073 4403780492465528759491555)
                ·
                  refine ⟨6605670738698293139237333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403780492465528759491555 6605670738698293139237333)
                  ·
                    refine ⟨154820407938241245450875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6605670738698293139237333 154820407938241245450875)
                    ·
                      rfl

theorem cell23_904535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_904535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904535 prefixEnd_904535 := by exact prefixLift 904535
  have htrace : WordTrace (prefixWord ++ tailWord_904535) baseStart_904535 baseEnd_904535 := by
    simpa [prefixWord, tailWord_904535, baseEnd_904535] using wordTrace_append hprefix tailTrace_904535
  have hstable : (prefixWord ++ tailWord_904535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904535).length < 2 ^ (prefixWord ++ tailWord_904535).sum := by decide
  have hdescent : baseEnd_904535 < baseStart_904535 := by decide
  rcases family_descends (prefixWord ++ tailWord_904535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904572 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_904572 : Nat := 118140960795 + 904572 * 2 ^ 59
def prefixEnd_904572 : Nat := 4983230072969 + 3 ^ 40 * 904572 * 2
def baseEnd_904572 : Nat := 464480222598940091589955

theorem tailTrace_904572 : CollatzResearch.WordTrace tailWord_904572 prefixEnd_904572 464480222598940091589955 := by
  unfold tailWord_904572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496225639448803721621985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21994967519265071628829313 16496225639448803721621985)
  ·
    refine ⟨12372169229586602791216489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16496225639448803721621985 12372169229586602791216489)
    ·
      refine ⟨9279126922189952093412367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12372169229586602791216489 9279126922189952093412367)
      ·
        refine ⟨13918690383284928140118551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279126922189952093412367 13918690383284928140118551)
        ·
          refine ⟨20878035574927392210177827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13918690383284928140118551 20878035574927392210177827)
          ·
            refine ⟨31317053362391088315266741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20878035574927392210177827 31317053362391088315266741)
            ·
              refine ⟨2935973752724164529556257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31317053362391088315266741 2935973752724164529556257)
              ·
                refine ⟨2201980314543123397167193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2935973752724164529556257 2201980314543123397167193)
                ·
                  refine ⟨1651485235907342547875395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2201980314543123397167193 1651485235907342547875395)
                  ·
                    refine ⟨2477227853861013821813093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1651485235907342547875395 2477227853861013821813093)
                    ·
                      refine ⟨464480222598940091589955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2477227853861013821813093 464480222598940091589955)
                      ·
                        rfl

theorem cell23_904572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_904572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_904572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_904572 prefixEnd_904572 := by exact prefixLift 904572
  have htrace : WordTrace (prefixWord ++ tailWord_904572) baseStart_904572 baseEnd_904572 := by
    simpa [prefixWord, tailWord_904572, baseEnd_904572] using wordTrace_append hprefix tailTrace_904572
  have hstable : (prefixWord ++ tailWord_904572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904572).length < 2 ^ (prefixWord ++ tailWord_904572).sum := by decide
  have hdescent : baseEnd_904572 < baseStart_904572 := by decide
  rcases family_descends (prefixWord ++ tailWord_904572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
