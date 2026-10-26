import V185TrunkScan23Chunk1395

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8268567 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_8268567 : Nat := 118140960795 + 8268567 * 2 ^ 59
def prefixEnd_8268567 : Nat := 4983230072969 + 3 ^ 40 * 8268567 * 2
def baseEnd_8268567 : Nat := 4245749194904855927286059

theorem tailTrace_8268567 : CollatzResearch.WordTrace tailWord_8268567 prefixEnd_8268567 4245749194904855927286059 := by
  unfold tailWord_8268567
  simp only [CollatzResearch.WordTrace]
  refine ⟨301579414235401392661003955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201052942823600928440669303 301579414235401392661003955)
  ·
    refine ⟨452369121353102088991505933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301579414235401392661003955 452369121353102088991505933)
    ·
      refine ⟨169638420507413283371814725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452369121353102088991505933 169638420507413283371814725)
      ·
        refine ⟨31807203845139990632215261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169638420507413283371814725 31807203845139990632215261)
        ·
          refine ⟨11927701441927496487080723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31807203845139990632215261 11927701441927496487080723)
          ·
            refine ⟨17891552162891244730621085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927701441927496487080723 17891552162891244730621085)
            ·
              refine ⟨6709332061084216773982907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17891552162891244730621085 6709332061084216773982907)
              ·
                refine ⟨10063998091626325160974361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709332061084216773982907 10063998091626325160974361)
                ·
                  refine ⟨7547998568719743870730771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063998091626325160974361 7547998568719743870730771)
                  ·
                    refine ⟨11321997853079615806096157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547998568719743870730771 11321997853079615806096157)
                    ·
                      refine ⟨4245749194904855927286059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11321997853079615806096157 4245749194904855927286059)
                      ·
                        rfl

theorem cell23_8268567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_8268567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268567 prefixEnd_8268567 := by exact prefixLift 8268567
  have htrace : WordTrace (prefixWord ++ tailWord_8268567) baseStart_8268567 baseEnd_8268567 := by
    simpa [prefixWord, tailWord_8268567, baseEnd_8268567] using wordTrace_append hprefix tailTrace_8268567
  have hstable : (prefixWord ++ tailWord_8268567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268567).length < 2 ^ (prefixWord ++ tailWord_8268567).sum := by decide
  have hdescent : baseEnd_8268567 < baseStart_8268567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268569 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_8268569 : Nat := 118140960795 + 8268569 * 2 ^ 59
def prefixEnd_8268569 : Nat := 4983230072969 + 3 ^ 40 * 8268569 * 2
def baseEnd_8268569 : Nat := 4245750221866164919461049

theorem tailTrace_8268569 : CollatzResearch.WordTrace tailWord_8268569 prefixEnd_8268569 4245750221866164919461049 := by
  unfold tailWord_8268569
  simp only [CollatzResearch.WordTrace]
  refine ⟨301579487181394147002576761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201052991454262764668384507 301579487181394147002576761)
  ·
    refine ⟨226184615386045610251932571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301579487181394147002576761 226184615386045610251932571)
    ·
      refine ⟨339276923079068415377898857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226184615386045610251932571 339276923079068415377898857)
      ·
        refine ⟨254457692309301311533424143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339276923079068415377898857 254457692309301311533424143)
        ·
          refine ⟨381686538463951967300136215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254457692309301311533424143 381686538463951967300136215)
          ·
            refine ⟨572529807695927950950204323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381686538463951967300136215 572529807695927950950204323)
            ·
              refine ⟨858794711543891926425306485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572529807695927950950204323 858794711543891926425306485)
              ·
                refine ⟨80512004207239868102372483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 858794711543891926425306485 80512004207239868102372483)
                ·
                  refine ⟨120768006310859802153558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80512004207239868102372483 120768006310859802153558725)
                  ·
                    refine ⟨22644001183286212903792261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120768006310859802153558725 22644001183286212903792261)
                    ·
                      refine ⟨4245750221866164919461049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22644001183286212903792261 4245750221866164919461049)
                      ·
                        rfl

theorem cell23_8268569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_8268569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268569 prefixEnd_8268569 := by exact prefixLift 8268569
  have htrace : WordTrace (prefixWord ++ tailWord_8268569) baseStart_8268569 baseEnd_8268569 := by
    simpa [prefixWord, tailWord_8268569, baseEnd_8268569] using wordTrace_append hprefix tailTrace_8268569
  have hstable : (prefixWord ++ tailWord_8268569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268569).length < 2 ^ (prefixWord ++ tailWord_8268569).sum := by decide
  have hdescent : baseEnd_8268569 < baseStart_8268569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268626 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_8268626 : Nat := 118140960795 + 8268626 * 2 ^ 59
def prefixEnd_8268626 : Nat := 4983230072969 + 3 ^ 40 * 8268626 * 2
def baseEnd_8268626 : Nat := 1415259830087823732149429

theorem tailTrace_8268626 : CollatzResearch.WordTrace tailWord_8268626 prefixEnd_8268626 1415259830087823732149429 := by
  unfold tailWord_8268626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75395391535546911434350433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201054377428125097158267821 75395391535546911434350433)
  ·
    refine ⟨56546543651660183575762825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75395391535546911434350433 56546543651660183575762825)
    ·
      refine ⟨42409907738745137681822119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56546543651660183575762825 42409907738745137681822119)
      ·
        refine ⟨63614861608117706522733179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42409907738745137681822119 63614861608117706522733179)
        ·
          refine ⟨95422292412176559784099769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63614861608117706522733179 95422292412176559784099769)
          ·
            refine ⟨71566719309132419838074827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95422292412176559784099769 71566719309132419838074827)
            ·
              refine ⟨107350078963698629757112241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71566719309132419838074827 107350078963698629757112241)
              ·
                refine ⟨80512559222773972317834181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107350078963698629757112241 80512559222773972317834181)
                ·
                  refine ⟨15096104854270119809593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80512559222773972317834181 15096104854270119809593909)
                  ·
                    refine ⟨1415259830087823732149429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096104854270119809593909 1415259830087823732149429)
                    ·
                      rfl

theorem cell23_8268626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_8268626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268626 prefixEnd_8268626 := by exact prefixLift 8268626
  have htrace : WordTrace (prefixWord ++ tailWord_8268626) baseStart_8268626 baseEnd_8268626 := by
    simpa [prefixWord, tailWord_8268626, baseEnd_8268626] using wordTrace_append hprefix tailTrace_8268626
  have hstable : (prefixWord ++ tailWord_8268626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268626).length < 2 ^ (prefixWord ++ tailWord_8268626).sum := by decide
  have hdescent : baseEnd_8268626 < baseStart_8268626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268643 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 2, 5]
def baseStart_8268643 : Nat := 118140960795 + 8268643 * 2 ^ 59
def prefixEnd_8268643 : Nat := 4983230072969 + 3 ^ 40 * 8268643 * 2
def baseEnd_8268643 : Nat := 1415262739811532543311903

theorem tailTrace_8268643 : CollatzResearch.WordTrace tailWord_8268643 prefixEnd_8268643 1415262739811532543311903 := by
  unfold tailWord_8268643
  simp only [CollatzResearch.WordTrace]
  refine ⟨301582186183126057640770583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201054790788750705093847055 301582186183126057640770583)
  ·
    refine ⟨452373279274689086461155875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301582186183126057640770583 452373279274689086461155875)
    ·
      refine ⟨678559918912033629691733813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452373279274689086461155875 678559918912033629691733813)
      ·
        refine ⟨63614992398003152783600045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 678559918912033629691733813 63614992398003152783600045)
        ·
          refine ⟨23855622149251182293850017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63614992398003152783600045 23855622149251182293850017)
          ·
            refine ⟨17891716611938386720387513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23855622149251182293850017 17891716611938386720387513)
            ·
              refine ⟨13418787458953790040290635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891716611938386720387513 13418787458953790040290635)
              ·
                refine ⟨20128181188430685060435953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418787458953790040290635 20128181188430685060435953)
                ·
                  refine ⟨15096135891323013795326965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20128181188430685060435953 15096135891323013795326965)
                  ·
                    refine ⟨1415262739811532543311903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096135891323013795326965 1415262739811532543311903)
                    ·
                      rfl

theorem cell23_8268643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 5].length) (baseStart_8268643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268643 prefixEnd_8268643 := by exact prefixLift 8268643
  have htrace : WordTrace (prefixWord ++ tailWord_8268643) baseStart_8268643 baseEnd_8268643 := by
    simpa [prefixWord, tailWord_8268643, baseEnd_8268643] using wordTrace_append hprefix tailTrace_8268643
  have hstable : (prefixWord ++ tailWord_8268643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268643).length < 2 ^ (prefixWord ++ tailWord_8268643).sum := by decide
  have hdescent : baseEnd_8268643 < baseStart_8268643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268649 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_8268649 : Nat := 118140960795 + 8268649 * 2 ^ 59
def prefixEnd_8268649 : Nat := 4983230072969 + 3 ^ 40 * 8268649 * 2
def baseEnd_8268649 : Nat := 4245791300318524606460681

theorem tailTrace_8268649 : CollatzResearch.WordTrace tailWord_8268649 prefixEnd_8268649 4245791300318524606460681 := by
  unfold tailWord_8268649
  simp only [CollatzResearch.WordTrace]
  refine ⟨301582405021104320665489001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201054936680736213776992667 301582405021104320665489001)
  ·
    refine ⟨226186803765828240499116751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301582405021104320665489001 226186803765828240499116751)
    ·
      refine ⟨339280205648742360748675127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226186803765828240499116751 339280205648742360748675127)
      ·
        refine ⟨508920308473113541123012691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339280205648742360748675127 508920308473113541123012691)
        ·
          refine ⟨763380462709670311684519037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508920308473113541123012691 763380462709670311684519037)
          ·
            refine ⟨286267673516126366881694639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763380462709670311684519037 286267673516126366881694639)
            ·
              refine ⟨429401510274189550322541959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286267673516126366881694639 429401510274189550322541959)
              ·
                refine ⟨644102265411284325483812939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429401510274189550322541959 644102265411284325483812939)
                ·
                  refine ⟨966153398116926488225719409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644102265411284325483812939 966153398116926488225719409)
                  ·
                    refine ⟨724615048587694866169289557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966153398116926488225719409 724615048587694866169289557)
                    ·
                      refine ⟨4245791300318524606460681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 724615048587694866169289557 4245791300318524606460681)
                      ·
                        rfl

theorem cell23_8268649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_8268649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268649 prefixEnd_8268649 := by exact prefixLift 8268649
  have htrace : WordTrace (prefixWord ++ tailWord_8268649) baseStart_8268649 baseEnd_8268649 := by
    simpa [prefixWord, tailWord_8268649, baseEnd_8268649] using wordTrace_append hprefix tailTrace_8268649
  have hstable : (prefixWord ++ tailWord_8268649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268649).length < 2 ^ (prefixWord ++ tailWord_8268649).sum := by decide
  have hdescent : baseEnd_8268649 < baseStart_8268649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268666 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_8268666 : Nat := 118140960795 + 8268666 * 2 ^ 59
def prefixEnd_8268666 : Nat := 4983230072969 + 3 ^ 40 * 8268666 * 2
def baseEnd_8268666 : Nat := 4245800029489651039948103

theorem tailTrace_8268666 : CollatzResearch.WordTrace tailWord_8268666 prefixEnd_8268666 4245800029489651039948103 := by
  unfold tailWord_8268666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75395756265510683142214463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201055350041361821712571901 75395756265510683142214463)
  ·
    refine ⟨113093634398266024713321695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75395756265510683142214463 113093634398266024713321695)
    ·
      refine ⟨169640451597399037069982543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113093634398266024713321695 169640451597399037069982543)
      ·
        refine ⟨254460677396098555604973815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169640451597399037069982543 254460677396098555604973815)
        ·
          refine ⟨381691016094147833407460723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254460677396098555604973815 381691016094147833407460723)
          ·
            refine ⟨572536524141221750111191085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381691016094147833407460723 572536524141221750111191085)
            ·
              refine ⟨214701196552958156291696657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572536524141221750111191085 214701196552958156291696657)
              ·
                refine ⟨161025897414718617218772493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214701196552958156291696657 161025897414718617218772493)
                ·
                  refine ⟨60384711530519481457039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161025897414718617218772493 60384711530519481457039685)
                  ·
                    refine ⟨11322133411972402773194941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60384711530519481457039685 11322133411972402773194941)
                    ·
                      refine ⟨4245800029489651039948103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322133411972402773194941 4245800029489651039948103)
                      ·
                        rfl

theorem cell23_8268666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_8268666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268666 prefixEnd_8268666 := by exact prefixLift 8268666
  have htrace : WordTrace (prefixWord ++ tailWord_8268666) baseStart_8268666 baseEnd_8268666 := by
    simpa [prefixWord, tailWord_8268666, baseEnd_8268666] using wordTrace_append hprefix tailTrace_8268666
  have hstable : (prefixWord ++ tailWord_8268666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268666).length < 2 ^ (prefixWord ++ tailWord_8268666).sum := by decide
  have hdescent : baseEnd_8268666 < baseStart_8268666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268676 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_8268676 : Nat := 118140960795 + 8268676 * 2 ^ 59
def prefixEnd_8268676 : Nat := 4983230072969 + 3 ^ 40 * 8268676 * 2
def baseEnd_8268676 : Nat := 4245805164296196000823057

theorem tailTrace_8268676 : CollatzResearch.WordTrace tailWord_8268676 prefixEnd_8268676 4245805164296196000823057 := by
  unfold tailWord_8268676
  simp only [CollatzResearch.WordTrace]
  refine ⟨150791694896003252138360941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201055593194671002851147921 150791694896003252138360941)
  ·
    refine ⟨56546885586001219551885353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150791694896003252138360941 56546885586001219551885353)
    ·
      refine ⟨42410164189500914663914015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56546885586001219551885353 42410164189500914663914015)
      ·
        refine ⟨63615246284251371995871023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410164189500914663914015 63615246284251371995871023)
        ·
          refine ⟨95422869426377057993806535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63615246284251371995871023 95422869426377057993806535)
          ·
            refine ⟨143134304139565586990709803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95422869426377057993806535 143134304139565586990709803)
            ·
              refine ⟨214701456209348380486064705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143134304139565586990709803 214701456209348380486064705)
              ·
                refine ⟨161026092157011285364548529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214701456209348380486064705 161026092157011285364548529)
                ·
                  refine ⟨120769569117758464023411397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161026092157011285364548529 120769569117758464023411397)
                  ·
                    refine ⟨22644294209579712004389637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120769569117758464023411397 22644294209579712004389637)
                    ·
                      refine ⟨4245805164296196000823057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22644294209579712004389637 4245805164296196000823057)
                      ·
                        rfl

theorem cell23_8268676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_8268676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268676 prefixEnd_8268676 := by exact prefixLift 8268676
  have htrace : WordTrace (prefixWord ++ tailWord_8268676) baseStart_8268676 baseEnd_8268676 := by
    simpa [prefixWord, tailWord_8268676, baseEnd_8268676] using wordTrace_append hprefix tailTrace_8268676
  have hstable : (prefixWord ++ tailWord_8268676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268676).length < 2 ^ (prefixWord ++ tailWord_8268676).sum := by decide
  have hdescent : baseEnd_8268676 < baseStart_8268676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268680 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_8268680 : Nat := 118140960795 + 8268680 * 2 ^ 59
def prefixEnd_8268680 : Nat := 4983230072969 + 3 ^ 40 * 8268680 * 2
def baseEnd_8268680 : Nat := 4245807218218813985173039

theorem tailTrace_8268680 : CollatzResearch.WordTrace tailWord_8268680 prefixEnd_8268680 4245807218218813985173039 := by
  unfold tailWord_8268680
  simp only [CollatzResearch.WordTrace]
  refine ⟨150791767841996006479933747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201055690455994675306578329 150791767841996006479933747)
  ·
    refine ⟨226187651762994009719900621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150791767841996006479933747 226187651762994009719900621)
    ·
      refine ⟨84820369411122753644962733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226187651762994009719900621 84820369411122753644962733)
      ·
        refine ⟨31807638529171032616861025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84820369411122753644962733 31807638529171032616861025)
        ·
          refine ⟨23855728896878274462645769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31807638529171032616861025 23855728896878274462645769)
          ·
            refine ⟨17891796672658705846984327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23855728896878274462645769 17891796672658705846984327)
            ·
              refine ⟨26837695008988058770476491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891796672658705846984327 26837695008988058770476491)
              ·
                refine ⟨40256542513482088155714737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26837695008988058770476491 40256542513482088155714737)
                ·
                  refine ⟨30192406885111566116786053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40256542513482088155714737 30192406885111566116786053)
                  ·
                    refine ⟨5661076290958418646897385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30192406885111566116786053 5661076290958418646897385)
                    ·
                      refine ⟨4245807218218813985173039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661076290958418646897385 4245807218218813985173039)
                      ·
                        rfl

theorem cell23_8268680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_8268680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268680 prefixEnd_8268680 := by exact prefixLift 8268680
  have htrace : WordTrace (prefixWord ++ tailWord_8268680) baseStart_8268680 baseEnd_8268680 := by
    simpa [prefixWord, tailWord_8268680, baseEnd_8268680] using wordTrace_append hprefix tailTrace_8268680
  have hstable : (prefixWord ++ tailWord_8268680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268680).length < 2 ^ (prefixWord ++ tailWord_8268680).sum := by decide
  have hdescent : baseEnd_8268680 < baseStart_8268680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268694 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_8268694 : Nat := 118140960795 + 8268694 * 2 ^ 59
def prefixEnd_8268694 : Nat := 4983230072969 + 3 ^ 40 * 8268694 * 2
def baseEnd_8268694 : Nat := 1415271468982658976799325

theorem tailTrace_8268694 : CollatzResearch.WordTrace tailWord_8268694 prefixEnd_8268694 1415271468982658976799325 := by
  unfold tailWord_8268694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849002894121330834429821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201056030870627528900584757 18849002894121330834429821)
  ·
    refine ⟨7068376085295499062911183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18849002894121330834429821 7068376085295499062911183)
    ·
      refine ⟨10602564127943248594366775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7068376085295499062911183 10602564127943248594366775)
      ·
        refine ⟨15903846191914872891550163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602564127943248594366775 15903846191914872891550163)
        ·
          refine ⟨23855769287872309337325245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903846191914872891550163 23855769287872309337325245)
          ·
            refine ⟨8945913482952116001496967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23855769287872309337325245 8945913482952116001496967)
            ·
              refine ⟨13418870224428174002245451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945913482952116001496967 13418870224428174002245451)
              ·
                refine ⟨20128305336642261003368177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418870224428174002245451 20128305336642261003368177)
                ·
                  refine ⟨15096229002481695752526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20128305336642261003368177 15096229002481695752526133)
                  ·
                    refine ⟨1415271468982658976799325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096229002481695752526133 1415271468982658976799325)
                    ·
                      rfl

theorem cell23_8268694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_8268694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268694 prefixEnd_8268694 := by exact prefixLift 8268694
  have htrace : WordTrace (prefixWord ++ tailWord_8268694) baseStart_8268694 baseEnd_8268694 := by
    simpa [prefixWord, tailWord_8268694, baseEnd_8268694] using wordTrace_append hprefix tailTrace_8268694
  have hstable : (prefixWord ++ tailWord_8268694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268694).length < 2 ^ (prefixWord ++ tailWord_8268694).sum := by decide
  have hdescent : baseEnd_8268694 < baseStart_8268694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268700 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8268700 : Nat := 118140960795 + 8268700 * 2 ^ 59
def prefixEnd_8268700 : Nat := 4983230072969 + 3 ^ 40 * 8268700 * 2
def baseEnd_8268700 : Nat := 4245817487831903906922947

theorem tailTrace_8268700 : CollatzResearch.WordTrace tailWord_8268700 prefixEnd_8268700 4245817487831903906922947 := by
  unfold tailWord_8268700
  simp only [CollatzResearch.WordTrace]
  refine ⟨150792132571959778187797777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201056176762613037583730369 150792132571959778187797777)
  ·
    refine ⟨113094099428969833640848333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150792132571959778187797777 113094099428969833640848333)
    ·
      refine ⟨42410287285863687615318125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113094099428969833640848333 42410287285863687615318125)
      ·
        refine ⟨15903857732198882855744297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42410287285863687615318125 15903857732198882855744297)
        ·
          refine ⟨11927893299149162141808223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15903857732198882855744297 11927893299149162141808223)
          ·
            refine ⟨17891839948723743212712335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927893299149162141808223 17891839948723743212712335)
            ·
              refine ⟨26837759923085614819068503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891839948723743212712335 26837759923085614819068503)
              ·
                refine ⟨40256639884628422228602755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26837759923085614819068503 40256639884628422228602755)
                ·
                  refine ⟨60384959826942633342904133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40256639884628422228602755 60384959826942633342904133)
                  ·
                    refine ⟨11322179967551743751794525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60384959826942633342904133 11322179967551743751794525)
                    ·
                      refine ⟨4245817487831903906922947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322179967551743751794525 4245817487831903906922947)
                      ·
                        rfl

theorem cell23_8268700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8268700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268700 prefixEnd_8268700 := by exact prefixLift 8268700
  have htrace : WordTrace (prefixWord ++ tailWord_8268700) baseStart_8268700 baseEnd_8268700 := by
    simpa [prefixWord, tailWord_8268700, baseEnd_8268700] using wordTrace_append hprefix tailTrace_8268700
  have hstable : (prefixWord ++ tailWord_8268700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268700).length < 2 ^ (prefixWord ++ tailWord_8268700).sum := by decide
  have hdescent : baseEnd_8268700 < baseStart_8268700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268713 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 3]
def baseStart_8268713 : Nat := 118140960795 + 8268713 * 2 ^ 59
def prefixEnd_8268713 : Nat := 4983230072969 + 3 ^ 40 * 8268713 * 2
def baseEnd_8268713 : Nat := 4245824163080412356060387

theorem tailTrace_8268713 : CollatzResearch.WordTrace tailWord_8268713 prefixEnd_8268713 4245824163080412356060387 := by
  unfold tailWord_8268713
  simp only [CollatzResearch.WordTrace]
  refine ⟨301584739292872459595818793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201056492861914973063879195 301584739292872459595818793)
  ·
    refine ⟨226188554469654344696864095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301584739292872459595818793 226188554469654344696864095)
    ·
      refine ⟨339282831704481517045296143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226188554469654344696864095 339282831704481517045296143)
      ·
        refine ⟨508924247556722275567944215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339282831704481517045296143 508924247556722275567944215)
        ·
          refine ⟨763386371335083413351916323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508924247556722275567944215 763386371335083413351916323)
          ·
            refine ⟨1145079557002625120027874485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763386371335083413351916323 1145079557002625120027874485)
            ·
              refine ⟨107351208468996105002613233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1145079557002625120027874485 107351208468996105002613233)
              ·
                refine ⟨80513406351747078751959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107351208468996105002613233 80513406351747078751959925)
                ·
                  refine ⟨7548131845476288632996243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80513406351747078751959925 7548131845476288632996243)
                  ·
                    refine ⟨11322197768214432949494365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548131845476288632996243 11322197768214432949494365)
                    ·
                      refine ⟨4245824163080412356060387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322197768214432949494365 4245824163080412356060387)
                      ·
                        rfl

theorem cell23_8268713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_8268713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268713 prefixEnd_8268713 := by exact prefixLift 8268713
  have htrace : WordTrace (prefixWord ++ tailWord_8268713) baseStart_8268713 baseEnd_8268713 := by
    simpa [prefixWord, tailWord_8268713, baseEnd_8268713] using wordTrace_append hprefix tailTrace_8268713
  have hstable : (prefixWord ++ tailWord_8268713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268713).length < 2 ^ (prefixWord ++ tailWord_8268713).sum := by decide
  have hdescent : baseEnd_8268713 < baseStart_8268713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268724 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_8268724 : Nat := 118140960795 + 8268724 * 2 ^ 59
def prefixEnd_8268724 : Nat := 4983230072969 + 3 ^ 40 * 8268724 * 2
def baseEnd_8268724 : Nat := 1415276603789203937674279

theorem tailTrace_8268724 : CollatzResearch.WordTrace tailWord_8268724 prefixEnd_8268724 1415276603789203937674279 := by
  unfold tailWord_8268724
  simp only [CollatzResearch.WordTrace]
  refine ⟨150792570247916304237234613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201056760330555072316312817 150792570247916304237234613)
  ·
    refine ⟨14136803460742153522240745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150792570247916304237234613 14136803460742153522240745)
    ·
      refine ⟨10602602595556615141680559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14136803460742153522240745 10602602595556615141680559)
      ·
        refine ⟨15903903893334922712520839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602602595556615141680559 15903903893334922712520839)
        ·
          refine ⟨23855855840002384068781259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903903893334922712520839 23855855840002384068781259)
          ·
            refine ⟨35783783760003576103171889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23855855840002384068781259 35783783760003576103171889)
            ·
              refine ⟨26837837820002682077378917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35783783760003576103171889 26837837820002682077378917)
              ·
                refine ⟨5032094591250502889508547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26837837820002682077378917 5032094591250502889508547)
                ·
                  refine ⟨7548141886875754334262821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032094591250502889508547 7548141886875754334262821)
                  ·
                    refine ⟨1415276603789203937674279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548141886875754334262821 1415276603789203937674279)
                    ·
                      rfl

theorem cell23_8268724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_8268724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268724 prefixEnd_8268724 := by exact prefixLift 8268724
  have htrace : WordTrace (prefixWord ++ tailWord_8268724) baseStart_8268724 baseEnd_8268724 := by
    simpa [prefixWord, tailWord_8268724, baseEnd_8268724] using wordTrace_append hprefix tailTrace_8268724
  have hstable : (prefixWord ++ tailWord_8268724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268724).length < 2 ^ (prefixWord ++ tailWord_8268724).sum := by decide
  have hdescent : baseEnd_8268724 < baseStart_8268724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268730 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_8268730 : Nat := 118140960795 + 8268730 * 2 ^ 59
def prefixEnd_8268730 : Nat := 4983230072969 + 3 ^ 40 * 8268730 * 2
def baseEnd_8268730 : Nat := 4245832892251538789547809

theorem tailTrace_8268730 : CollatzResearch.WordTrace tailWord_8268730 prefixEnd_8268730 4245832892251538789547809 := by
  unfold tailWord_8268730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75396339833452717874796911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201056906222540580999458429 75396339833452717874796911)
  ·
    refine ⟨113094509750179076812195367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75396339833452717874796911 113094509750179076812195367)
    ·
      refine ⟨169641764625268615218293051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113094509750179076812195367 169641764625268615218293051)
      ·
        refine ⟨254462646937902922827439577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169641764625268615218293051 254462646937902922827439577)
        ·
          refine ⟨190846985203427192120579683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254462646937902922827439577 190846985203427192120579683)
          ·
            refine ⟨286270477805140788180869525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190846985203427192120579683 286270477805140788180869525)
            ·
              refine ⟨13418928647115974445978259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286270477805140788180869525 13418928647115974445978259)
              ·
                refine ⟨20128392970673961668967389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418928647115974445978259 20128392970673961668967389)
                ·
                  refine ⟨7548147364002735625862771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20128392970673961668967389 7548147364002735625862771)
                  ·
                    refine ⟨11322221046004103438794157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548147364002735625862771 11322221046004103438794157)
                    ·
                      refine ⟨4245832892251538789547809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322221046004103438794157 4245832892251538789547809)
                      ·
                        rfl

theorem cell23_8268730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_8268730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268730 prefixEnd_8268730 := by exact prefixLift 8268730
  have htrace : WordTrace (prefixWord ++ tailWord_8268730) baseStart_8268730 baseEnd_8268730 := by
    simpa [prefixWord, tailWord_8268730, baseEnd_8268730] using wordTrace_append hprefix tailTrace_8268730
  have hstable : (prefixWord ++ tailWord_8268730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268730).length < 2 ^ (prefixWord ++ tailWord_8268730).sum := by decide
  have hdescent : baseEnd_8268730 < baseStart_8268730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268750 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_8268750 : Nat := 118140960795 + 8268750 * 2 ^ 59
def prefixEnd_8268750 : Nat := 4983230072969 + 3 ^ 40 * 8268750 * 2
def baseEnd_8268750 : Nat := 1415281053954876237099239

theorem tailTrace_8268750 : CollatzResearch.WordTrace tailWord_8268750 prefixEnd_8268750 1415281053954876237099239 := by
  unfold tailWord_8268750
  simp only [CollatzResearch.WordTrace]
  refine ⟨37698261099217301864364463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201057392529158943276610469 37698261099217301864364463)
  ·
    refine ⟨56547391648825952796546695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37698261099217301864364463 56547391648825952796546695)
    ·
      refine ⟨84821087473238929194820043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56547391648825952796546695 84821087473238929194820043)
      ·
        refine ⟨127231631209858393792230065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84821087473238929194820043 127231631209858393792230065)
        ·
          refine ⟨95423723407393795344172549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127231631209858393792230065 95423723407393795344172549)
          ·
            refine ⟨17891948138886336627032353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95423723407393795344172549 17891948138886336627032353)
            ·
              refine ⟨13418961104164752470274265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891948138886336627032353 13418961104164752470274265)
              ·
                refine ⟨10064220828123564352705699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13418961104164752470274265 10064220828123564352705699)
                ·
                  refine ⟨15096331242185346529058549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10064220828123564352705699 15096331242185346529058549)
                  ·
                    refine ⟨1415281053954876237099239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096331242185346529058549 1415281053954876237099239)
                    ·
                      rfl

theorem cell23_8268750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_8268750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268750 prefixEnd_8268750 := by exact prefixLift 8268750
  have htrace : WordTrace (prefixWord ++ tailWord_8268750) baseStart_8268750 baseEnd_8268750 := by
    simpa [prefixWord, tailWord_8268750, baseEnd_8268750] using wordTrace_append hprefix tailTrace_8268750
  have hstable : (prefixWord ++ tailWord_8268750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268750).length < 2 ^ (prefixWord ++ tailWord_8268750).sum := by decide
  have hdescent : baseEnd_8268750 < baseStart_8268750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268753 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 6, 2]
def baseStart_8268753 : Nat := 118140960795 + 8268753 * 2 ^ 59
def prefixEnd_8268753 : Nat := 4983230072969 + 3 ^ 40 * 8268753 * 2
def baseEnd_8268753 : Nat := 4245844702306592199560203

theorem tailTrace_8268753 : CollatzResearch.WordTrace tailWord_8268753 prefixEnd_8268753 4245844702306592199560203 := by
  unfold tailWord_8268753
  simp only [CollatzResearch.WordTrace]
  refine ⟨301586198212727546427274913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201057465475151697618183275 301586198212727546427274913)
  ·
    refine ⟨226189648659545659820456185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301586198212727546427274913 226189648659545659820456185)
    ·
      refine ⟨169642236494659244865342139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226189648659545659820456185 169642236494659244865342139)
      ·
        refine ⟨254463354741988867298013209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169642236494659244865342139 254463354741988867298013209)
        ·
          refine ⟨190847516056491650473509907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254463354741988867298013209 190847516056491650473509907)
          ·
            refine ⟨286271274084737475710264861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190847516056491650473509907 286271274084737475710264861)
            ·
              refine ⟨107351727781776553391349323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286271274084737475710264861 107351727781776553391349323)
              ·
                refine ⟨161027591672664830087023985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107351727781776553391349323 161027591672664830087023985)
                ·
                  refine ⟨120770693754498622565267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161027591672664830087023985 120770693754498622565267989)
                  ·
                    refine ⟨5661126269742122932746937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120770693754498622565267989 5661126269742122932746937)
                    ·
                      refine ⟨4245844702306592199560203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661126269742122932746937 4245844702306592199560203)
                      ·
                        rfl

theorem cell23_8268753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_8268753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268753 prefixEnd_8268753 := by exact prefixLift 8268753
  have htrace : WordTrace (prefixWord ++ tailWord_8268753) baseStart_8268753 baseEnd_8268753 := by
    simpa [prefixWord, tailWord_8268753, baseEnd_8268753] using wordTrace_append hprefix tailTrace_8268753
  have hstable : (prefixWord ++ tailWord_8268753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268753).length < 2 ^ (prefixWord ++ tailWord_8268753).sum := by decide
  have hdescent : baseEnd_8268753 < baseStart_8268753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268776 : List Nat := [2, 1, 4, 1, 1, 1, 13]
def baseStart_8268776 : Nat := 118140960795 + 8268776 * 2 ^ 59
def prefixEnd_8268776 : Nat := 4983230072969 + 3 ^ 40 * 8268776 * 2
def baseEnd_8268776 : Nat := 52417981634094390241637

theorem tailTrace_8268776 : CollatzResearch.WordTrace tailWord_8268776 prefixEnd_8268776 52417981634094390241637 := by
  unfold tailWord_8268776
  simp only [CollatzResearch.WordTrace]
  refine ⟨150793518545822110677681091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201058024727762814236908121 150793518545822110677681091)
  ·
    refine ⟨226190277818733166016521637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150793518545822110677681091 226190277818733166016521637)
    ·
      refine ⟨42410677091012468628097807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226190277818733166016521637 42410677091012468628097807)
      ·
        refine ⟨63616015636518702942146711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410677091012468628097807 63616015636518702942146711)
        ·
          refine ⟨95424023454778054413220067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63616015636518702942146711 95424023454778054413220067)
          ·
            refine ⟨143136035182167081619830101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95424023454778054413220067 143136035182167081619830101)
            ·
              refine ⟨52417981634094390241637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 143136035182167081619830101 52417981634094390241637)
              ·
                rfl

theorem cell23_8268776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 13].length) (baseStart_8268776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268776 prefixEnd_8268776 := by exact prefixLift 8268776
  have htrace : WordTrace (prefixWord ++ tailWord_8268776) baseStart_8268776 baseEnd_8268776 := by
    simpa [prefixWord, tailWord_8268776, baseEnd_8268776] using wordTrace_append hprefix tailTrace_8268776
  have hstable : (prefixWord ++ tailWord_8268776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268776).length < 2 ^ (prefixWord ++ tailWord_8268776).sum := by decide
  have hdescent : baseEnd_8268776 < baseStart_8268776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268788 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 6]
def baseStart_8268788 : Nat := 118140960795 + 8268788 * 2 ^ 59
def prefixEnd_8268788 : Nat := 4983230072969 + 3 ^ 40 * 8268788 * 2
def baseEnd_8268788 : Nat := 471762519347722173624727

theorem tailTrace_8268788 : CollatzResearch.WordTrace tailWord_8268788 prefixEnd_8268788 471762519347722173624727 := by
  unfold tailWord_8268788
  simp only [CollatzResearch.WordTrace]
  refine ⟨150793737383800373702399509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201058316511733831603199345 150793737383800373702399509)
  ·
    refine ⟨7068456439865642517299977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150793737383800373702399509 7068456439865642517299977)
    ·
      refine ⟨5301342329899231887974983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7068456439865642517299977 5301342329899231887974983)
      ·
        refine ⟨7952013494848847831962475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301342329899231887974983 7952013494848847831962475)
        ·
          refine ⟨11928020242273271747943713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952013494848847831962475 11928020242273271747943713)
          ·
            refine ⟨8946015181704953810957785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928020242273271747943713 8946015181704953810957785)
            ·
              refine ⟨6709511386278715358218339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946015181704953810957785 6709511386278715358218339)
              ·
                refine ⟨10064267079418073037327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709511386278715358218339 10064267079418073037327509)
                ·
                  refine ⟨471762519347722173624727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10064267079418073037327509 471762519347722173624727)
                  ·
                    rfl

theorem cell23_8268788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_8268788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268788 prefixEnd_8268788 := by exact prefixLift 8268788
  have htrace : WordTrace (prefixWord ++ tailWord_8268788) baseStart_8268788 baseEnd_8268788 := by
    simpa [prefixWord, tailWord_8268788, baseEnd_8268788] using wordTrace_append hprefix tailTrace_8268788
  have hstable : (prefixWord ++ tailWord_8268788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268788).length < 2 ^ (prefixWord ++ tailWord_8268788).sum := by decide
  have hdescent : baseEnd_8268788 < baseStart_8268788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268790 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_8268790 : Nat := 118140960795 + 8268790 * 2 ^ 59
def prefixEnd_8268790 : Nat := 4983230072969 + 3 ^ 40 * 8268790 * 2
def baseEnd_8268790 : Nat := 4245863701090808554797533

theorem tailTrace_8268790 : CollatzResearch.WordTrace tailWord_8268790 prefixEnd_8268790 4245863701090808554797533 := by
  unfold tailWord_8268790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849221732099593859148239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201058365142395667830914549 18849221732099593859148239)
  ·
    refine ⟨28273832598149390788722359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18849221732099593859148239 28273832598149390788722359)
    ·
      refine ⟨42410748897224086183083539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28273832598149390788722359 42410748897224086183083539)
      ·
        refine ⟨63616123345836129274625309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410748897224086183083539 63616123345836129274625309)
        ·
          refine ⟨23856046254688548477984491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63616123345836129274625309 23856046254688548477984491)
          ·
            refine ⟨35784069382032822716976737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23856046254688548477984491 35784069382032822716976737)
            ·
              refine ⟨26838052036524617037732553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35784069382032822716976737 26838052036524617037732553)
              ·
                refine ⟨20128539027393462778299415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26838052036524617037732553 20128539027393462778299415)
                ·
                  refine ⟨30192808541090194167449123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20128539027393462778299415 30192808541090194167449123)
                  ·
                    refine ⟨45289212811635291251173685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30192808541090194167449123 45289212811635291251173685)
                    ·
                      refine ⟨4245863701090808554797533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45289212811635291251173685 4245863701090808554797533)
                      ·
                        rfl

theorem cell23_8268790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_8268790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268790 prefixEnd_8268790 := by exact prefixLift 8268790
  have htrace : WordTrace (prefixWord ++ tailWord_8268790) baseStart_8268790 baseEnd_8268790 := by
    simpa [prefixWord, tailWord_8268790, baseEnd_8268790] using wordTrace_append hprefix tailTrace_8268790
  have hstable : (prefixWord ++ tailWord_8268790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268790).length < 2 ^ (prefixWord ++ tailWord_8268790).sum := by decide
  have hdescent : baseEnd_8268790 < baseStart_8268790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268837 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_8268837 : Nat := 118140960795 + 8268837 * 2 ^ 59
def prefixEnd_8268837 : Nat := 4983230072969 + 3 ^ 40 * 8268837 * 2
def baseEnd_8268837 : Nat := 4245887834681569870909817

theorem tailTrace_8268837 : CollatzResearch.WordTrace tailWord_8268837 prefixEnd_8268837 4245887834681569870909817 := by
  unfold tailWord_8268837
  simp only [CollatzResearch.WordTrace]
  refine ⟨301589261944423228773332765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201059507962948819182221843 301589261944423228773332765)
  ·
    refine ⟨113095973229158710789999787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301589261944423228773332765 113095973229158710789999787)
    ·
      refine ⟨169643959843738066184999681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113095973229158710789999787 169643959843738066184999681)
      ·
        refine ⟨127232969882803549638749761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169643959843738066184999681 127232969882803549638749761)
        ·
          refine ⟨95424727412102662229062321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127232969882803549638749761 95424727412102662229062321)
          ·
            refine ⟨71568545559076996671796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95424727412102662229062321 71568545559076996671796741)
            ·
              refine ⟨13419102292326936875961889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71568545559076996671796741 13419102292326936875961889)
              ·
                refine ⟨10064326719245202656971417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13419102292326936875961889 10064326719245202656971417)
                ·
                  refine ⟨7548245039433901992728563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10064326719245202656971417 7548245039433901992728563)
                  ·
                    refine ⟨11322367559150852989092845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548245039433901992728563 11322367559150852989092845)
                    ·
                      refine ⟨4245887834681569870909817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322367559150852989092845 4245887834681569870909817)
                      ·
                        rfl

theorem cell23_8268837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_8268837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268837 prefixEnd_8268837 := by exact prefixLift 8268837
  have htrace : WordTrace (prefixWord ++ tailWord_8268837) baseStart_8268837 baseEnd_8268837 := by
    simpa [prefixWord, tailWord_8268837, baseEnd_8268837] using wordTrace_append hprefix tailTrace_8268837
  have hstable : (prefixWord ++ tailWord_8268837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268837).length < 2 ^ (prefixWord ++ tailWord_8268837).sum := by decide
  have hdescent : baseEnd_8268837 < baseStart_8268837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268854 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_8268854 : Nat := 118140960795 + 8268854 * 2 ^ 59
def prefixEnd_8268854 : Nat := 4983230072969 + 3 ^ 40 * 8268854 * 2
def baseEnd_8268854 : Nat := 4245896563852696304397239

theorem tailTrace_8268854 : CollatzResearch.WordTrace tailWord_8268854 prefixEnd_8268854 4245896563852696304397239 := by
  unfold tailWord_8268854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849367624085102542293851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201059921323574427117801077 18849367624085102542293851)
  ·
    refine ⟨28274051436127653813440777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18849367624085102542293851 28274051436127653813440777)
    ·
      refine ⟨21205538577095740360080583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28274051436127653813440777 21205538577095740360080583)
      ·
        refine ⟨31808307865643610540120875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21205538577095740360080583 31808307865643610540120875)
        ·
          refine ⟨47712461798465415810181313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31808307865643610540120875 47712461798465415810181313)
          ·
            refine ⟨35784346348849061857635985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47712461798465415810181313 35784346348849061857635985)
            ·
              refine ⟨26838259761636796393226989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35784346348849061857635985 26838259761636796393226989)
              ·
                refine ⟨10064347410613798647460121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26838259761636796393226989 10064347410613798647460121)
                ·
                  refine ⟨7548260557960348985595091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10064347410613798647460121 7548260557960348985595091)
                  ·
                    refine ⟨11322390836940523478392637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548260557960348985595091 11322390836940523478392637)
                    ·
                      refine ⟨4245896563852696304397239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322390836940523478392637 4245896563852696304397239)
                      ·
                        rfl

theorem cell23_8268854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_8268854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268854 prefixEnd_8268854 := by exact prefixLift 8268854
  have htrace : WordTrace (prefixWord ++ tailWord_8268854) baseStart_8268854 baseEnd_8268854 := by
    simpa [prefixWord, tailWord_8268854, baseEnd_8268854] using wordTrace_append hprefix tailTrace_8268854
  have hstable : (prefixWord ++ tailWord_8268854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268854).length < 2 ^ (prefixWord ++ tailWord_8268854).sum := by decide
  have hdescent : baseEnd_8268854 < baseStart_8268854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268863 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_8268863 : Nat := 118140960795 + 8268863 * 2 ^ 59
def prefixEnd_8268863 : Nat := 4983230072969 + 3 ^ 40 * 8268863 * 2
def baseEnd_8268863 : Nat := 4245901185178586769184697

theorem tailTrace_8268863 : CollatzResearch.WordTrace tailWord_8268863 prefixEnd_8268863 4245901185178586769184697 := by
  unfold tailWord_8268863
  simp only [CollatzResearch.WordTrace]
  refine ⟨301590210242329035213779243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201060140161552690142519495 301590210242329035213779243)
  ·
    refine ⟨452385315363493552820668865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301590210242329035213779243 452385315363493552820668865)
    ·
      refine ⟨339288986522620164615501649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452385315363493552820668865 339288986522620164615501649)
      ·
        refine ⟨254466739891965123461626237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339288986522620164615501649 254466739891965123461626237)
        ·
          refine ⟨95425027459486921298109839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254466739891965123461626237 95425027459486921298109839)
          ·
            refine ⟨143137541189230381947164759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95425027459486921298109839 143137541189230381947164759)
            ·
              refine ⟨214706311783845572920747139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143137541189230381947164759 214706311783845572920747139)
              ·
                refine ⟨322059467675768359381120709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214706311783845572920747139 322059467675768359381120709)
                ·
                  refine ⟨60386150189206567383960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322059467675768359381120709 60386150189206567383960133)
                  ·
                    refine ⟨11322403160476231384492525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60386150189206567383960133 11322403160476231384492525)
                    ·
                      refine ⟨4245901185178586769184697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322403160476231384492525 4245901185178586769184697)
                      ·
                        rfl

theorem cell23_8268863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_8268863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268863 prefixEnd_8268863 := by exact prefixLift 8268863
  have htrace : WordTrace (prefixWord ++ tailWord_8268863) baseStart_8268863 baseEnd_8268863 := by
    simpa [prefixWord, tailWord_8268863, baseEnd_8268863] using wordTrace_append hprefix tailTrace_8268863
  have hstable : (prefixWord ++ tailWord_8268863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268863).length < 2 ^ (prefixWord ++ tailWord_8268863).sum := by decide
  have hdescent : baseEnd_8268863 < baseStart_8268863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268913 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_8268913 : Nat := 118140960795 + 8268913 * 2 ^ 59
def prefixEnd_8268913 : Nat := 4983230072969 + 3 ^ 40 * 8268913 * 2
def baseEnd_8268913 : Nat := 1415308953070437191186489

theorem tailTrace_8268913 : CollatzResearch.WordTrace tailWord_8268913 prefixEnd_8268913 1415308953070437191186489 := by
  unfold tailWord_8268913
  simp only [CollatzResearch.WordTrace]
  refine ⟨301592033892147893753099393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201061355928098595835399595 301592033892147893753099393)
  ·
    refine ⟨226194025419110920314824545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301592033892147893753099393 226194025419110920314824545)
    ·
      refine ⟨169645519064333190236118409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226194025419110920314824545 169645519064333190236118409)
      ·
        refine ⟨127234139298249892677088807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169645519064333190236118409 127234139298249892677088807)
        ·
          refine ⟨190851208947374839015633211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127234139298249892677088807 190851208947374839015633211)
          ·
            refine ⟨286276813421062258523449817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190851208947374839015633211 286276813421062258523449817)
            ·
              refine ⟨214707610065796693892587363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286276813421062258523449817 214707610065796693892587363)
              ·
                refine ⟨322061415098695040838881045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214707610065796693892587363 322061415098695040838881045)
                ·
                  refine ⟨15096628832751330039322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322061415098695040838881045 15096628832751330039322549)
                  ·
                    refine ⟨1415308953070437191186489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096628832751330039322549 1415308953070437191186489)
                    ·
                      rfl

theorem cell23_8268913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_8268913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268913 prefixEnd_8268913 := by exact prefixLift 8268913
  have htrace : WordTrace (prefixWord ++ tailWord_8268913) baseStart_8268913 baseEnd_8268913 := by
    simpa [prefixWord, tailWord_8268913, baseEnd_8268913] using wordTrace_append hprefix tailTrace_8268913
  have hstable : (prefixWord ++ tailWord_8268913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268913).length < 2 ^ (prefixWord ++ tailWord_8268913).sum := by decide
  have hdescent : baseEnd_8268913 < baseStart_8268913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268920 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_8268920 : Nat := 118140960795 + 8268920 * 2 ^ 59
def prefixEnd_8268920 : Nat := 4983230072969 + 3 ^ 40 * 8268920 * 2
def baseEnd_8268920 : Nat := 4245930453575893046171935

theorem tailTrace_8268920 : CollatzResearch.WordTrace tailWord_8268920 prefixEnd_8268920 4245930453575893046171935 := by
  unfold tailWord_8268920
  simp only [CollatzResearch.WordTrace]
  refine ⟨150796144601561266974302107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201061526135415022632402809 150796144601561266974302107)
  ·
    refine ⟨226194216902341900461453161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150796144601561266974302107 226194216902341900461453161)
    ·
      refine ⟨169645662676756425346089871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226194216902341900461453161 169645662676756425346089871)
      ·
        refine ⟨254468494015134638019134807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169645662676756425346089871 254468494015134638019134807)
        ·
          refine ⟨381702741022701957028702211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254468494015134638019134807 381702741022701957028702211)
          ·
            refine ⟨572554111534052935543053317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381702741022701957028702211 572554111534052935543053317)
            ·
              refine ⟨107353895912634925414322497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572554111534052935543053317 107353895912634925414322497)
              ·
                refine ⟨80515421934476194060741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107353895912634925414322497 80515421934476194060741873)
                ·
                  refine ⟨60386566450857145545556405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80515421934476194060741873 60386566450857145545556405)
                  ·
                    refine ⟨5661240604767857394895913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60386566450857145545556405 5661240604767857394895913)
                    ·
                      refine ⟨4245930453575893046171935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661240604767857394895913 4245930453575893046171935)
                      ·
                        rfl

theorem cell23_8268920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_8268920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268920 prefixEnd_8268920 := by exact prefixLift 8268920
  have htrace : WordTrace (prefixWord ++ tailWord_8268920) baseStart_8268920 baseEnd_8268920 := by
    simpa [prefixWord, tailWord_8268920, baseEnd_8268920] using wordTrace_append hprefix tailTrace_8268920
  have hstable : (prefixWord ++ tailWord_8268920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268920).length < 2 ^ (prefixWord ++ tailWord_8268920).sum := by decide
  have hdescent : baseEnd_8268920 < baseStart_8268920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8268963 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_8268963 : Nat := 118140960795 + 8268963 * 2 ^ 59
def prefixEnd_8268963 : Nat := 4983230072969 + 3 ^ 40 * 8268963 * 2
def baseEnd_8268963 : Nat := 4245952533244036377934237

theorem tailTrace_8268963 : CollatzResearch.WordTrace tailWord_8268963 prefixEnd_8268963 4245952533244036377934237 := by
  unfold tailWord_8268963
  simp only [CollatzResearch.WordTrace]
  refine ⟨301593857541966752292419543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201062571694644501528279695 301593857541966752292419543)
  ·
    refine ⟨452390786312950128438629315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301593857541966752292419543 452390786312950128438629315)
    ·
      refine ⟨678586179469425192657943973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452390786312950128438629315 678586179469425192657943973)
      ·
        refine ⟨127234908650517223623364495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678586179469425192657943973 127234908650517223623364495)
        ·
          refine ⟨190852362975775835435046743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127234908650517223623364495 190852362975775835435046743)
          ·
            refine ⟨286278544463663753152570115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190852362975775835435046743 286278544463663753152570115)
            ·
              refine ⟨429417816695495629728855173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286278544463663753152570115 429417816695495629728855173)
              ·
                refine ⟨80515840630405430574160345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429417816695495629728855173 80515840630405430574160345)
                ·
                  refine ⟨60386880472804072930620259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80515840630405430574160345 60386880472804072930620259)
                  ·
                    refine ⟨90580320709206109395930389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60386880472804072930620259 90580320709206109395930389)
                    ·
                      refine ⟨4245952533244036377934237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90580320709206109395930389 4245952533244036377934237)
                      ·
                        rfl

theorem cell23_8268963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_8268963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8268963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8268963 prefixEnd_8268963 := by exact prefixLift 8268963
  have htrace : WordTrace (prefixWord ++ tailWord_8268963) baseStart_8268963 baseEnd_8268963 := by
    simpa [prefixWord, tailWord_8268963, baseEnd_8268963] using wordTrace_append hprefix tailTrace_8268963
  have hstable : (prefixWord ++ tailWord_8268963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8268963).length < 2 ^ (prefixWord ++ tailWord_8268963).sum := by decide
  have hdescent : baseEnd_8268963 < baseStart_8268963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8268963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269010 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_8269010 : Nat := 118140960795 + 8269010 * 2 ^ 59
def prefixEnd_8269010 : Nat := 4983230072969 + 3 ^ 40 * 8269010 * 2
def baseEnd_8269010 : Nat := 4245976666834797694046521

theorem tailTrace_8269010 : CollatzResearch.WordTrace tailWord_8269010 prefixEnd_8269010 4245976666834797694046521 := by
  unfold tailWord_8269010
  simp only [CollatzResearch.WordTrace]
  refine ⟨75398892943199119829845121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201063714515197652879586989 75398892943199119829845121)
  ·
    refine ⟨56549169707399339872383841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75398892943199119829845121 56549169707399339872383841)
    ·
      refine ⟨42411877280549504904287881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56549169707399339872383841 42411877280549504904287881)
      ·
        refine ⟨31808907960412128678215911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42411877280549504904287881 31808907960412128678215911)
        ·
          refine ⟨47713361940618193017323867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31808907960412128678215911 47713361940618193017323867)
          ·
            refine ⟨71570042910927289525985801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47713361940618193017323867 71570042910927289525985801)
            ·
              refine ⟨53677532183195467144489351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71570042910927289525985801 53677532183195467144489351)
              ·
                refine ⟨80516298274793200716734027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53677532183195467144489351 80516298274793200716734027)
                ·
                  refine ⟨120774447412189801075101041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80516298274793200716734027 120774447412189801075101041)
                  ·
                    refine ⟨90580835559142350806325781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120774447412189801075101041 90580835559142350806325781)
                    ·
                      refine ⟨4245976666834797694046521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90580835559142350806325781 4245976666834797694046521)
                      ·
                        rfl

theorem cell23_8269010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_8269010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269010 prefixEnd_8269010 := by exact prefixLift 8269010
  have htrace : WordTrace (prefixWord ++ tailWord_8269010) baseStart_8269010 baseEnd_8269010 := by
    simpa [prefixWord, tailWord_8269010, baseEnd_8269010] using wordTrace_append hprefix tailTrace_8269010
  have hstable : (prefixWord ++ tailWord_8269010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269010).length < 2 ^ (prefixWord ++ tailWord_8269010).sum := by decide
  have hdescent : baseEnd_8269010 < baseStart_8269010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269017 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 3]
def baseStart_8269017 : Nat := 118140960795 + 8269017 * 2 ^ 59
def prefixEnd_8269017 : Nat := 4983230072969 + 3 ^ 40 * 8269017 * 2
def baseEnd_8269017 : Nat := 4245980261199379166658989

theorem tailTrace_8269017 : CollatzResearch.WordTrace tailWord_8269017 prefixEnd_8269017 4245980261199379166658989 := by
  unfold tailWord_8269017
  simp only [CollatzResearch.WordTrace]
  refine ⟨301595827083771119514885305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201063884722514079676590203 301595827083771119514885305)
  ·
    refine ⟨226196870312828339636163979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301595827083771119514885305 226196870312828339636163979)
    ·
      refine ⟨339295305469242509454245969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226196870312828339636163979 339295305469242509454245969)
      ·
        refine ⟨254471479101931882090684477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339295305469242509454245969 254471479101931882090684477)
        ·
          refine ⟨95426804663224455784006679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254471479101931882090684477 95426804663224455784006679)
          ·
            refine ⟨143140206994836683676010019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95426804663224455784006679 143140206994836683676010019)
            ·
              refine ⟨214710310492255025514015029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143140206994836683676010019 214710310492255025514015029)
              ·
                refine ⟨20129091608648908641938909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214710310492255025514015029 20129091608648908641938909)
                ·
                  refine ⟨7548409353243340740727091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20129091608648908641938909 7548409353243340740727091)
                  ·
                    refine ⟨11322614029865011111090637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548409353243340740727091 11322614029865011111090637)
                    ·
                      refine ⟨4245980261199379166658989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322614029865011111090637 4245980261199379166658989)
                      ·
                        rfl

theorem cell23_8269017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_8269017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269017 prefixEnd_8269017 := by exact prefixLift 8269017
  have htrace : WordTrace (prefixWord ++ tailWord_8269017) baseStart_8269017 baseEnd_8269017 := by
    simpa [prefixWord, tailWord_8269017, baseEnd_8269017] using wordTrace_append hprefix tailTrace_8269017
  have hstable : (prefixWord ++ tailWord_8269017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269017).length < 2 ^ (prefixWord ++ tailWord_8269017).sum := by decide
  have hdescent : baseEnd_8269017 < baseStart_8269017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269034 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_8269034 : Nat := 118140960795 + 8269034 * 2 ^ 59
def prefixEnd_8269034 : Nat := 4983230072969 + 3 ^ 40 * 8269034 * 2
def baseEnd_8269034 : Nat := 4245988990370505600146411

theorem tailTrace_8269034 : CollatzResearch.WordTrace tailWord_8269034 prefixEnd_8269034 4245988990370505600146411 := by
  unfold tailWord_8269034
  simp only [CollatzResearch.WordTrace]
  refine ⟨75399111781177382854563539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201064298083139687612169437 75399111781177382854563539)
  ·
    refine ⟨113098667671766074281845309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75399111781177382854563539 113098667671766074281845309)
    ·
      refine ⟨42412000376912277855691991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113098667671766074281845309 42412000376912277855691991)
      ·
        refine ⟨63618000565368416783537987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42412000376912277855691991 63618000565368416783537987)
        ·
          refine ⟨95427000848052625175306981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63618000565368416783537987 95427000848052625175306981)
          ·
            refine ⟨17892562659009867220370059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95427000848052625175306981 17892562659009867220370059)
            ·
              refine ⟨26838843988514800830555089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892562659009867220370059 26838843988514800830555089)
              ·
                refine ⟨20129132991386100622916317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26838843988514800830555089 20129132991386100622916317)
                ·
                  refine ⟨7548424871769787733593619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20129132991386100622916317 7548424871769787733593619)
                  ·
                    refine ⟨11322637307654681600390429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548424871769787733593619 11322637307654681600390429)
                    ·
                      refine ⟨4245988990370505600146411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322637307654681600390429 4245988990370505600146411)
                      ·
                        rfl

theorem cell23_8269034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_8269034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269034 prefixEnd_8269034 := by exact prefixLift 8269034
  have htrace : WordTrace (prefixWord ++ tailWord_8269034) baseStart_8269034 baseEnd_8269034 := by
    simpa [prefixWord, tailWord_8269034, baseEnd_8269034] using wordTrace_append hprefix tailTrace_8269034
  have hstable : (prefixWord ++ tailWord_8269034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269034).length < 2 ^ (prefixWord ++ tailWord_8269034).sum := by decide
  have hdescent : baseEnd_8269034 < baseStart_8269034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269037 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_8269037 : Nat := 118140960795 + 8269037 * 2 ^ 59
def prefixEnd_8269037 : Nat := 4983230072969 + 3 ^ 40 * 8269037 * 2
def baseEnd_8269037 : Nat := 1415330176937489696136299

theorem tailTrace_8269037 : CollatzResearch.WordTrace tailWord_8269037 prefixEnd_8269037 1415330176937489696136299 := by
  unfold tailWord_8269037
  simp only [CollatzResearch.WordTrace]
  refine ⟨301596556543698662930613365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201064371029132441953742243 301596556543698662930613365)
  ·
    refine ⟨28274677175971749649745003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301596556543698662930613365 28274677175971749649745003)
    ·
      refine ⟨42412015763957624474617505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28274677175971749649745003 42412015763957624474617505)
      ·
        refine ⟨31809011822968218355963129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42412015763957624474617505 31809011822968218355963129)
        ·
          refine ⟨23856758867226163766972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31809011822968218355963129 23856758867226163766972347)
          ·
            refine ⟨35785138300839245650458521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23856758867226163766972347 35785138300839245650458521)
            ·
              refine ⟨26838853725629434237843891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35785138300839245650458521 26838853725629434237843891)
              ·
                refine ⟨40258280588444151356765837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26838853725629434237843891 40258280588444151356765837)
                ·
                  refine ⟨15096855220666556758787189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40258280588444151356765837 15096855220666556758787189)
                  ·
                    refine ⟨1415330176937489696136299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096855220666556758787189 1415330176937489696136299)
                    ·
                      rfl

theorem cell23_8269037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_8269037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269037 prefixEnd_8269037 := by exact prefixLift 8269037
  have htrace : WordTrace (prefixWord ++ tailWord_8269037) baseStart_8269037 baseEnd_8269037 := by
    simpa [prefixWord, tailWord_8269037, baseEnd_8269037] using wordTrace_append hprefix tailTrace_8269037
  have hstable : (prefixWord ++ tailWord_8269037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269037).length < 2 ^ (prefixWord ++ tailWord_8269037).sum := by decide
  have hdescent : baseEnd_8269037 < baseStart_8269037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269050 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_8269050 : Nat := 118140960795 + 8269050 * 2 ^ 59
def prefixEnd_8269050 : Nat := 4983230072969 + 3 ^ 40 * 8269050 * 2
def baseEnd_8269050 : Nat := 1415332402020325845848779

theorem tailTrace_8269050 : CollatzResearch.WordTrace tailWord_8269050 prefixEnd_8269050 1415332402020325845848779 := by
  unfold tailWord_8269050
  simp only [CollatzResearch.WordTrace]
  refine ⟨75399257673162891537709151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201064687128434377433891069 75399257673162891537709151)
  ·
    refine ⟨113098886509744337306563727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75399257673162891537709151 113098886509744337306563727)
    ·
      refine ⟨169648329764616505959845591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113098886509744337306563727 169648329764616505959845591)
      ·
        refine ⟨254472494646924758939768387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169648329764616505959845591 254472494646924758939768387)
        ·
          refine ⟨381708741970387138409652581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254472494646924758939768387 381708741970387138409652581)
          ·
            refine ⟨71570389119447588451809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381708741970387138409652581 71570389119447588451809859)
            ·
              refine ⟨107355583679171382677714789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71570389119447588451809859 107355583679171382677714789)
              ·
                refine ⟨20129171939844634252071523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107355583679171382677714789 20129171939844634252071523)
                ·
                  refine ⟨30193757909766951378107285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20129171939844634252071523 30193757909766951378107285)
                  ·
                    refine ⟨1415332402020325845848779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30193757909766951378107285 1415332402020325845848779)
                    ·
                      rfl

theorem cell23_8269050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_8269050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269050 prefixEnd_8269050 := by exact prefixLift 8269050
  have htrace : WordTrace (prefixWord ++ tailWord_8269050) baseStart_8269050 baseEnd_8269050 := by
    simpa [prefixWord, tailWord_8269050, baseEnd_8269050] using wordTrace_append hprefix tailTrace_8269050
  have hstable : (prefixWord ++ tailWord_8269050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269050).length < 2 ^ (prefixWord ++ tailWord_8269050).sum := by decide
  have hdescent : baseEnd_8269050 < baseStart_8269050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269054 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_8269054 : Nat := 118140960795 + 8269054 * 2 ^ 59
def prefixEnd_8269054 : Nat := 4983230072969 + 3 ^ 40 * 8269054 * 2
def baseEnd_8269054 : Nat := 1415333086661198507298773

theorem tailTrace_8269054 : CollatzResearch.WordTrace tailWord_8269054 prefixEnd_8269054 1415333086661198507298773 := by
  unfold tailWord_8269054
  simp only [CollatzResearch.WordTrace]
  refine ⟨37699647073079634354247777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201064784389758049889321477 37699647073079634354247777)
  ·
    refine ⟨28274735304809725765685833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37699647073079634354247777 28274735304809725765685833)
    ·
      refine ⟨21206051478607294324264375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28274735304809725765685833 21206051478607294324264375)
      ·
        refine ⟨31809077217910941486396563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206051478607294324264375 31809077217910941486396563)
        ·
          refine ⟨47713615826866412229594845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31809077217910941486396563 47713615826866412229594845)
          ·
            refine ⟨17892605935074904586098067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47713615826866412229594845 17892605935074904586098067)
            ·
              refine ⟨26838908902612356879147101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892605935074904586098067 26838908902612356879147101)
              ·
                refine ⟨10064590838479633829680163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26838908902612356879147101 10064590838479633829680163)
                ·
                  refine ⟨15096886257719450744520245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10064590838479633829680163 15096886257719450744520245)
                  ·
                    refine ⟨1415333086661198507298773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15096886257719450744520245 1415333086661198507298773)
                    ·
                      rfl

theorem cell23_8269054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_8269054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269054 prefixEnd_8269054 := by exact prefixLift 8269054
  have htrace : WordTrace (prefixWord ++ tailWord_8269054) baseStart_8269054 baseEnd_8269054 := by
    simpa [prefixWord, tailWord_8269054, baseEnd_8269054] using wordTrace_append hprefix tailTrace_8269054
  have hstable : (prefixWord ++ tailWord_8269054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269054).length < 2 ^ (prefixWord ++ tailWord_8269054).sum := by decide
  have hdescent : baseEnd_8269054 < baseStart_8269054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269067 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 4, 4]
def baseStart_8269067 : Nat := 118140960795 + 8269067 * 2 ^ 59
def prefixEnd_8269067 : Nat := 4983230072969 + 3 ^ 40 * 8269067 * 2
def baseEnd_8269067 : Nat := 1415335311744034657011253

theorem tailTrace_8269067 : CollatzResearch.WordTrace tailWord_8269067 prefixEnd_8269067 1415335311744034657011253 := by
  unfold tailWord_8269067
  simp only [CollatzResearch.WordTrace]
  refine ⟨301597650733589978054205455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201065100489059985369470303 301597650733589978054205455)
  ·
    refine ⟨452396476100384967081308183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301597650733589978054205455 452396476100384967081308183)
    ·
      refine ⟨678594714150577450621962275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452396476100384967081308183 678594714150577450621962275)
      ·
        refine ⟨1017892071225866175932943413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678594714150577450621962275 1017892071225866175932943413)
        ·
          refine ⟨95427381677424953993713445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1017892071225866175932943413 95427381677424953993713445)
          ·
            refine ⟨17892634064517178873821271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95427381677424953993713445 17892634064517178873821271)
            ·
              refine ⟨26838951096775768310731907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892634064517178873821271 26838951096775768310731907)
              ·
                refine ⟨40258426645163652466097861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26838951096775768310731907 40258426645163652466097861)
                ·
                  refine ⟨7548454995968184837393349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40258426645163652466097861 7548454995968184837393349)
                  ·
                    refine ⟨1415335311744034657011253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548454995968184837393349 1415335311744034657011253)
                    ·
                      rfl

theorem cell23_8269067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 4].length) (baseStart_8269067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269067 prefixEnd_8269067 := by exact prefixLift 8269067
  have htrace : WordTrace (prefixWord ++ tailWord_8269067) baseStart_8269067 baseEnd_8269067 := by
    simpa [prefixWord, tailWord_8269067, baseEnd_8269067] using wordTrace_append hprefix tailTrace_8269067
  have hstable : (prefixWord ++ tailWord_8269067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269067).length < 2 ^ (prefixWord ++ tailWord_8269067).sum := by decide
  have hdescent : baseEnd_8269067 < baseStart_8269067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269087 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_8269087 : Nat := 118140960795 + 8269087 * 2 ^ 59
def prefixEnd_8269087 : Nat := 4983230072969 + 3 ^ 40 * 8269087 * 2
def baseEnd_8269087 : Nat := 4246016204845193892783667

theorem tailTrace_8269087 : CollatzResearch.WordTrace tailWord_8269087 prefixEnd_8269087 4246016204845193892783667 := by
  unfold tailWord_8269087
  simp only [CollatzResearch.WordTrace]
  refine ⟨301598380193517521469933515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201065586795678347646622343 301598380193517521469933515)
  ·
    refine ⟨452397570290276282204900273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301598380193517521469933515 452397570290276282204900273)
    ·
      refine ⟨339298177717707211653675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452397570290276282204900273 339298177717707211653675205)
      ·
        refine ⟨63618408322070102185064101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339298177717707211653675205 63618408322070102185064101)
        ·
          refine ⟨11928451560388144159699519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63618408322070102185064101 11928451560388144159699519)
          ·
            refine ⟨17892677340582216239549279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11928451560388144159699519 17892677340582216239549279)
            ·
              refine ⟨26839016010873324359323919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892677340582216239549279 26839016010873324359323919)
              ·
                refine ⟨40258524016309986538985879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26839016010873324359323919 40258524016309986538985879)
                ·
                  refine ⟨60387786024464979808478819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40258524016309986538985879 60387786024464979808478819)
                  ·
                    refine ⟨90581679036697469712718229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60387786024464979808478819 90581679036697469712718229)
                    ·
                      refine ⟨4246016204845193892783667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90581679036697469712718229 4246016204845193892783667)
                      ·
                        rfl

theorem cell23_8269087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_8269087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269087 prefixEnd_8269087 := by exact prefixLift 8269087
  have htrace : WordTrace (prefixWord ++ tailWord_8269087) baseStart_8269087 baseEnd_8269087 := by
    simpa [prefixWord, tailWord_8269087, baseEnd_8269087] using wordTrace_append hprefix tailTrace_8269087
  have hstable : (prefixWord ++ tailWord_8269087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269087).length < 2 ^ (prefixWord ++ tailWord_8269087).sum := by decide
  have hdescent : baseEnd_8269087 < baseStart_8269087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269120 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_8269120 : Nat := 118140960795 + 8269120 * 2 ^ 59
def prefixEnd_8269120 : Nat := 4983230072969 + 3 ^ 40 * 8269120 * 2
def baseEnd_8269120 : Nat := 4246033149706792263671015

theorem tailTrace_8269120 : CollatzResearch.WordTrace tailWord_8269120 prefixEnd_8269120 4246033149706792263671015 := by
  unfold tailWord_8269120
  simp only [CollatzResearch.WordTrace]
  refine ⟨150799791901198984052942407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201066389201598645403923209 150799791901198984052942407)
  ·
    refine ⟨226199687851798476079413611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150799791901198984052942407 226199687851798476079413611)
    ·
      refine ⟨339299531777697714119120417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226199687851798476079413611 339299531777697714119120417)
      ·
        refine ⟨254474648833273285589340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339299531777697714119120417 254474648833273285589340313)
        ·
          refine ⟨190855986624954964192005235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254474648833273285589340313 190855986624954964192005235)
          ·
            refine ⟨286283979937432446288007853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190855986624954964192005235 286283979937432446288007853)
            ·
              refine ⟨107356492476537167358002945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286283979937432446288007853 107356492476537167358002945)
              ·
                refine ⟨80517369357402875518502209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107356492476537167358002945 80517369357402875518502209)
                ·
                  refine ⟨60388027018052156638876657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80517369357402875518502209 60388027018052156638876657)
                  ·
                    refine ⟨45291020263539117479157493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60388027018052156638876657 45291020263539117479157493)
                    ·
                      refine ⟨4246033149706792263671015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45291020263539117479157493 4246033149706792263671015)
                      ·
                        rfl

theorem cell23_8269120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_8269120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269120 prefixEnd_8269120 := by exact prefixLift 8269120
  have htrace : WordTrace (prefixWord ++ tailWord_8269120) baseStart_8269120 baseEnd_8269120 := by
    simpa [prefixWord, tailWord_8269120, baseEnd_8269120] using wordTrace_append hprefix tailTrace_8269120
  have hstable : (prefixWord ++ tailWord_8269120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269120).length < 2 ^ (prefixWord ++ tailWord_8269120).sum := by decide
  have hdescent : baseEnd_8269120 < baseStart_8269120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269134 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_8269134 : Nat := 118140960795 + 8269134 * 2 ^ 59
def prefixEnd_8269134 : Nat := 4983230072969 + 3 ^ 40 * 8269134 * 2
def baseEnd_8269134 : Nat := 4246040338435955208895951

theorem tailTrace_8269134 : CollatzResearch.WordTrace tailWord_8269134 prefixEnd_8269134 4246040338435955208895951 := by
  unfold tailWord_8269134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700011803043406062111807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201066729616231498997929637 37700011803043406062111807)
  ·
    refine ⟨56550017704565109093167711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37700011803043406062111807 56550017704565109093167711)
    ·
      refine ⟨84825026556847663639751567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56550017704565109093167711 84825026556847663639751567)
      ·
        refine ⟨127237539835271495459627351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84825026556847663639751567 127237539835271495459627351)
        ·
          refine ⟨190856309752907243189441027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127237539835271495459627351 190856309752907243189441027)
          ·
            refine ⟨286284464629360864784161541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190856309752907243189441027 286284464629360864784161541)
            ·
              refine ⟨53678337118005162147030289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286284464629360864784161541 53678337118005162147030289)
              ·
                refine ⟨40258752838503871610272717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53678337118005162147030289 40258752838503871610272717)
                ·
                  refine ⟨15097032314438951853852269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40258752838503871610272717 15097032314438951853852269)
                  ·
                    refine ⟨5661387117914606945194601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15097032314438951853852269 5661387117914606945194601)
                    ·
                      refine ⟨4246040338435955208895951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661387117914606945194601 4246040338435955208895951)
                      ·
                        rfl

theorem cell23_8269134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_8269134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269134 prefixEnd_8269134 := by exact prefixLift 8269134
  have htrace : WordTrace (prefixWord ++ tailWord_8269134) baseStart_8269134 baseEnd_8269134 := by
    simpa [prefixWord, tailWord_8269134, baseEnd_8269134] using wordTrace_append hprefix tailTrace_8269134
  have hstable : (prefixWord ++ tailWord_8269134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269134).length < 2 ^ (prefixWord ++ tailWord_8269134).sum := by decide
  have hdescent : baseEnd_8269134 < baseStart_8269134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269141 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_8269141 : Nat := 118140960795 + 8269141 * 2 ^ 59
def prefixEnd_8269141 : Nat := 4983230072969 + 3 ^ 40 * 8269141 * 2
def baseEnd_8269141 : Nat := 4246043932800536681508419

theorem tailTrace_8269141 : CollatzResearch.WordTrace tailWord_8269141 prefixEnd_8269141 4246043932800536681508419 := by
  unfold tailWord_8269141
  simp only [CollatzResearch.WordTrace]
  refine ⟨301600349735321888692399277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201066899823547925794932851 301600349735321888692399277)
  ·
    refine ⟨113100131150745708259649729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301600349735321888692399277 113100131150745708259649729)
    ·
      refine ⟨84825098363059281194737297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113100131150745708259649729 84825098363059281194737297)
      ·
        refine ⟨63618823772294460896052973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84825098363059281194737297 63618823772294460896052973)
        ·
          refine ⟨23857058914610422836019865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63618823772294460896052973 23857058914610422836019865)
          ·
            refine ⟨17892794185957817127014899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23857058914610422836019865 17892794185957817127014899)
            ·
              refine ⟨26839191278936725690522349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892794185957817127014899 26839191278936725690522349)
              ·
                refine ⟨10064696729601272133945881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26839191278936725690522349 10064696729601272133945881)
                ·
                  refine ⟨7548522547200954100459411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10064696729601272133945881 7548522547200954100459411)
                  ·
                    refine ⟨11322783820801431150689117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548522547200954100459411 11322783820801431150689117)
                    ·
                      refine ⟨4246043932800536681508419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322783820801431150689117 4246043932800536681508419)
                      ·
                        rfl

theorem cell23_8269141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_8269141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269141 prefixEnd_8269141 := by exact prefixLift 8269141
  have htrace : WordTrace (prefixWord ++ tailWord_8269141) baseStart_8269141 baseEnd_8269141 := by
    simpa [prefixWord, tailWord_8269141, baseEnd_8269141] using wordTrace_append hprefix tailTrace_8269141
  have hstable : (prefixWord ++ tailWord_8269141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269141).length < 2 ^ (prefixWord ++ tailWord_8269141).sum := by decide
  have hdescent : baseEnd_8269141 < baseStart_8269141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269142 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8269142 : Nat := 118140960795 + 8269142 * 2 ^ 59
def prefixEnd_8269142 : Nat := 4983230072969 + 3 ^ 40 * 8269142 * 2
def baseEnd_8269142 : Nat := 4246044446281191177595915

theorem tailTrace_8269142 : CollatzResearch.WordTrace tailWord_8269142 prefixEnd_8269142 4246044446281191177595915 := by
  unfold tailWord_8269142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850024138019891616449105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201066924138878843908790453 18850024138019891616449105)
  ·
    refine ⟨14137518103514918712336829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18850024138019891616449105 14137518103514918712336829)
    ·
      refine ⟨5301569288818094517126311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14137518103514918712336829 5301569288818094517126311)
      ·
        refine ⟨7952353933227141775689467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301569288818094517126311 7952353933227141775689467)
        ·
          refine ⟨11928530899840712663534201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952353933227141775689467 11928530899840712663534201)
          ·
            refine ⟨8946398174880534497650651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928530899840712663534201 8946398174880534497650651)
            ·
              refine ⟨13419597262320801746475977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946398174880534497650651 13419597262320801746475977)
              ·
                refine ⟨10064697946740601309856983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13419597262320801746475977 10064697946740601309856983)
                ·
                  refine ⟨15097046920110901964785475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10064697946740601309856983 15097046920110901964785475)
                  ·
                    refine ⟨22645570380166352947178213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15097046920110901964785475 22645570380166352947178213)
                    ·
                      refine ⟨4246044446281191177595915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22645570380166352947178213 4246044446281191177595915)
                      ·
                        rfl

theorem cell23_8269142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8269142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269142 prefixEnd_8269142 := by exact prefixLift 8269142
  have htrace : WordTrace (prefixWord ++ tailWord_8269142) baseStart_8269142 baseEnd_8269142 := by
    simpa [prefixWord, tailWord_8269142, baseEnd_8269142] using wordTrace_append hprefix tailTrace_8269142
  have hstable : (prefixWord ++ tailWord_8269142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269142).length < 2 ^ (prefixWord ++ tailWord_8269142).sum := by decide
  have hdescent : baseEnd_8269142 < baseStart_8269142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269164 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_8269164 : Nat := 118140960795 + 8269164 * 2 ^ 59
def prefixEnd_8269164 : Nat := 4983230072969 + 3 ^ 40 * 8269164 * 2
def baseEnd_8269164 : Nat := 4246055742855590091520813

theorem tailTrace_8269164 : CollatzResearch.WordTrace tailWord_8269164 prefixEnd_8269164 4246055742855590091520813 := by
  unfold tailWord_8269164
  simp only [CollatzResearch.WordTrace]
  refine ⟨150800594307119281810243273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201067459076159042413657697 150800594307119281810243273)
  ·
    refine ⟨113100445730339461357682455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150800594307119281810243273 113100445730339461357682455)
    ·
      refine ⟨169650668595509192036523683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113100445730339461357682455 169650668595509192036523683)
      ·
        refine ⟨254476002893263788054785525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169650668595509192036523683 254476002893263788054785525)
        ·
          refine ⟨23857125271243480130136143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254476002893263788054785525 23857125271243480130136143)
          ·
            refine ⟨35785687906865220195204215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23857125271243480130136143 35785687906865220195204215)
            ·
              refine ⟨53678531860297830292806323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35785687906865220195204215 53678531860297830292806323)
              ·
                refine ⟨80517797790446745439209485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53678531860297830292806323 80517797790446745439209485)
                ·
                  refine ⟨30194174171417529539703557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80517797790446745439209485 30194174171417529539703557)
                  ·
                    refine ⟨5661407657140786788694417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30194174171417529539703557 5661407657140786788694417)
                    ·
                      refine ⟨4246055742855590091520813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661407657140786788694417 4246055742855590091520813)
                      ·
                        rfl

theorem cell23_8269164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_8269164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269164 prefixEnd_8269164 := by exact prefixLift 8269164
  have htrace : WordTrace (prefixWord ++ tailWord_8269164) baseStart_8269164 baseEnd_8269164 := by
    simpa [prefixWord, tailWord_8269164, baseEnd_8269164] using wordTrace_append hprefix tailTrace_8269164
  have hstable : (prefixWord ++ tailWord_8269164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269164).length < 2 ^ (prefixWord ++ tailWord_8269164).sum := by decide
  have hdescent : baseEnd_8269164 < baseStart_8269164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269198 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_8269198 : Nat := 118140960795 + 8269198 * 2 ^ 59
def prefixEnd_8269198 : Nat := 4983230072969 + 3 ^ 40 * 8269198 * 2
def baseEnd_8269198 : Nat := 4246073201197842958495657

theorem tailTrace_8269198 : CollatzResearch.WordTrace tailWord_8269198 prefixEnd_8269198 4246073201197842958495657 := by
  unfold tailWord_8269198
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700303587014423428403031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201068285797410258284816165 37700303587014423428403031)
  ·
    refine ⟨56550455380521635142604547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37700303587014423428403031 56550455380521635142604547)
    ·
      refine ⟨84825683070782452713906821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56550455380521635142604547 84825683070782452713906821)
      ·
        refine ⟨15904815575771709883857529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84825683070782452713906821 15904815575771709883857529)
        ·
          refine ⟨11928611681828782412893147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15904815575771709883857529 11928611681828782412893147)
          ·
            refine ⟨17892917522743173619339721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11928611681828782412893147 17892917522743173619339721)
            ·
              refine ⟨13419688142057380214504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17892917522743173619339721 13419688142057380214504791)
              ·
                refine ⟨20129532213086070321757187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419688142057380214504791 20129532213086070321757187)
                ·
                  refine ⟨30194298319629105482635781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20129532213086070321757187 30194298319629105482635781)
                  ·
                    refine ⟨5661430934930457277994209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30194298319629105482635781 5661430934930457277994209)
                    ·
                      refine ⟨4246073201197842958495657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661430934930457277994209 4246073201197842958495657)
                      ·
                        rfl

theorem cell23_8269198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_8269198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269198 prefixEnd_8269198 := by exact prefixLift 8269198
  have htrace : WordTrace (prefixWord ++ tailWord_8269198) baseStart_8269198 baseEnd_8269198 := by
    simpa [prefixWord, tailWord_8269198, baseEnd_8269198] using wordTrace_append hprefix tailTrace_8269198
  have hstable : (prefixWord ++ tailWord_8269198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269198).length < 2 ^ (prefixWord ++ tailWord_8269198).sum := by decide
  have hdescent : baseEnd_8269198 < baseStart_8269198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269204 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 7]
def baseStart_8269204 : Nat := 118140960795 + 8269204 * 2 ^ 59
def prefixEnd_8269204 : Nat := 4983230072969 + 3 ^ 40 * 8269204 * 2
def baseEnd_8269204 : Nat := 471786253564641103891181

theorem tailTrace_8269204 : CollatzResearch.WordTrace tailWord_8269204 prefixEnd_8269204 471786253564641103891181 := by
  unfold tailWord_8269204
  simp only [CollatzResearch.WordTrace]
  refine ⟨150801323767046825225971333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201068431689395766967961777 150801323767046825225971333)
  ·
    refine ⟨28275248206321279729869625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150801323767046825225971333 28275248206321279729869625)
    ·
      refine ⟨21206436154740959797402219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28275248206321279729869625 21206436154740959797402219)
      ·
        refine ⟨31809654232111439696103329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206436154740959797402219 31809654232111439696103329)
        ·
          refine ⟨23857240674083579772077497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31809654232111439696103329 23857240674083579772077497)
          ·
            refine ⟨17892930505562684829058123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23857240674083579772077497 17892930505562684829058123)
            ·
              refine ⟨26839395758344027243587185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892930505562684829058123 26839395758344027243587185)
              ·
                refine ⟨20129546818758020432690389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26839395758344027243587185 20129546818758020432690389)
                ·
                  refine ⟨471786253564641103891181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20129546818758020432690389 471786253564641103891181)
                  ·
                    rfl

theorem cell23_8269204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_8269204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269204 prefixEnd_8269204 := by exact prefixLift 8269204
  have htrace : WordTrace (prefixWord ++ tailWord_8269204) baseStart_8269204 baseEnd_8269204 := by
    simpa [prefixWord, tailWord_8269204, baseEnd_8269204] using wordTrace_append hprefix tailTrace_8269204
  have hstable : (prefixWord ++ tailWord_8269204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269204).length < 2 ^ (prefixWord ++ tailWord_8269204).sum := by decide
  have hdescent : baseEnd_8269204 < baseStart_8269204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269274 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_8269274 : Nat := 118140960795 + 8269274 * 2 ^ 59
def prefixEnd_8269274 : Nat := 4983230072969 + 3 ^ 40 * 8269274 * 2
def baseEnd_8269274 : Nat := 4246112225727584661145307

theorem tailTrace_8269274 : CollatzResearch.WordTrace tailWord_8269274 prefixEnd_8269274 4246112225727584661145307 := by
  unfold tailWord_8269274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75401300160960013101747719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201070133762560034937993917 75401300160960013101747719)
  ·
    refine ⟨113101950241440019652621579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75401300160960013101747719 113101950241440019652621579)
    ·
      refine ⟨169652925362160029478932369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113101950241440019652621579 169652925362160029478932369)
      ·
        refine ⟨127239694021620022109199277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169652925362160029478932369 127239694021620022109199277)
        ·
          refine ⟨47714885258107508290949729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127239694021620022109199277 47714885258107508290949729)
          ·
            refine ⟨35786163943580631218212297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47714885258107508290949729 35786163943580631218212297)
            ·
              refine ⟨26839622957685473413659223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35786163943580631218212297 26839622957685473413659223)
              ·
                refine ⟨40259434436528210120488835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26839622957685473413659223 40259434436528210120488835)
                ·
                  refine ⟨60389151654792315180733253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40259434436528210120488835 60389151654792315180733253)
                  ·
                    refine ⟨11322965935273559096387485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60389151654792315180733253 11322965935273559096387485)
                    ·
                      refine ⟨4246112225727584661145307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11322965935273559096387485 4246112225727584661145307)
                      ·
                        rfl

theorem cell23_8269274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_8269274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269274 prefixEnd_8269274 := by exact prefixLift 8269274
  have htrace : WordTrace (prefixWord ++ tailWord_8269274) baseStart_8269274 baseEnd_8269274 := by
    simpa [prefixWord, tailWord_8269274, baseEnd_8269274] using wordTrace_append hprefix tailTrace_8269274
  have hstable : (prefixWord ++ tailWord_8269274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269274).length < 2 ^ (prefixWord ++ tailWord_8269274).sum := by decide
  have hdescent : baseEnd_8269274 < baseStart_8269274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269294 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_8269294 : Nat := 118140960795 + 8269294 * 2 ^ 59
def prefixEnd_8269294 : Nat := 4983230072969 + 3 ^ 40 * 8269294 * 2
def baseEnd_8269294 : Nat := 471791388371186064766135

theorem tailTrace_8269294 : CollatzResearch.WordTrace tailWord_8269294 prefixEnd_8269294 471791388371186064766135 := by
  unfold tailWord_8269294
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700741262970949477839867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201070620069178397215145957 37700741262970949477839867)
  ·
    refine ⟨56551111894456424216759801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37700741262970949477839867 56551111894456424216759801)
    ·
      refine ⟨42413333920842318162569851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56551111894456424216759801 42413333920842318162569851)
      ·
        refine ⟨63620000881263477243854777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42413333920842318162569851 63620000881263477243854777)
        ·
          refine ⟨47715000660947607932891083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63620000881263477243854777 47715000660947607932891083)
          ·
            refine ⟨71572500991421411899336625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47715000660947607932891083 71572500991421411899336625)
            ·
              refine ⟨53679375743566058924502469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71572500991421411899336625 53679375743566058924502469)
              ·
                refine ⟨10064882951918636048344213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53679375743566058924502469 10064882951918636048344213)
                ·
                  refine ⟨471791388371186064766135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10064882951918636048344213 471791388371186064766135)
                  ·
                    rfl

theorem cell23_8269294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_8269294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269294 prefixEnd_8269294 := by exact prefixLift 8269294
  have htrace : WordTrace (prefixWord ++ tailWord_8269294) baseStart_8269294 baseEnd_8269294 := by
    simpa [prefixWord, tailWord_8269294, baseEnd_8269294] using wordTrace_append hprefix tailTrace_8269294
  have hstable : (prefixWord ++ tailWord_8269294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269294).length < 2 ^ (prefixWord ++ tailWord_8269294).sum := by decide
  have hdescent : baseEnd_8269294 < baseStart_8269294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269298 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_8269298 : Nat := 118140960795 + 8269298 * 2 ^ 59
def prefixEnd_8269298 : Nat := 4983230072969 + 3 ^ 40 * 8269298 * 2
def baseEnd_8269298 : Nat := 1415374849754430855748399

theorem tailTrace_8269298 : CollatzResearch.WordTrace tailWord_8269298 prefixEnd_8269298 1415374849754430855748399 := by
  unfold tailWord_8269298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75401518998938276126466137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201070717330502069670576365 75401518998938276126466137)
  ·
    refine ⟨56551139249203707094849603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75401518998938276126466137 56551139249203707094849603)
    ·
      refine ⟨84826708873805560642274405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56551139249203707094849603 84826708873805560642274405)
      ·
        refine ⟨15905007913838542620426451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84826708873805560642274405 15905007913838542620426451)
        ·
          refine ⟨23857511870757813930639677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15905007913838542620426451 23857511870757813930639677)
          ·
            refine ⟨8946566951534180223989879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23857511870757813930639677 8946566951534180223989879)
            ·
              refine ⟨13419850427301270335984819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946566951534180223989879 13419850427301270335984819)
              ·
                refine ⟨20129775640951905503977229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419850427301270335984819 20129775640951905503977229)
                ·
                  refine ⟨7548665865356964563991461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20129775640951905503977229 7548665865356964563991461)
                  ·
                    refine ⟨1415374849754430855748399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548665865356964563991461 1415374849754430855748399)
                    ·
                      rfl

theorem cell23_8269298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_8269298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269298 prefixEnd_8269298 := by exact prefixLift 8269298
  have htrace : WordTrace (prefixWord ++ tailWord_8269298) baseStart_8269298 baseEnd_8269298 := by
    simpa [prefixWord, tailWord_8269298, baseEnd_8269298] using wordTrace_append hprefix tailTrace_8269298
  have hstable : (prefixWord ++ tailWord_8269298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269298).length < 2 ^ (prefixWord ++ tailWord_8269298).sum := by decide
  have hdescent : baseEnd_8269298 < baseStart_8269298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269307 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 5, 5]
def baseStart_8269307 : Nat := 118140960795 + 8269307 * 2 ^ 59
def prefixEnd_8269307 : Nat := 4983230072969 + 3 ^ 40 * 8269307 * 2
def baseEnd_8269307 : Nat := 1415376390196394344010885

theorem tailTrace_8269307 : CollatzResearch.WordTrace tailWord_8269307 prefixEnd_8269307 1415376390196394344010885 := by
  unfold tailWord_8269307
  simp only [CollatzResearch.WordTrace]
  refine ⟨301606404252720499042942175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201070936168480332695294783 301606404252720499042942175)
  ·
    refine ⟨452409606379080748564413263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301606404252720499042942175 452409606379080748564413263)
    ·
      refine ⟨678614409568621122846619895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452409606379080748564413263 678614409568621122846619895)
      ·
        refine ⟨1017921614352931684269929843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678614409568621122846619895 1017921614352931684269929843)
        ·
          refine ⟨1526882421529397526404894765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017921614352931684269929843 1526882421529397526404894765)
          ·
            refine ⟨572580908073524072401835537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526882421529397526404894765 572580908073524072401835537)
            ·
              refine ⟨429435681055143054301376653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572580908073524072401835537 429435681055143054301376653)
              ·
                refine ⟨161038380395678645363016245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429435681055143054301376653 161038380395678645363016245)
                ·
                  refine ⟨15097348162094873002782773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161038380395678645363016245 15097348162094873002782773)
                  ·
                    refine ⟨1415376390196394344010885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15097348162094873002782773 1415376390196394344010885)
                    ·
                      rfl

theorem cell23_8269307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 5].length) (baseStart_8269307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269307 prefixEnd_8269307 := by exact prefixLift 8269307
  have htrace : WordTrace (prefixWord ++ tailWord_8269307) baseStart_8269307 baseEnd_8269307 := by
    simpa [prefixWord, tailWord_8269307, baseEnd_8269307] using wordTrace_append hprefix tailTrace_8269307
  have hstable : (prefixWord ++ tailWord_8269307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269307).length < 2 ^ (prefixWord ++ tailWord_8269307).sum := by decide
  have hdescent : baseEnd_8269307 < baseStart_8269307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269331 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 2, 3, 2]
def baseStart_8269331 : Nat := 118140960795 + 8269331 * 2 ^ 59
def prefixEnd_8269331 : Nat := 4983230072969 + 3 ^ 40 * 8269331 * 2
def baseEnd_8269331 : Nat := 4246141494124890938132545

theorem tailTrace_8269331 : CollatzResearch.WordTrace tailWord_8269331 prefixEnd_8269331 4246141494124890938132545 := by
  unfold tailWord_8269331
  simp only [CollatzResearch.WordTrace]
  refine ⟨301607279604633551141815847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201071519736422367427877231 301607279604633551141815847)
  ·
    refine ⟨452410919406950326712723771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301607279604633551141815847 452410919406950326712723771)
    ·
      refine ⟨678616379110425490069085657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452410919406950326712723771 678616379110425490069085657)
      ·
        refine ⟨508962284332819117551814243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678616379110425490069085657 508962284332819117551814243)
        ·
          refine ⟨763443426499228676327721365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508962284332819117551814243 763443426499228676327721365)
          ·
            refine ⟨35786410617151344202861939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 763443426499228676327721365 35786410617151344202861939)
            ·
              refine ⟨53679615925727016304292909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35786410617151344202861939 53679615925727016304292909)
              ·
                refine ⟨20129855972147631114109841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53679615925727016304292909 20129855972147631114109841)
                ·
                  refine ⟨15097391979110723335582381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20129855972147631114109841 15097391979110723335582381)
                  ·
                    refine ⟨5661521992166521250843393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15097391979110723335582381 5661521992166521250843393)
                    ·
                      refine ⟨4246141494124890938132545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661521992166521250843393 4246141494124890938132545)
                      ·
                        rfl

theorem cell23_8269331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3, 2].length) (baseStart_8269331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269331 prefixEnd_8269331 := by exact prefixLift 8269331
  have htrace : WordTrace (prefixWord ++ tailWord_8269331) baseStart_8269331 baseEnd_8269331 := by
    simpa [prefixWord, tailWord_8269331, baseEnd_8269331] using wordTrace_append hprefix tailTrace_8269331
  have hstable : (prefixWord ++ tailWord_8269331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269331).length < 2 ^ (prefixWord ++ tailWord_8269331).sum := by decide
  have hdescent : baseEnd_8269331 < baseStart_8269331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_8269338 : Nat := 118140960795 + 8269338 * 2 ^ 59
def prefixEnd_8269338 : Nat := 4983230072969 + 3 ^ 40 * 8269338 * 2
def baseEnd_8269338 : Nat := 4246145088489472410745013

theorem tailTrace_8269338 : CollatzResearch.WordTrace tailWord_8269338 prefixEnd_8269338 4246145088489472410745013 := by
  unfold tailWord_8269338
  simp only [CollatzResearch.WordTrace]
  refine ⟨75401883728902047834330167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201071689943738794224880445 75401883728902047834330167)
  ·
    refine ⟨113102825593353071751495251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75401883728902047834330167 113102825593353071751495251)
    ·
      refine ⟨169654238390029607627242877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113102825593353071751495251 169654238390029607627242877)
      ·
        refine ⟨63620339396261102860216079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169654238390029607627242877 63620339396261102860216079)
        ·
          refine ⟨95430509094391654290324119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63620339396261102860216079 95430509094391654290324119)
          ·
            refine ⟨143145763641587481435486179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95430509094391654290324119 143145763641587481435486179)
            ·
              refine ⟨214718645462381222153229269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143145763641587481435486179 214718645462381222153229269)
              ·
                refine ⟨5032468253024559894216311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214718645462381222153229269 5032468253024559894216311)
                ·
                  refine ⟨7548702379536839841324467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032468253024559894216311 7548702379536839841324467)
                  ·
                    refine ⟨11323053569305259761986701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7548702379536839841324467 11323053569305259761986701)
                    ·
                      refine ⟨4246145088489472410745013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323053569305259761986701 4246145088489472410745013)
                      ·
                        rfl

theorem cell23_8269338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_8269338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269338 prefixEnd_8269338 := by exact prefixLift 8269338
  have htrace : WordTrace (prefixWord ++ tailWord_8269338) baseStart_8269338 baseEnd_8269338 := by
    simpa [prefixWord, tailWord_8269338, baseEnd_8269338] using wordTrace_append hprefix tailTrace_8269338
  have hstable : (prefixWord ++ tailWord_8269338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269338).length < 2 ^ (prefixWord ++ tailWord_8269338).sum := by decide
  have hdescent : baseEnd_8269338 < baseStart_8269338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269354 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_8269354 : Nat := 118140960795 + 8269354 * 2 ^ 59
def prefixEnd_8269354 : Nat := 4983230072969 + 3 ^ 40 * 8269354 * 2
def baseEnd_8269354 : Nat := 1415384434726648116048313

theorem tailTrace_8269354 : CollatzResearch.WordTrace tailWord_8269354 prefixEnd_8269354 1415384434726648116048313 := by
  unfold tailWord_8269354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75402029620887556517475779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201072078989033484046602077 75402029620887556517475779)
  ·
    refine ⟨113103044431331334776213669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75402029620887556517475779 113103044431331334776213669)
    ·
      refine ⟨21206820830874625270540063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113103044431331334776213669 21206820830874625270540063)
      ·
        refine ⟨31810231246311937905810095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206820830874625270540063 31810231246311937905810095)
        ·
          refine ⟨47715346869467906858715143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31810231246311937905810095 47715346869467906858715143)
          ·
            refine ⟨71573020304201860288072715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47715346869467906858715143 71573020304201860288072715)
            ·
              refine ⟨107359530456302790432109073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71573020304201860288072715 107359530456302790432109073)
              ·
                refine ⟨80519647842227092824081805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107359530456302790432109073 80519647842227092824081805)
                ·
                  refine ⟨30194867940835159809030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80519647842227092824081805 30194867940835159809030677)
                  ·
                    refine ⟨1415384434726648116048313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30194867940835159809030677 1415384434726648116048313)
                    ·
                      rfl

theorem cell23_8269354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_8269354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269354 prefixEnd_8269354 := by exact prefixLift 8269354
  have htrace : WordTrace (prefixWord ++ tailWord_8269354) baseStart_8269354 baseEnd_8269354 := by
    simpa [prefixWord, tailWord_8269354, baseEnd_8269354] using wordTrace_append hprefix tailTrace_8269354
  have hstable : (prefixWord ++ tailWord_8269354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269354).length < 2 ^ (prefixWord ++ tailWord_8269354).sum := by decide
  have hdescent : baseEnd_8269354 < baseStart_8269354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269381 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_8269381 : Nat := 118140960795 + 8269381 * 2 ^ 59
def prefixEnd_8269381 : Nat := 4983230072969 + 3 ^ 40 * 8269381 * 2
def baseEnd_8269381 : Nat := 4246167168157615742507315

theorem tailTrace_8269381 : CollatzResearch.WordTrace tailWord_8269381 prefixEnd_8269381 4246167168157615742507315 := by
  unfold tailWord_8269381
  simp only [CollatzResearch.WordTrace]
  refine ⟨301609103254452409681135997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201072735502968273120757331 301609103254452409681135997)
  ·
    refine ⟨113103413720419653630425999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301609103254452409681135997 113103413720419653630425999)
    ·
      refine ⟨169655120580629480445638999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113103413720419653630425999 169655120580629480445638999)
      ·
        refine ⟨254482680870944220668458499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169655120580629480445638999 254482680870944220668458499)
        ·
          refine ⟨381724021306416331002687749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254482680870944220668458499 381724021306416331002687749)
          ·
            refine ⟨71573253994953062063003953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381724021306416331002687749 71573253994953062063003953)
            ·
              refine ⟨53679940496214796547252965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71573253994953062063003953 53679940496214796547252965)
              ·
                refine ⟨10064988843040274352609931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53679940496214796547252965 10064988843040274352609931)
                ·
                  refine ⟨15097483264560411528914897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10064988843040274352609931 15097483264560411528914897)
                  ·
                    refine ⟨11323112448420308646686173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15097483264560411528914897 11323112448420308646686173)
                    ·
                      refine ⟨4246167168157615742507315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323112448420308646686173 4246167168157615742507315)
                      ·
                        rfl

theorem cell23_8269381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_8269381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269381 prefixEnd_8269381 := by exact prefixLift 8269381
  have htrace : WordTrace (prefixWord ++ tailWord_8269381) baseStart_8269381 baseEnd_8269381 := by
    simpa [prefixWord, tailWord_8269381, baseEnd_8269381] using wordTrace_append hprefix tailTrace_8269381
  have hstable : (prefixWord ++ tailWord_8269381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269381).length < 2 ^ (prefixWord ++ tailWord_8269381).sum := by decide
  have hdescent : baseEnd_8269381 < baseStart_8269381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269405 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_8269405 : Nat := 118140960795 + 8269405 * 2 ^ 59
def prefixEnd_8269405 : Nat := 4983230072969 + 3 ^ 40 * 8269405 * 2
def baseEnd_8269405 : Nat := 1415393163897774549535735

theorem tailTrace_8269405 : CollatzResearch.WordTrace tailWord_8269405 prefixEnd_8269405 1415393163897774549535735 := by
  unfold tailWord_8269405
  simp only [CollatzResearch.WordTrace]
  refine ⟨301609978606365461780009669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201073319070910307853339779 301609978606365461780009669)
  ·
    refine ⟨56551870988693524083751813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301609978606365461780009669 56551870988693524083751813)
    ·
      refine ⟨10603475810380035765703465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56551870988693524083751813 10603475810380035765703465)
      ·
        refine ⟨7952606857785026824277599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10603475810380035765703465 7952606857785026824277599)
        ·
          refine ⟨11928910286677540236416399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952606857785026824277599 11928910286677540236416399)
          ·
            refine ⟨17893365430016310354624599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11928910286677540236416399 17893365430016310354624599)
            ·
              refine ⟨26840048145024465531936899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17893365430016310354624599 26840048145024465531936899)
              ·
                refine ⟨40260072217536698297905349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26840048145024465531936899 40260072217536698297905349)
                ·
                  refine ⟨7548763540788130930857253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40260072217536698297905349 7548763540788130930857253)
                  ·
                    refine ⟨1415393163897774549535735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548763540788130930857253 1415393163897774549535735)
                    ·
                      rfl

theorem cell23_8269405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_8269405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269405 prefixEnd_8269405 := by exact prefixLift 8269405
  have htrace : WordTrace (prefixWord ++ tailWord_8269405) baseStart_8269405 baseEnd_8269405 := by
    simpa [prefixWord, tailWord_8269405, baseEnd_8269405] using wordTrace_append hprefix tailTrace_8269405
  have hstable : (prefixWord ++ tailWord_8269405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269405).length < 2 ^ (prefixWord ++ tailWord_8269405).sum := by decide
  have hdescent : baseEnd_8269405 < baseStart_8269405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269451 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 4, 2]
def baseStart_8269451 : Nat := 118140960795 + 8269451 * 2 ^ 59
def prefixEnd_8269451 : Nat := 4983230072969 + 3 ^ 40 * 8269451 * 2
def baseEnd_8269451 : Nat := 4246203111803430468631993

theorem tailTrace_8269451 : CollatzResearch.WordTrace tailWord_8269451 prefixEnd_8269451 4246203111803430468631993 := by
  unfold tailWord_8269451
  simp only [CollatzResearch.WordTrace]
  refine ⟨301611656364198811636184207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201074437576132541090789471 301611656364198811636184207)
  ·
    refine ⟨452417484546298217454276311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301611656364198811636184207 452417484546298217454276311)
    ·
      refine ⟨678626226819447326181414467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452417484546298217454276311 678626226819447326181414467)
      ·
        refine ⟨1017939340229170989272121701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678626226819447326181414467 1017939340229170989272121701)
        ·
          refine ⟨190863626292969560488522819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1017939340229170989272121701 190863626292969560488522819)
          ·
            refine ⟨286295439439454340732784229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190863626292969560488522819 286295439439454340732784229)
            ·
              refine ⟨53680394894897688887397043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286295439439454340732784229 53680394894897688887397043)
              ·
                refine ⟨80520592342346533331095565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53680394894897688887397043 80520592342346533331095565)
                ·
                  refine ⟨30195222128379949999160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80520592342346533331095565 30195222128379949999160837)
                  ·
                    refine ⟨5661604149071240624842657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30195222128379949999160837 5661604149071240624842657)
                    ·
                      refine ⟨4246203111803430468631993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661604149071240624842657 4246203111803430468631993)
                      ·
                        rfl

theorem cell23_8269451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4, 2].length) (baseStart_8269451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269451 prefixEnd_8269451 := by exact prefixLift 8269451
  have htrace : WordTrace (prefixWord ++ tailWord_8269451) baseStart_8269451 baseEnd_8269451 := by
    simpa [prefixWord, tailWord_8269451, baseEnd_8269451] using wordTrace_append hprefix tailTrace_8269451
  have hstable : (prefixWord ++ tailWord_8269451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269451).length < 2 ^ (prefixWord ++ tailWord_8269451).sum := by decide
  have hdescent : baseEnd_8269451 < baseStart_8269451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269508 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 5]
def baseStart_8269508 : Nat := 118140960795 + 8269508 * 2 ^ 59
def prefixEnd_8269508 : Nat := 4983230072969 + 3 ^ 40 * 8269508 * 2
def baseEnd_8269508 : Nat := 471803597800081860624359

theorem tailTrace_8269508 : CollatzResearch.WordTrace tailWord_8269508 prefixEnd_8269508 471803597800081860624359 := by
  unfold tailWord_8269508
  simp only [CollatzResearch.WordTrace]
  refine ⟨150806867662496155185504589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201075823549994873580672785 150806867662496155185504589)
  ·
    refine ⟨56552575373436058194564221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150806867662496155185504589 56552575373436058194564221)
    ·
      refine ⟨21207215765038521822961583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56552575373436058194564221 21207215765038521822961583)
      ·
        refine ⟨31810823647557782734442375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207215765038521822961583 31810823647557782734442375)
        ·
          refine ⟨47716235471336674101663563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31810823647557782734442375 47716235471336674101663563)
          ·
            refine ⟨71574353207005011152495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47716235471336674101663563 71574353207005011152495345)
            ·
              refine ⟨53680764905253758364371509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71574353207005011152495345 53680764905253758364371509)
              ·
                refine ⟨5032571709867539846659829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53680764905253758364371509 5032571709867539846659829)
                ·
                  refine ⟨471803597800081860624359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032571709867539846659829 471803597800081860624359)
                  ·
                    rfl

theorem cell23_8269508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_8269508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269508 prefixEnd_8269508 := by exact prefixLift 8269508
  have htrace : WordTrace (prefixWord ++ tailWord_8269508) baseStart_8269508 baseEnd_8269508 := by
    simpa [prefixWord, tailWord_8269508, baseEnd_8269508] using wordTrace_append hprefix tailTrace_8269508
  have hstable : (prefixWord ++ tailWord_8269508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269508).length < 2 ^ (prefixWord ++ tailWord_8269508).sum := by decide
  have hdescent : baseEnd_8269508 < baseStart_8269508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269521 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_8269521 : Nat := 118140960795 + 8269521 * 2 ^ 59
def prefixEnd_8269521 : Nat := 4983230072969 + 3 ^ 40 * 8269521 * 2
def baseEnd_8269521 : Nat := 1415413018483081731585557

theorem tailTrace_8269521 : CollatzResearch.WordTrace tailWord_8269521 prefixEnd_8269521 1415413018483081731585557 := by
  unfold tailWord_8269521
  simp only [CollatzResearch.WordTrace]
  refine ⟨301614209473945213591232417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201076139649296809060821611 301614209473945213591232417)
  ·
    refine ⟨226210657105458910193424313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301614209473945213591232417 226210657105458910193424313)
    ·
      refine ⟨169657992829094182645068235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226210657105458910193424313 169657992829094182645068235)
      ·
        refine ⟨254486989243641273967602353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169657992829094182645068235 254486989243641273967602353)
        ·
          refine ⟨190865241932730955475701765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254486989243641273967602353 190865241932730955475701765)
          ·
            refine ⟨35787232862387054151694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190865241932730955475701765 35787232862387054151694081)
            ·
              refine ⟨26840424646790290613770561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35787232862387054151694081 26840424646790290613770561)
              ·
                refine ⟨20130318485092717960327921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26840424646790290613770561 20130318485092717960327921)
                ·
                  refine ⟨15097738863819538470245941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20130318485092717960327921 15097738863819538470245941)
                  ·
                    refine ⟨1415413018483081731585557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15097738863819538470245941 1415413018483081731585557)
                    ·
                      rfl

theorem cell23_8269521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_8269521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269521 prefixEnd_8269521 := by exact prefixLift 8269521
  have htrace : WordTrace (prefixWord ++ tailWord_8269521) baseStart_8269521 baseEnd_8269521 := by
    simpa [prefixWord, tailWord_8269521, baseEnd_8269521] using wordTrace_append hprefix tailTrace_8269521
  have hstable : (prefixWord ++ tailWord_8269521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269521).length < 2 ^ (prefixWord ++ tailWord_8269521).sum := by decide
  have hdescent : baseEnd_8269521 < baseStart_8269521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269541 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_8269541 : Nat := 118140960795 + 8269541 * 2 ^ 59
def prefixEnd_8269541 : Nat := 4983230072969 + 3 ^ 40 * 8269541 * 2
def baseEnd_8269541 : Nat := 4246249325062335116506579

theorem tailTrace_8269541 : CollatzResearch.WordTrace tailWord_8269541 prefixEnd_8269541 4246249325062335116506579 := by
  unfold tailWord_8269541
  simp only [CollatzResearch.WordTrace]
  refine ⟨301614938933872757006960477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201076625955915171337973651 301614938933872757006960477)
  ·
    refine ⟨113105602100202283877610179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301614938933872757006960477 113105602100202283877610179)
    ·
      refine ⟨169658403150303425816415269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113105602100202283877610179 169658403150303425816415269)
      ·
        refine ⟨31810950590681892340577863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169658403150303425816415269 31810950590681892340577863)
        ·
          refine ⟨47716425886022838510866795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31810950590681892340577863 47716425886022838510866795)
          ·
            refine ⟨71574638829034257766300193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47716425886022838510866795 71574638829034257766300193)
            ·
              refine ⟨53680979121775693324725145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71574638829034257766300193 53680979121775693324725145)
              ·
                refine ⟨40260734341331769993543859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53680979121775693324725145 40260734341331769993543859)
                ·
                  refine ⟨60391101511997654990315789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40260734341331769993543859 60391101511997654990315789)
                  ·
                    refine ⟨22646663066999120621368421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60391101511997654990315789 22646663066999120621368421)
                    ·
                      refine ⟨4246249325062335116506579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22646663066999120621368421 4246249325062335116506579)
                      ·
                        rfl

theorem cell23_8269541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_8269541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269541 prefixEnd_8269541 := by exact prefixLift 8269541
  have htrace : WordTrace (prefixWord ++ tailWord_8269541) baseStart_8269541 baseEnd_8269541 := by
    simpa [prefixWord, tailWord_8269541, baseEnd_8269541] using wordTrace_append hprefix tailTrace_8269541
  have hstable : (prefixWord ++ tailWord_8269541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269541).length < 2 ^ (prefixWord ++ tailWord_8269541).sum := by decide
  have hdescent : baseEnd_8269541 < baseStart_8269541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269558 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_8269558 : Nat := 118140960795 + 8269558 * 2 ^ 59
def prefixEnd_8269558 : Nat := 4983230072969 + 3 ^ 40 * 8269558 * 2
def baseEnd_8269558 : Nat := 4246258054233461549994001

theorem tailTrace_8269558 : CollatzResearch.WordTrace tailWord_8269558 prefixEnd_8269558 4246258054233461549994001 := by
  unfold tailWord_8269558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850972435925698056895583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201077039316540779273552885 18850972435925698056895583)
  ·
    refine ⟨28276458653888547085343375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18850972435925698056895583 28276458653888547085343375)
    ·
      refine ⟨42414687980832820628015063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28276458653888547085343375 42414687980832820628015063)
      ·
        refine ⟨63622031971249230942022595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42414687980832820628015063 63622031971249230942022595)
        ·
          refine ⟨95433047956873846413033893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63622031971249230942022595 95433047956873846413033893)
          ·
            refine ⟨17893696491913846202443855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95433047956873846413033893 17893696491913846202443855)
            ·
              refine ⟨26840544737870769303665783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17893696491913846202443855 26840544737870769303665783)
              ·
                refine ⟨40260817106806153955498675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26840544737870769303665783 40260817106806153955498675)
                ·
                  refine ⟨60391225660209230933248013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40260817106806153955498675 60391225660209230933248013)
                  ·
                    refine ⟨22646709622578461599968005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60391225660209230933248013 22646709622578461599968005)
                    ·
                      refine ⟨4246258054233461549994001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22646709622578461599968005 4246258054233461549994001)
                      ·
                        rfl

theorem cell23_8269558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_8269558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269558 prefixEnd_8269558 := by exact prefixLift 8269558
  have htrace : WordTrace (prefixWord ++ tailWord_8269558) baseStart_8269558 baseEnd_8269558 := by
    simpa [prefixWord, tailWord_8269558, baseEnd_8269558] using wordTrace_append hprefix tailTrace_8269558
  have hstable : (prefixWord ++ tailWord_8269558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269558).length < 2 ^ (prefixWord ++ tailWord_8269558).sum := by decide
  have hdescent : baseEnd_8269558 < baseStart_8269558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269619 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 1, 4]
def baseStart_8269619 : Nat := 118140960795 + 8269619 * 2 ^ 59
def prefixEnd_8269619 : Nat := 4983230072969 + 3 ^ 40 * 8269619 * 2
def baseEnd_8269619 : Nat := 1415429792184461937110407

theorem tailTrace_8269619 : CollatzResearch.WordTrace tailWord_8269619 prefixEnd_8269619 1415429792184461937110407 := by
  unfold tailWord_8269619
  simp only [CollatzResearch.WordTrace]
  refine ⟨301617783827590176328299911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201078522551726784218866607 301617783827590176328299911)
  ·
    refine ⟨452426675741385264492449867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301617783827590176328299911 452426675741385264492449867)
    ·
      refine ⟨678640013612077896738674801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452426675741385264492449867 678640013612077896738674801)
      ·
        refine ⟨508980010209058422554006101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678640013612077896738674801 508980010209058422554006101)
        ·
          refine ⟨5964609494637403389304759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 508980010209058422554006101 5964609494637403389304759)
          ·
            refine ⟨8946914241956105083957139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964609494637403389304759 8946914241956105083957139)
            ·
              refine ⟨13420371362934157625935709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946914241956105083957139 13420371362934157625935709)
              ·
                refine ⟨5032639261100309109725891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13420371362934157625935709 5032639261100309109725891)
                ·
                  refine ⟨7548958891650463664588837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032639261100309109725891 7548958891650463664588837)
                  ·
                    refine ⟨1415429792184461937110407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548958891650463664588837 1415429792184461937110407)
                    ·
                      rfl

theorem cell23_8269619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 4].length) (baseStart_8269619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269619 prefixEnd_8269619 := by exact prefixLift 8269619
  have htrace : WordTrace (prefixWord ++ tailWord_8269619) baseStart_8269619 baseEnd_8269619 := by
    simpa [prefixWord, tailWord_8269619, baseEnd_8269619] using wordTrace_append hprefix tailTrace_8269619
  have hstable : (prefixWord ++ tailWord_8269619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269619).length < 2 ^ (prefixWord ++ tailWord_8269619).sum := by decide
  have hdescent : baseEnd_8269619 < baseStart_8269619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269628 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_8269628 : Nat := 118140960795 + 8269628 * 2 ^ 59
def prefixEnd_8269628 : Nat := 4983230072969 + 3 ^ 40 * 8269628 * 2
def baseEnd_8269628 : Nat := 1415431332626425425372893

theorem tailTrace_8269628 : CollatzResearch.WordTrace tailWord_8269628 prefixEnd_8269628 1415431332626425425372893 := by
  unfold tailWord_8269628
  simp only [CollatzResearch.WordTrace]
  refine ⟨150809056042278785432688769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201078741389705047243585025 150809056042278785432688769)
  ·
    refine ⟨113106792031709089074516577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150809056042278785432688769 113106792031709089074516577)
    ·
      refine ⟨84830094023781816805887433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113106792031709089074516577 84830094023781816805887433)
      ·
        refine ⟨63622570517836362604415575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84830094023781816805887433 63622570517836362604415575)
        ·
          refine ⟨95433855776754543906623363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63622570517836362604415575 95433855776754543906623363)
          ·
            refine ⟨143150783665131815859935045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95433855776754543906623363 143150783665131815859935045)
            ·
              refine ⟨26840771937212215473737821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143150783665131815859935045 26840771937212215473737821)
              ·
                refine ⟨10065289476454580802651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26840771937212215473737821 10065289476454580802651683)
                ·
                  refine ⟨15097934214681871203977525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10065289476454580802651683 15097934214681871203977525)
                  ·
                    refine ⟨1415431332626425425372893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15097934214681871203977525 1415431332626425425372893)
                    ·
                      rfl

theorem cell23_8269628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_8269628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269628 prefixEnd_8269628 := by exact prefixLift 8269628
  have htrace : WordTrace (prefixWord ++ tailWord_8269628) baseStart_8269628 baseEnd_8269628 := by
    simpa [prefixWord, tailWord_8269628, baseEnd_8269628] using wordTrace_append hprefix tailTrace_8269628
  have hstable : (prefixWord ++ tailWord_8269628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269628).length < 2 ^ (prefixWord ++ tailWord_8269628).sum := by decide
  have hdescent : baseEnd_8269628 < baseStart_8269628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269635 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 2, 3, 2]
def baseStart_8269635 : Nat := 118140960795 + 8269635 * 2 ^ 59
def prefixEnd_8269635 : Nat := 4983230072969 + 3 ^ 40 * 8269635 * 2
def baseEnd_8269635 : Nat := 4246297592243857748731147

theorem tailTrace_8269635 : CollatzResearch.WordTrace tailWord_8269635 prefixEnd_8269635 4246297592243857748731147 := by
  unfold tailWord_8269635
  simp only [CollatzResearch.WordTrace]
  refine ⟨301618367395532211060882359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201078911597021474040588239 301618367395532211060882359)
  ·
    refine ⟨452427551093298316591323539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301618367395532211060882359 452427551093298316591323539)
    ·
      refine ⟨678641326639947474886985309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452427551093298316591323539 678641326639947474886985309)
      ·
        refine ⟨254490497489980303082619491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678641326639947474886985309 254490497489980303082619491)
        ·
          refine ⟨381735746234970454623929237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254490497489980303082619491 381735746234970454623929237)
          ·
            refine ⟨17893863104764240060496683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381735746234970454623929237 17893863104764240060496683)
            ·
              refine ⟨26840794657146360090745025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17893863104764240060496683 26840794657146360090745025)
              ·
                refine ⟨20130595992859770068058769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26840794657146360090745025 20130595992859770068058769)
                ·
                  refine ⟨15097946994644827551044077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20130595992859770068058769 15097946994644827551044077)
                  ·
                    refine ⟨5661730122991810331641529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15097946994644827551044077 5661730122991810331641529)
                    ·
                      refine ⟨4246297592243857748731147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661730122991810331641529 4246297592243857748731147)
                      ·
                        rfl

theorem cell23_8269635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_8269635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269635 prefixEnd_8269635 := by exact prefixLift 8269635
  have htrace : WordTrace (prefixWord ++ tailWord_8269635) baseStart_8269635 baseEnd_8269635 := by
    simpa [prefixWord, tailWord_8269635, baseEnd_8269635] using wordTrace_append hprefix tailTrace_8269635
  have hstable : (prefixWord ++ tailWord_8269635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269635).length < 2 ^ (prefixWord ++ tailWord_8269635).sum := by decide
  have hdescent : baseEnd_8269635 < baseStart_8269635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269651 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3]
def baseStart_8269651 : Nat := 118140960795 + 8269651 * 2 ^ 59
def prefixEnd_8269651 : Nat := 4983230072969 + 3 ^ 40 * 8269651 * 2
def baseEnd_8269651 : Nat := 4246305807934329686131073

theorem tailTrace_8269651 : CollatzResearch.WordTrace tailWord_8269651 prefixEnd_8269651 4246305807934329686131073 := by
  unfold tailWord_8269651
  simp only [CollatzResearch.WordTrace]
  refine ⟨301618950963474245793464807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201079300642316163862309871 301618950963474245793464807)
  ·
    refine ⟨452428426445211368690197211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301618950963474245793464807 452428426445211368690197211)
    ·
      refine ⟨678642639667817053035295817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452428426445211368690197211 678642639667817053035295817)
      ·
        refine ⟨508981979750862789776471863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678642639667817053035295817 508981979750862789776471863)
        ·
          refine ⟨763472969626294184664707795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508981979750862789776471863 763472969626294184664707795)
          ·
            refine ⟨1145209454439441276997061693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763472969626294184664707795 1145209454439441276997061693)
            ·
              refine ⟨429453545414790478873898135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145209454439441276997061693 429453545414790478873898135)
              ·
                refine ⟨644180318122185718310847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429453545414790478873898135 644180318122185718310847203)
                ·
                  refine ⟨966270477183278577466270805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644180318122185718310847203 966270477183278577466270805)
                  ·
                    refine ⟨11323482154491545829682861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 966270477183278577466270805 11323482154491545829682861)
                    ·
                      refine ⟨4246305807934329686131073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323482154491545829682861 4246305807934329686131073)
                      ·
                        rfl

theorem cell23_8269651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_8269651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269651 prefixEnd_8269651 := by exact prefixLift 8269651
  have htrace : WordTrace (prefixWord ++ tailWord_8269651) baseStart_8269651 baseEnd_8269651 := by
    simpa [prefixWord, tailWord_8269651, baseEnd_8269651] using wordTrace_append hprefix tailTrace_8269651
  have hstable : (prefixWord ++ tailWord_8269651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269651).length < 2 ^ (prefixWord ++ tailWord_8269651).sum := by decide
  have hdescent : baseEnd_8269651 < baseStart_8269651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269665 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_8269665 : Nat := 118140960795 + 8269665 * 2 ^ 59
def prefixEnd_8269665 : Nat := 4983230072969 + 3 ^ 40 * 8269665 * 2
def baseEnd_8269665 : Nat := 4246312996663492631356009

theorem tailTrace_8269665 : CollatzResearch.WordTrace tailWord_8269665 prefixEnd_8269665 4246312996663492631356009 := by
  unfold tailWord_8269665
  simp only [CollatzResearch.WordTrace]
  refine ⟨301619461585423526184474449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201079641056949017456316299 301619461585423526184474449)
  ·
    refine ⟨226214596189067644638355837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301619461585423526184474449 226214596189067644638355837)
    ·
      refine ⟨84830473570900366739383439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226214596189067644638355837 84830473570900366739383439)
      ·
        refine ⟨127245710356350550109075159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84830473570900366739383439 127245710356350550109075159)
        ·
          refine ⟨190868565534525825163612739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127245710356350550109075159 190868565534525825163612739)
          ·
            refine ⟨286302848301788737745419109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190868565534525825163612739 286302848301788737745419109)
            ·
              refine ⟨53681784056585388327266083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286302848301788737745419109 53681784056585388327266083)
              ·
                refine ⟨80522676084878082490899125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53681784056585388327266083 80522676084878082490899125)
                ·
                  refine ⟨7549000882957320233521793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80522676084878082490899125 7549000882957320233521793)
                  ·
                    refine ⟨5661750662217990175141345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549000882957320233521793 5661750662217990175141345)
                    ·
                      refine ⟨4246312996663492631356009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661750662217990175141345 4246312996663492631356009)
                      ·
                        rfl

theorem cell23_8269665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_8269665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269665 prefixEnd_8269665 := by exact prefixLift 8269665
  have htrace : WordTrace (prefixWord ++ tailWord_8269665) baseStart_8269665 baseEnd_8269665 := by
    simpa [prefixWord, tailWord_8269665, baseEnd_8269665] using wordTrace_append hprefix tailTrace_8269665
  have hstable : (prefixWord ++ tailWord_8269665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269665).length < 2 ^ (prefixWord ++ tailWord_8269665).sum := by decide
  have hdescent : baseEnd_8269665 < baseStart_8269665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269671 : List Nat := [1, 1, 5, 1, 2, 1, 1, 11]
def baseStart_8269671 : Nat := 118140960795 + 8269671 * 2 ^ 59
def prefixEnd_8269671 : Nat := 4983230072969 + 3 ^ 40 * 8269671 * 2
def baseEnd_8269671 : Nat := 157270965835089615106703

theorem tailTrace_8269671 : CollatzResearch.WordTrace tailWord_8269671 prefixEnd_8269671 157270965835089615106703 := by
  unfold tailWord_8269671
  simp only [CollatzResearch.WordTrace]
  refine ⟨301619680423401789209192867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201079786948934526139461911 301619680423401789209192867)
  ·
    refine ⟨452429520635102683813789301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301619680423401789209192867 452429520635102683813789301)
    ·
      refine ⟨42415267559540876607542747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452429520635102683813789301 42415267559540876607542747)
      ·
        refine ⟨63622901339311314911314121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42415267559540876607542747 63622901339311314911314121)
        ·
          refine ⟨47717176004483486183485591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63622901339311314911314121 47717176004483486183485591)
          ·
            refine ⟨71575764006725229275228387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47717176004483486183485591 71575764006725229275228387)
            ·
              refine ⟨107363646010087843912842581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71575764006725229275228387 107363646010087843912842581)
              ·
                refine ⟨157270965835089615106703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107363646010087843912842581 157270965835089615106703)
                ·
                  rfl

theorem cell23_8269671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 11].length) (baseStart_8269671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269671 prefixEnd_8269671 := by exact prefixLift 8269671
  have htrace : WordTrace (prefixWord ++ tailWord_8269671) baseStart_8269671 baseEnd_8269671 := by
    simpa [prefixWord, tailWord_8269671, baseEnd_8269671] using wordTrace_append hprefix tailTrace_8269671
  have hstable : (prefixWord ++ tailWord_8269671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269671).length < 2 ^ (prefixWord ++ tailWord_8269671).sum := by decide
  have hdescent : baseEnd_8269671 < baseStart_8269671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269699 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 1, 2, 2]
def baseStart_8269699 : Nat := 118140960795 + 8269699 * 2 ^ 59
def prefixEnd_8269699 : Nat := 4983230072969 + 3 ^ 40 * 8269699 * 2
def baseEnd_8269699 : Nat := 4246330455005745498330853

theorem tailTrace_8269699 : CollatzResearch.WordTrace tailWord_8269699 prefixEnd_8269699 4246330455005745498330853 := by
  unfold tailWord_8269699
  simp only [CollatzResearch.WordTrace]
  refine ⟨301620701667300349991212151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201080467778200233327474767 301620701667300349991212151)
  ·
    refine ⟨452431052500950524986818227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301620701667300349991212151 452431052500950524986818227)
    ·
      refine ⟨678646578751425787480227341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452431052500950524986818227 678646578751425787480227341)
      ·
        refine ⟨254492467031784670305085253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678646578751425787480227341 254492467031784670305085253)
        ·
          refine ⟨47717337568459625682203485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254492467031784670305085253 47717337568459625682203485)
          ·
            refine ⟨17894001588172359630826307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47717337568459625682203485 17894001588172359630826307)
            ·
              refine ⟨26841002382258539446239461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17894001588172359630826307 26841002382258539446239461)
              ·
                refine ⟨5032687946673476146169899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26841002382258539446239461 5032687946673476146169899)
                ·
                  refine ⟨7549031920010214219254849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032687946673476146169899 7549031920010214219254849)
                  ·
                    refine ⟨5661773940007660664441137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549031920010214219254849 5661773940007660664441137)
                    ·
                      refine ⟨4246330455005745498330853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661773940007660664441137 4246330455005745498330853)
                      ·
                        rfl

theorem cell23_8269699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_8269699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269699 prefixEnd_8269699 := by exact prefixLift 8269699
  have htrace : WordTrace (prefixWord ++ tailWord_8269699) baseStart_8269699 baseEnd_8269699 := by
    simpa [prefixWord, tailWord_8269699, baseEnd_8269699] using wordTrace_append hprefix tailTrace_8269699
  have hstable : (prefixWord ++ tailWord_8269699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269699).length < 2 ^ (prefixWord ++ tailWord_8269699).sum := by decide
  have hdescent : baseEnd_8269699 < baseStart_8269699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269701 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_8269701 : Nat := 118140960795 + 8269701 * 2 ^ 59
def prefixEnd_8269701 : Nat := 4983230072969 + 3 ^ 40 * 8269701 * 2
def baseEnd_8269701 : Nat := 1415443827322351496835281

theorem tailTrace_8269701 : CollatzResearch.WordTrace tailWord_8269701 prefixEnd_8269701 1415443827322351496835281 := by
  unfold tailWord_8269701
  simp only [CollatzResearch.WordTrace]
  refine ⟨301620774613293104332784957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201080516408862069555189971 301620774613293104332784957)
  ·
    refine ⟨113107790479984914124794359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301620774613293104332784957 113107790479984914124794359)
    ·
      refine ⟨169661685719977371187191539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113107790479984914124794359 169661685719977371187191539)
      ·
        refine ⟨254492528579966056780787309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169661685719977371187191539 254492528579966056780787309)
        ·
          refine ⟨95434698217487271292795241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254492528579966056780787309 95434698217487271292795241)
          ·
            refine ⟨71576023663115453469596431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95434698217487271292795241 71576023663115453469596431)
            ·
              refine ⟨107364035494673180204394647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71576023663115453469596431 107364035494673180204394647)
              ·
                refine ⟨161046053242009770306591971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107364035494673180204394647 161046053242009770306591971)
                ·
                  refine ⟨241569079863014655459887957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161046053242009770306591971 241569079863014655459887957)
                  ·
                    refine ⟨1415443827322351496835281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241569079863014655459887957 1415443827322351496835281)
                    ·
                      rfl

theorem cell23_8269701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_8269701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269701 prefixEnd_8269701 := by exact prefixLift 8269701
  have htrace : WordTrace (prefixWord ++ tailWord_8269701) baseStart_8269701 baseEnd_8269701 := by
    simpa [prefixWord, tailWord_8269701, baseEnd_8269701] using wordTrace_append hprefix tailTrace_8269701
  have hstable : (prefixWord ++ tailWord_8269701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269701).length < 2 ^ (prefixWord ++ tailWord_8269701).sum := by decide
  have hdescent : baseEnd_8269701 < baseStart_8269701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269731 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 8]
def baseStart_8269731 : Nat := 118140960795 + 8269731 * 2 ^ 59
def prefixEnd_8269731 : Nat := 4983230072969 + 3 ^ 40 * 8269731 * 2
def baseEnd_8269731 : Nat := 1415448962128896457710235

theorem tailTrace_8269731 : CollatzResearch.WordTrace tailWord_8269731 prefixEnd_8269731 1415448962128896457710235 := by
  unfold tailWord_8269731
  simp only [CollatzResearch.WordTrace]
  refine ⟨301621868803184419456377047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201081245868789612970918031 301621868803184419456377047)
  ·
    refine ⟨452432803204776629184565571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301621868803184419456377047 452432803204776629184565571)
    ·
      refine ⟨678649204807164943776848357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452432803204776629184565571 678649204807164943776848357)
      ·
        refine ⟨127246725901343426958159067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678649204807164943776848357 127246725901343426958159067)
        ·
          refine ⟨190870088852015140437238601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127246725901343426958159067 190870088852015140437238601)
          ·
            refine ⟨143152566639011355327928951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190870088852015140437238601 143152566639011355327928951)
            ·
              refine ⟨214728849958517032991893427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143152566639011355327928951 214728849958517032991893427)
              ·
                refine ⟨322093274937775549487840141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214728849958517032991893427 322093274937775549487840141)
                ·
                  refine ⟨120784978101665831057940053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322093274937775549487840141 120784978101665831057940053)
                  ·
                    refine ⟨1415448962128896457710235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120784978101665831057940053 1415448962128896457710235)
                    ·
                      rfl

theorem cell23_8269731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_8269731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269731 prefixEnd_8269731 := by exact prefixLift 8269731
  have htrace : WordTrace (prefixWord ++ tailWord_8269731) baseStart_8269731 baseEnd_8269731 := by
    simpa [prefixWord, tailWord_8269731, baseEnd_8269731] using wordTrace_append hprefix tailTrace_8269731
  have hstable : (prefixWord ++ tailWord_8269731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269731).length < 2 ^ (prefixWord ++ tailWord_8269731).sum := by decide
  have hdescent : baseEnd_8269731 < baseStart_8269731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269749 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_8269749 : Nat := 118140960795 + 8269749 * 2 ^ 59
def prefixEnd_8269749 : Nat := 4983230072969 + 3 ^ 40 * 8269749 * 2
def baseEnd_8269749 : Nat := 4246356129038470302705623

theorem tailTrace_8269749 : CollatzResearch.WordTrace tailWord_8269749 prefixEnd_8269749 4246356129038470302705623 := by
  unfold tailWord_8269749
  simp only [CollatzResearch.WordTrace]
  refine ⟨301622525317119208530532301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201081683544746139020354867 301622525317119208530532301)
  ·
    refine ⟨113108446993919703198949613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301622525317119208530532301 113108446993919703198949613)
    ·
      refine ⟨42415667622719888699606105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113108446993919703198949613 42415667622719888699606105)
      ·
        refine ⟨31811750717039916524704579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42415667622719888699606105 31811750717039916524704579)
        ·
          refine ⟨47717626075559874787056869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31811750717039916524704579 47717626075559874787056869)
          ·
            refine ⟨8947054889167476522573163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47717626075559874787056869 8947054889167476522573163)
            ·
              refine ⟨13420582333751214783859745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947054889167476522573163 13420582333751214783859745)
              ·
                refine ⟨10065436750313411087894809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13420582333751214783859745 10065436750313411087894809)
                ·
                  refine ⟨7549077562735058315921107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10065436750313411087894809 7549077562735058315921107)
                  ·
                    refine ⟨11323616344102587473881661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549077562735058315921107 11323616344102587473881661)
                    ·
                      refine ⟨4246356129038470302705623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323616344102587473881661 4246356129038470302705623)
                      ·
                        rfl

theorem cell23_8269749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_8269749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269749 prefixEnd_8269749 := by exact prefixLift 8269749
  have htrace : WordTrace (prefixWord ++ tailWord_8269749) baseStart_8269749 baseEnd_8269749 := by
    simpa [prefixWord, tailWord_8269749, baseEnd_8269749] using wordTrace_append hprefix tailTrace_8269749
  have hstable : (prefixWord ++ tailWord_8269749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269749).length < 2 ^ (prefixWord ++ tailWord_8269749).sum := by decide
  have hdescent : baseEnd_8269749 < baseStart_8269749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269772 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_8269772 : Nat := 118140960795 + 8269772 * 2 ^ 59
def prefixEnd_8269772 : Nat := 4983230072969 + 3 ^ 40 * 8269772 * 2
def baseEnd_8269772 : Nat := 4246367939093523712718017

theorem tailTrace_8269772 : CollatzResearch.WordTrace tailWord_8269772 prefixEnd_8269772 4246367939093523712718017 := by
  unfold tailWord_8269772
  simp only [CollatzResearch.WordTrace]
  refine ⟨150811682098017941729309785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201082242797357255639079713 150811682098017941729309785)
  ·
    refine ⟨113108761573513456296982339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150811682098017941729309785 113108761573513456296982339)
    ·
      refine ⟨169663142360270184445473509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113108761573513456296982339 169663142360270184445473509)
      ·
        refine ⟨31811839192550659583526283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169663142360270184445473509 31811839192550659583526283)
        ·
          refine ⟨47717758788825989375289425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31811839192550659583526283 47717758788825989375289425)
          ·
            refine ⟨35788319091619492031467069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47717758788825989375289425 35788319091619492031467069)
            ·
              refine ⟨13420619659357309511800151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35788319091619492031467069 13420619659357309511800151)
              ·
                refine ⟨20130929489035964267700227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13420619659357309511800151 20130929489035964267700227)
                ·
                  refine ⟨30196394233553946401550341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20130929489035964267700227 30196394233553946401550341)
                  ·
                    refine ⟨5661823918791364950290689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30196394233553946401550341 5661823918791364950290689)
                    ·
                      refine ⟨4246367939093523712718017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5661823918791364950290689 4246367939093523712718017)
                      ·
                        rfl

theorem cell23_8269772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_8269772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269772 prefixEnd_8269772 := by exact prefixLift 8269772
  have htrace : WordTrace (prefixWord ++ tailWord_8269772) baseStart_8269772 baseEnd_8269772 := by
    simpa [prefixWord, tailWord_8269772, baseEnd_8269772] using wordTrace_append hprefix tailTrace_8269772
  have hstable : (prefixWord ++ tailWord_8269772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269772).length < 2 ^ (prefixWord ++ tailWord_8269772).sum := by decide
  have hdescent : baseEnd_8269772 < baseStart_8269772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269808 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_8269808 : Nat := 118140960795 + 8269808 * 2 ^ 59
def prefixEnd_8269808 : Nat := 4983230072969 + 3 ^ 40 * 8269808 * 2
def baseEnd_8269808 : Nat := 1415462141465695190622617

theorem tailTrace_8269808 : CollatzResearch.WordTrace tailWord_8269808 prefixEnd_8269808 1415462141465695190622617 := by
  unfold tailWord_8269808
  simp only [CollatzResearch.WordTrace]
  refine ⟨150812338611952730803465039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201083118149270307737953385 150812338611952730803465039)
  ·
    refine ⟨226218507917929096205197559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150812338611952730803465039 226218507917929096205197559)
    ·
      refine ⟨339327761876893644307796339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226218507917929096205197559 339327761876893644307796339)
      ·
        refine ⟨508991642815340466461694509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339327761876893644307796339 508991642815340466461694509)
        ·
          refine ⟨190871866055752674923135441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508991642815340466461694509 190871866055752674923135441)
          ·
            refine ⟨143153899541814506192351581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190871866055752674923135441 143153899541814506192351581)
            ·
              refine ⟨53682712328180439822131843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143153899541814506192351581 53682712328180439822131843)
              ·
                refine ⟨80524068492270659733197765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53682712328180439822131843 80524068492270659733197765)
                ·
                  refine ⟨15098262842300748699974581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80524068492270659733197765 15098262842300748699974581)
                  ·
                    refine ⟨1415462141465695190622617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15098262842300748699974581 1415462141465695190622617)
                    ·
                      rfl

theorem cell23_8269808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_8269808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269808 prefixEnd_8269808 := by exact prefixLift 8269808
  have htrace : WordTrace (prefixWord ++ tailWord_8269808) baseStart_8269808 baseEnd_8269808 := by
    simpa [prefixWord, tailWord_8269808, baseEnd_8269808] using wordTrace_append hprefix tailTrace_8269808
  have hstable : (prefixWord ++ tailWord_8269808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269808).length < 2 ^ (prefixWord ++ tailWord_8269808).sum := by decide
  have hdescent : baseEnd_8269808 < baseStart_8269808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269863 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 5]
def baseStart_8269863 : Nat := 118140960795 + 8269863 * 2 ^ 59
def prefixEnd_8269863 : Nat := 4983230072969 + 3 ^ 40 * 8269863 * 2
def baseEnd_8269863 : Nat := 471823851759231428520011

theorem tailTrace_8269863 : CollatzResearch.WordTrace tailWord_8269863 prefixEnd_8269863 471823851759231428520011 := by
  unfold tailWord_8269863
  simp only [CollatzResearch.WordTrace]
  refine ⟨301626683238706206000182243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201084455492470804000121495 301626683238706206000182243)
  ·
    refine ⟨452440024858059309000273365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301626683238706206000182243 452440024858059309000273365)
    ·
      refine ⟨10604063082610765054693907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 452440024858059309000273365 10604063082610765054693907)
      ·
        refine ⟨15906094623916147582040861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604063082610765054693907 15906094623916147582040861)
        ·
          refine ⟨5964785483968555343265323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15906094623916147582040861 5964785483968555343265323)
          ·
            refine ⟨8947178225952833014897985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964785483968555343265323 8947178225952833014897985)
            ·
              refine ⟨6710383669464624761173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8947178225952833014897985 6710383669464624761173489)
              ·
                refine ⟨5032787752098468570880117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710383669464624761173489 5032787752098468570880117)
                ·
                  refine ⟨471823851759231428520011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032787752098468570880117 471823851759231428520011)
                  ·
                    rfl

theorem cell23_8269863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 5].length) (baseStart_8269863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269863 prefixEnd_8269863 := by exact prefixLift 8269863
  have htrace : WordTrace (prefixWord ++ tailWord_8269863) baseStart_8269863 baseEnd_8269863 := by
    simpa [prefixWord, tailWord_8269863, baseEnd_8269863] using wordTrace_append hprefix tailTrace_8269863
  have hstable : (prefixWord ++ tailWord_8269863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269863).length < 2 ^ (prefixWord ++ tailWord_8269863).sum := by decide
  have hdescent : baseEnd_8269863 < baseStart_8269863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269885 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 6]
def baseStart_8269885 : Nat := 118140960795 + 8269885 * 2 ^ 59
def prefixEnd_8269885 : Nat := 4983230072969 + 3 ^ 40 * 8269885 * 2
def baseEnd_8269885 : Nat := 471825106934164641178333

theorem tailTrace_8269885 : CollatzResearch.WordTrace tailWord_8269885 prefixEnd_8269885 471825106934164641178333 := by
  unfold tailWord_8269885
  simp only [CollatzResearch.WordTrace]
  refine ⟨301627485644626503757483109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201084990429751002504988739 301627485644626503757483109)
  ·
    refine ⟨56555153558367469454528083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301627485644626503757483109 56555153558367469454528083)
    ·
      refine ⟨84832730337551204181792125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56555153558367469454528083 84832730337551204181792125)
      ·
        refine ⟨31812273876581701568172047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84832730337551204181792125 31812273876581701568172047)
        ·
          refine ⟨47718410814872552352258071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31812273876581701568172047 47718410814872552352258071)
          ·
            refine ⟨71577616222308828528387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47718410814872552352258071 71577616222308828528387107)
            ·
              refine ⟨107366424333463242792580661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71577616222308828528387107 107366424333463242792580661)
              ·
                refine ⟨10065602281262179011804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107366424333463242792580661 10065602281262179011804437)
                ·
                  refine ⟨471825106934164641178333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10065602281262179011804437 471825106934164641178333)
                  ·
                    rfl

theorem cell23_8269885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_8269885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269885 prefixEnd_8269885 := by exact prefixLift 8269885
  have htrace : WordTrace (prefixWord ++ tailWord_8269885) baseStart_8269885 baseEnd_8269885 := by
    simpa [prefixWord, tailWord_8269885, baseEnd_8269885] using wordTrace_append hprefix tailTrace_8269885
  have hstable : (prefixWord ++ tailWord_8269885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269885).length < 2 ^ (prefixWord ++ tailWord_8269885).sum := by decide
  have hdescent : baseEnd_8269885 < baseStart_8269885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269906 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_8269906 : Nat := 118140960795 + 8269906 * 2 ^ 59
def prefixEnd_8269906 : Nat := 4983230072969 + 3 ^ 40 * 8269906 * 2
def baseEnd_8269906 : Nat := 1415478915167075396147467

theorem tailTrace_8269906 : CollatzResearch.WordTrace tailWord_8269906 prefixEnd_8269906 1415478915167075396147467 := by
  unfold tailWord_8269906
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407062894387606085999393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201085501051700282895998381 75407062894387606085999393)
  ·
    refine ⟨56555297170790704564499545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75407062894387606085999393 56555297170790704564499545)
    ·
      refine ⟨42416472878093028423374659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56555297170790704564499545 42416472878093028423374659)
      ·
        refine ⟨63624709317139542635061989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42416472878093028423374659 63624709317139542635061989)
        ·
          refine ⟨11929632996963664244074123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63624709317139542635061989 11929632996963664244074123)
          ·
            refine ⟨17894449495445496366111185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11929632996963664244074123 17894449495445496366111185)
            ·
              refine ⟨13420837121584122274583389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17894449495445496366111185 13420837121584122274583389)
              ·
                refine ⟨5032813920594045852968771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13420837121584122274583389 5032813920594045852968771)
                ·
                  refine ⟨7549220880891068779453157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032813920594045852968771 7549220880891068779453157)
                  ·
                    refine ⟨1415478915167075396147467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549220880891068779453157 1415478915167075396147467)
                    ·
                      rfl

theorem cell23_8269906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_8269906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269906 prefixEnd_8269906 := by exact prefixLift 8269906
  have htrace : WordTrace (prefixWord ++ tailWord_8269906) baseStart_8269906 baseEnd_8269906 := by
    simpa [prefixWord, tailWord_8269906, baseEnd_8269906] using wordTrace_append hprefix tailTrace_8269906
  have hstable : (prefixWord ++ tailWord_8269906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269906).length < 2 ^ (prefixWord ++ tailWord_8269906).sum := by decide
  have hdescent : baseEnd_8269906 < baseStart_8269906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269929 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 1, 1, 3]
def baseStart_8269929 : Nat := 118140960795 + 8269929 * 2 ^ 59
def prefixEnd_8269929 : Nat := 4983230072969 + 3 ^ 40 * 8269929 * 2
def baseEnd_8269929 : Nat := 4246448555556279598454795

theorem tailTrace_8269929 : CollatzResearch.WordTrace tailWord_8269929 prefixEnd_8269929 4246448555556279598454795 := by
  unfold tailWord_8269929
  simp only [CollatzResearch.WordTrace]
  refine ⟨301629090456467099272084841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201086060304311399514723227 301629090456467099272084841)
  ·
    refine ⟨226221817842350324454063631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301629090456467099272084841 226221817842350324454063631)
    ·
      refine ⟨339332726763525486681095447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226221817842350324454063631 339332726763525486681095447)
      ·
        refine ⟨508999090145288230021643171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339332726763525486681095447 508999090145288230021643171)
        ·
          refine ⟨763498635217932345032464757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508999090145288230021643171 763498635217932345032464757)
          ·
            refine ⟨71577997051681157346793571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 763498635217932345032464757 71577997051681157346793571)
            ·
              refine ⟨107366995577521736020190357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71577997051681157346793571 107366995577521736020190357)
              ·
                refine ⟨5032827917696331375946423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107366995577521736020190357 5032827917696331375946423)
                ·
                  refine ⟨7549241876544497063919635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032827917696331375946423 7549241876544497063919635)
                  ·
                    refine ⟨11323862814816745595879453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549241876544497063919635 11323862814816745595879453)
                    ·
                      refine ⟨4246448555556279598454795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323862814816745595879453 4246448555556279598454795)
                      ·
                        rfl

theorem cell23_8269929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 1, 3].length) (baseStart_8269929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269929 prefixEnd_8269929 := by exact prefixLift 8269929
  have htrace : WordTrace (prefixWord ++ tailWord_8269929) baseStart_8269929 baseEnd_8269929 := by
    simpa [prefixWord, tailWord_8269929, baseEnd_8269929] using wordTrace_append hprefix tailTrace_8269929
  have hstable : (prefixWord ++ tailWord_8269929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269929).length < 2 ^ (prefixWord ++ tailWord_8269929).sum := by decide
  have hdescent : baseEnd_8269929 < baseStart_8269929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269962 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_8269962 : Nat := 118140960795 + 8269962 * 2 ^ 59
def prefixEnd_8269962 : Nat := 4983230072969 + 3 ^ 40 * 8269962 * 2
def baseEnd_8269962 : Nat := 1415488500139292656447381

theorem tailTrace_8269962 : CollatzResearch.WordTrace tailWord_8269962 prefixEnd_8269962 1415488500139292656447381 := by
  unfold tailWord_8269962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407573516336886477009035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201086862710231697272024093 75407573516336886477009035)
  ·
    refine ⟨113111360274505329715513553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75407573516336886477009035 113111360274505329715513553)
    ·
      refine ⟨84833520205878997286635165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113111360274505329715513553 84833520205878997286635165)
      ·
        refine ⟨31812570077204623982488187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84833520205878997286635165 31812570077204623982488187)
        ·
          refine ⟨47718855115806935973732281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31812570077204623982488187 47718855115806935973732281)
          ·
            refine ⟨35789141336855201980299211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47718855115806935973732281 35789141336855201980299211)
            ·
              refine ⟨53683712005282802970448817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35789141336855201980299211 53683712005282802970448817)
              ·
                refine ⟨40262784003962102227836613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53683712005282802970448817 40262784003962102227836613)
                ·
                  refine ⟨7549272000742894167719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40262784003962102227836613 7549272000742894167719365)
                  ·
                    refine ⟨1415488500139292656447381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549272000742894167719365 1415488500139292656447381)
                    ·
                      rfl

theorem cell23_8269962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_8269962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269962 prefixEnd_8269962 := by exact prefixLift 8269962
  have htrace : WordTrace (prefixWord ++ tailWord_8269962) baseStart_8269962 baseEnd_8269962 := by
    simpa [prefixWord, tailWord_8269962, baseEnd_8269962] using wordTrace_append hprefix tailTrace_8269962
  have hstable : (prefixWord ++ tailWord_8269962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269962).length < 2 ^ (prefixWord ++ tailWord_8269962).sum := by decide
  have hdescent : baseEnd_8269962 < baseStart_8269962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8269974 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8269974 : Nat := 118140960795 + 8269974 * 2 ^ 59
def prefixEnd_8269974 : Nat := 4983230072969 + 3 ^ 40 * 8269974 * 2
def baseEnd_8269974 : Nat := 1415490554061910640797363

theorem tailTrace_8269974 : CollatzResearch.WordTrace tailWord_8269974 prefixEnd_8269974 1415490554061910640797363 := by
  unfold tailWord_8269974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851920733831504497342061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201087154494202714638315317 18851920733831504497342061)
  ·
    refine ⟨7069470275186814186503273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18851920733831504497342061 7069470275186814186503273)
    ·
      refine ⟨5302102706390110639877455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7069470275186814186503273 5302102706390110639877455)
      ·
        refine ⟨7953154059585165959816183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302102706390110639877455 7953154059585165959816183)
        ·
          refine ⟨11929731089377748939724275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953154059585165959816183 11929731089377748939724275)
          ·
            refine ⟨17894596634066623409586413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11929731089377748939724275 17894596634066623409586413)
            ·
              refine ⟨6710473737774983778594905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17894596634066623409586413 6710473737774983778594905)
              ·
                refine ⟨5032855303331237833946179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710473737774983778594905 5032855303331237833946179)
                ·
                  refine ⟨7549282954996856750919269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032855303331237833946179 7549282954996856750919269)
                  ·
                    refine ⟨1415490554061910640797363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549282954996856750919269 1415490554061910640797363)
                    ·
                      rfl

theorem cell23_8269974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8269974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8269974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8269974 prefixEnd_8269974 := by exact prefixLift 8269974
  have htrace : WordTrace (prefixWord ++ tailWord_8269974) baseStart_8269974 baseEnd_8269974 := by
    simpa [prefixWord, tailWord_8269974, baseEnd_8269974] using wordTrace_append hprefix tailTrace_8269974
  have hstable : (prefixWord ++ tailWord_8269974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8269974).length < 2 ^ (prefixWord ++ tailWord_8269974).sum := by decide
  have hdescent : baseEnd_8269974 < baseStart_8269974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8269974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270002 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_8270002 : Nat := 118140960795 + 8270002 * 2 ^ 59
def prefixEnd_8270002 : Nat := 4983230072969 + 3 ^ 40 * 8270002 * 2
def baseEnd_8270002 : Nat := 4246486039644057812841959

theorem tailTrace_8270002 : CollatzResearch.WordTrace tailWord_8270002 prefixEnd_8270002 4246486039644057812841959 := by
  unfold tailWord_8270002
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407938246300658184873065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201087835323468421826328173 75407938246300658184873065)
  ·
    refine ⟨56555953684725493638654799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75407938246300658184873065 56555953684725493638654799)
    ·
      refine ⟨84833930527088240457982199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56555953684725493638654799 84833930527088240457982199)
      ·
        refine ⟨127250895790632360686973299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84833930527088240457982199 127250895790632360686973299)
        ·
          refine ⟨190876343685948541030459949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127250895790632360686973299 190876343685948541030459949)
          ·
            refine ⟨71578628882230702886422481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190876343685948541030459949 71578628882230702886422481)
            ·
              refine ⟨53683971661673027164816861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71578628882230702886422481 53683971661673027164816861)
              ·
                refine ⟨20131489373127385186806323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53683971661673027164816861 20131489373127385186806323)
                ·
                  refine ⟨30197234059691077780209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20131489373127385186806323 30197234059691077780209485)
                  ·
                    refine ⟨11323962772384154167578557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30197234059691077780209485 11323962772384154167578557)
                    ·
                      refine ⟨4246486039644057812841959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11323962772384154167578557 4246486039644057812841959)
                      ·
                        rfl

theorem cell23_8270002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_8270002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270002 prefixEnd_8270002 := by exact prefixLift 8270002
  have htrace : WordTrace (prefixWord ++ tailWord_8270002) baseStart_8270002 baseEnd_8270002 := by
    simpa [prefixWord, tailWord_8270002, baseEnd_8270002] using wordTrace_append hprefix tailTrace_8270002
  have hstable : (prefixWord ++ tailWord_8270002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270002).length < 2 ^ (prefixWord ++ tailWord_8270002).sum := by decide
  have hdescent : baseEnd_8270002 < baseStart_8270002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270037 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_8270037 : Nat := 118140960795 + 8270037 * 2 ^ 59
def prefixEnd_8270037 : Nat := 4983230072969 + 3 ^ 40 * 8270037 * 2
def baseEnd_8270037 : Nat := 4246504011466965175904299

theorem tailTrace_8270037 : CollatzResearch.WordTrace tailWord_8270037 prefixEnd_8270037 4246504011466965175904299 := by
  unfold tailWord_8270037
  simp only [CollatzResearch.WordTrace]
  refine ⟨301633029540075833717016365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201088686360050555811344243 301633029540075833717016365)
  ·
    refine ⟨113112386077528437643881137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301633029540075833717016365 113112386077528437643881137)
    ·
      refine ⟨84834289558146328232910853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113112386077528437643881137 84834289558146328232910853)
      ·
        refine ⟨15906429292152436543670785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84834289558146328232910853 15906429292152436543670785)
        ·
          refine ⟨11929821969114327407753089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15906429292152436543670785 11929821969114327407753089)
          ·
            refine ⟨8947366476835745555814817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11929821969114327407753089 8947366476835745555814817)
            ·
              refine ⟨6710524857626809166861113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8947366476835745555814817 6710524857626809166861113)
              ·
                refine ⟨5032893643220106875145835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710524857626809166861113 5032893643220106875145835)
                ·
                  refine ⟨7549340464830160312718753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032893643220106875145835 7549340464830160312718753)
                  ·
                    refine ⟨5662005348622620234539065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549340464830160312718753 5662005348622620234539065)
                    ·
                      refine ⟨4246504011466965175904299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662005348622620234539065 4246504011466965175904299)
                      ·
                        rfl

theorem cell23_8270037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_8270037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270037 prefixEnd_8270037 := by exact prefixLift 8270037
  have htrace : WordTrace (prefixWord ++ tailWord_8270037) baseStart_8270037 baseEnd_8270037 := by
    simpa [prefixWord, tailWord_8270037, baseEnd_8270037] using wordTrace_append hprefix tailTrace_8270037
  have hstable : (prefixWord ++ tailWord_8270037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270037).length < 2 ^ (prefixWord ++ tailWord_8270037).sum := by decide
  have hdescent : baseEnd_8270037 < baseStart_8270037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270059 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 4, 2]
def baseStart_8270059 : Nat := 118140960795 + 8270059 * 2 ^ 59
def prefixEnd_8270059 : Nat := 4983230072969 + 3 ^ 40 * 8270059 * 2
def baseEnd_8270059 : Nat := 4246515308041364089829197

theorem tailTrace_8270059 : CollatzResearch.WordTrace tailWord_8270059 prefixEnd_8270059 4246515308041364089829197 := by
  unfold tailWord_8270059
  simp only [CollatzResearch.WordTrace]
  refine ⟨301633831945996131474317231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201089221297330754316211487 301633831945996131474317231)
  ·
    refine ⟨452450747918994197211475847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301633831945996131474317231 452450747918994197211475847)
    ·
      refine ⟨678676121878491295817213771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452450747918994197211475847 678676121878491295817213771)
      ·
        refine ⟨1018014182817736943725820657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678676121878491295817213771 1018014182817736943725820657)
        ·
          refine ⟨763510637113302707794365493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018014182817736943725820657 763510637113302707794365493)
          ·
            refine ⟨71579122229372128855721765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 763510637113302707794365493 71579122229372128855721765)
            ·
              refine ⟨13421085418007274160447831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71579122229372128855721765 13421085418007274160447831)
              ·
                refine ⟨20131628127010911240671747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13421085418007274160447831 20131628127010911240671747)
                ·
                  refine ⟨30197442190516366861007621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20131628127010911240671747 30197442190516366861007621)
                  ·
                    refine ⟨5662020410721818786438929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30197442190516366861007621 5662020410721818786438929)
                    ·
                      refine ⟨4246515308041364089829197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662020410721818786438929 4246515308041364089829197)
                      ·
                        rfl

theorem cell23_8270059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4, 2].length) (baseStart_8270059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270059 prefixEnd_8270059 := by exact prefixLift 8270059
  have htrace : WordTrace (prefixWord ++ tailWord_8270059) baseStart_8270059 baseEnd_8270059 := by
    simpa [prefixWord, tailWord_8270059, baseEnd_8270059] using wordTrace_append hprefix tailTrace_8270059
  have hstable : (prefixWord ++ tailWord_8270059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270059).length < 2 ^ (prefixWord ++ tailWord_8270059).sum := by decide
  have hdescent : baseEnd_8270059 < baseStart_8270059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270062 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_8270062 : Nat := 118140960795 + 8270062 * 2 ^ 59
def prefixEnd_8270062 : Nat := 4983230072969 + 3 ^ 40 * 8270062 * 2
def baseEnd_8270062 : Nat := 4246516848483327578091683

theorem tailTrace_8270062 : CollatzResearch.WordTrace tailWord_8270062 prefixEnd_8270062 4246516848483327578091683 := by
  unfold tailWord_8270062
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704242670623157873334555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201089294243323508657784293 37704242670623157873334555)
  ·
    refine ⟨56556364005934736810001833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37704242670623157873334555 56556364005934736810001833)
    ·
      refine ⟨42417273004451052607501375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56556364005934736810001833 42417273004451052607501375)
      ·
        refine ⟨63625909506676578911252063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417273004451052607501375 63625909506676578911252063)
        ·
          refine ⟨95438864260014868366878095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63625909506676578911252063 95438864260014868366878095)
          ·
            refine ⟨143158296390022302550317143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95438864260014868366878095 143158296390022302550317143)
            ·
              refine ⟨214737444585033453825475715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143158296390022302550317143 214737444585033453825475715)
              ·
                refine ⟨322106166877550180738213573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214737444585033453825475715 322106166877550180738213573)
                ·
                  refine ⟨60394906289540658888415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322106166877550180738213573 60394906289540658888415045)
                  ·
                    refine ⟨11324044929288873541577821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60394906289540658888415045 11324044929288873541577821)
                    ·
                      refine ⟨4246516848483327578091683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324044929288873541577821 4246516848483327578091683)
                      ·
                        rfl

theorem cell23_8270062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_8270062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270062 prefixEnd_8270062 := by exact prefixLift 8270062
  have htrace : WordTrace (prefixWord ++ tailWord_8270062) baseStart_8270062 baseEnd_8270062 := by
    simpa [prefixWord, tailWord_8270062, baseEnd_8270062] using wordTrace_append hprefix tailTrace_8270062
  have hstable : (prefixWord ++ tailWord_8270062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270062).length < 2 ^ (prefixWord ++ tailWord_8270062).sum := by decide
  have hdescent : baseEnd_8270062 < baseStart_8270062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270065 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 9]
def baseStart_8270065 : Nat := 118140960795 + 8270065 * 2 ^ 59
def prefixEnd_8270065 : Nat := 4983230072969 + 3 ^ 40 * 8270065 * 2
def baseEnd_8270065 : Nat := 471835376547254562928241

theorem tailTrace_8270065 : CollatzResearch.WordTrace tailWord_8270065 prefixEnd_8270065 471835376547254562928241 := by
  unfold tailWord_8270065
  simp only [CollatzResearch.WordTrace]
  refine ⟨301634050783974394499035649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201089367189316262999357099 301634050783974394499035649)
  ·
    refine ⟨226225538087980795874276737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301634050783974394499035649 226225538087980795874276737)
    ·
      refine ⟨169669153565985596905707553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226225538087980795874276737 169669153565985596905707553)
      ·
        refine ⟨127251865174489197679280665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169669153565985596905707553 127251865174489197679280665)
        ·
          refine ⟨95438898880866898259460499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127251865174489197679280665 95438898880866898259460499)
          ·
            refine ⟨143158348321300347389190749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95438898880866898259460499 143158348321300347389190749)
            ·
              refine ⟨53684380620487630270946531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143158348321300347389190749 53684380620487630270946531)
              ·
                refine ⟨80526570930731445406419797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53684380620487630270946531 80526570930731445406419797)
                ·
                  refine ⟨471835376547254562928241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80526570930731445406419797 471835376547254562928241)
                  ·
                    rfl

theorem cell23_8270065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_8270065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270065 prefixEnd_8270065 := by exact prefixLift 8270065
  have htrace : WordTrace (prefixWord ++ tailWord_8270065) baseStart_8270065 baseEnd_8270065 := by
    simpa [prefixWord, tailWord_8270065, baseEnd_8270065] using wordTrace_append hprefix tailTrace_8270065
  have hstable : (prefixWord ++ tailWord_8270065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270065).length < 2 ^ (prefixWord ++ tailWord_8270065).sum := by decide
  have hdescent : baseEnd_8270065 < baseStart_8270065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270092 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_8270092 : Nat := 118140960795 + 8270092 * 2 ^ 59
def prefixEnd_8270092 : Nat := 4983230072969 + 3 ^ 40 * 8270092 * 2
def baseEnd_8270092 : Nat := 4246532252902962460716545

theorem tailTrace_8270092 : CollatzResearch.WordTrace tailWord_8270092 prefixEnd_8270092 4246532252902962460716545 := by
  unfold tailWord_8270092
  simp only [CollatzResearch.WordTrace]
  refine ⟨150817517777438289055134265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201090023703251052073512353 150817517777438289055134265)
  ·
    refine ⟨113113138333078716791350699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150817517777438289055134265 113113138333078716791350699)
    ·
      refine ⟨169669707499618075187026049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113113138333078716791350699 169669707499618075187026049)
      ·
        refine ⟨127252280624713556390269537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169669707499618075187026049 127252280624713556390269537)
        ·
          refine ⟨95439210468535167292702153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127252280624713556390269537 95439210468535167292702153)
          ·
            refine ⟨71579407851401375469526615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95439210468535167292702153 71579407851401375469526615)
            ·
              refine ⟨107369111777102063204289923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71579407851401375469526615 107369111777102063204289923)
              ·
                refine ⟨161053667665653094806434885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107369111777102063204289923 161053667665653094806434885)
                ·
                  refine ⟨30197562687309955276206541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161053667665653094806434885 30197562687309955276206541)
                  ·
                    refine ⟨11324086007741233228577453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30197562687309955276206541 11324086007741233228577453)
                    ·
                      refine ⟨4246532252902962460716545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324086007741233228577453 4246532252902962460716545)
                      ·
                        rfl

theorem cell23_8270092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_8270092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270092 prefixEnd_8270092 := by exact prefixLift 8270092
  have htrace : WordTrace (prefixWord ++ tailWord_8270092) baseStart_8270092 baseEnd_8270092 := by
    simpa [prefixWord, tailWord_8270092, baseEnd_8270092] using wordTrace_append hprefix tailTrace_8270092
  have hstable : (prefixWord ++ tailWord_8270092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270092).length < 2 ^ (prefixWord ++ tailWord_8270092).sum := by decide
  have hdescent : baseEnd_8270092 < baseStart_8270092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270110 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_8270110 : Nat := 118140960795 + 8270110 * 2 ^ 59
def prefixEnd_8270110 : Nat := 4983230072969 + 3 ^ 40 * 8270110 * 2
def baseEnd_8270110 : Nat := 4246541495554743390291463

theorem tailTrace_8270110 : CollatzResearch.WordTrace tailWord_8270110 prefixEnd_8270110 4246541495554743390291463 := by
  unfold tailWord_8270110
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704461508601420898052973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201090461379207578122949189 37704461508601420898052973)
  ·
    refine ⟨14139173065725532836769865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37704461508601420898052973 14139173065725532836769865)
    ·
      refine ⟨10604379799294149627577399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14139173065725532836769865 10604379799294149627577399)
      ·
        refine ⟨15906569698941224441366099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604379799294149627577399 15906569698941224441366099)
        ·
          refine ⟨23859854548411836662049149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906569698941224441366099 23859854548411836662049149)
          ·
            refine ⟨8947445455654438748268431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859854548411836662049149 8947445455654438748268431)
            ·
              refine ⟨13421168183481658122402647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947445455654438748268431 13421168183481658122402647)
              ·
                refine ⟨20131752275222487183603971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13421168183481658122402647 20131752275222487183603971)
                ·
                  refine ⟨30197628412833730775405957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20131752275222487183603971 30197628412833730775405957)
                  ·
                    refine ⟨5662055327406324520388617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30197628412833730775405957 5662055327406324520388617)
                    ·
                      refine ⟨4246541495554743390291463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662055327406324520388617 4246541495554743390291463)
                      ·
                        rfl

theorem cell23_8270110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_8270110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270110 prefixEnd_8270110 := by exact prefixLift 8270110
  have htrace : WordTrace (prefixWord ++ tailWord_8270110) baseStart_8270110 baseEnd_8270110 := by
    simpa [prefixWord, tailWord_8270110, baseEnd_8270110] using wordTrace_append hprefix tailTrace_8270110
  have hstable : (prefixWord ++ tailWord_8270110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270110).length < 2 ^ (prefixWord ++ tailWord_8270110).sum := by decide
  have hdescent : baseEnd_8270110 < baseStart_8270110 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270112 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 7]
def baseStart_8270112 : Nat := 118140960795 + 8270112 * 2 ^ 59
def prefixEnd_8270112 : Nat := 4983230072969 + 3 ^ 40 * 8270112 * 2
def baseEnd_8270112 : Nat := 1415514174172017460822151

theorem tailTrace_8270112 : CollatzResearch.WordTrace tailWord_8270112 prefixEnd_8270112 1415514174172017460822151 := by
  unfold tailWord_8270112
  simp only [CollatzResearch.WordTrace]
  refine ⟨150817882507402060762998295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201090510009869414350664393 150817882507402060762998295)
  ·
    refine ⟨226226823761103091144497443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150817882507402060762998295 226226823761103091144497443)
    ·
      refine ⟨339340235641654636716746165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226226823761103091144497443 339340235641654636716746165)
      ·
        refine ⟨31813147091405122192194953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339340235641654636716746165 31813147091405122192194953)
        ·
          refine ⟨23859860318553841644146215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31813147091405122192194953 23859860318553841644146215)
          ·
            refine ⟨35789790477830762466219323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23859860318553841644146215 35789790477830762466219323)
            ·
              refine ⟨53684685716746143699328985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35789790477830762466219323 53684685716746143699328985)
              ·
                refine ⟨40263514287559607774496739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53684685716746143699328985 40263514287559607774496739)
                ·
                  refine ⟨60395271431339411661745109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40263514287559607774496739 60395271431339411661745109)
                  ·
                    refine ⟨1415514174172017460822151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60395271431339411661745109 1415514174172017460822151)
                    ·
                      rfl

theorem cell23_8270112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_8270112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270112 prefixEnd_8270112 := by exact prefixLift 8270112
  have htrace : WordTrace (prefixWord ++ tailWord_8270112) baseStart_8270112 baseEnd_8270112 := by
    simpa [prefixWord, tailWord_8270112, baseEnd_8270112] using wordTrace_append hprefix tailTrace_8270112
  have hstable : (prefixWord ++ tailWord_8270112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270112).length < 2 ^ (prefixWord ++ tailWord_8270112).sum := by decide
  have hdescent : baseEnd_8270112 < baseStart_8270112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270162 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_8270162 : Nat := 118140960795 + 8270162 * 2 ^ 59
def prefixEnd_8270162 : Nat := 4983230072969 + 3 ^ 40 * 8270162 * 2
def baseEnd_8270162 : Nat := 4246568196548777186841223

theorem tailTrace_8270162 : CollatzResearch.WordTrace tailWord_8270162 prefixEnd_8270162 4246568196548777186841223 := by
  unfold tailWord_8270162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75409397166155745016329185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201091725776415320043544493 75409397166155745016329185)
  ·
    refine ⟨56557047874616808762246889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75409397166155745016329185 56557047874616808762246889)
    ·
      refine ⟨42417785905962606571685167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56557047874616808762246889 42417785905962606571685167)
      ·
        refine ⟨63626678858943909857527751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417785905962606571685167 63626678858943909857527751)
        ·
          refine ⟨95440018288415864786291627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63626678858943909857527751 95440018288415864786291627)
          ·
            refine ⟨143160027432623797179437441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95440018288415864786291627 143160027432623797179437441)
            ·
              refine ⟨107370020574467847884578081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143160027432623797179437441 107370020574467847884578081)
              ·
                refine ⟨80527515430850885913433561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107370020574467847884578081 80527515430850885913433561)
                ·
                  refine ⟨60395636573138164435075171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80527515430850885913433561 60395636573138164435075171)
                  ·
                    refine ⟨90593454859707246652612757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60395636573138164435075171 90593454859707246652612757)
                    ·
                      refine ⟨4246568196548777186841223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90593454859707246652612757 4246568196548777186841223)
                      ·
                        rfl

theorem cell23_8270162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_8270162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270162 prefixEnd_8270162 := by exact prefixLift 8270162
  have htrace : WordTrace (prefixWord ++ tailWord_8270162) baseStart_8270162 baseEnd_8270162 := by
    simpa [prefixWord, tailWord_8270162, baseEnd_8270162] using wordTrace_append hprefix tailTrace_8270162
  have hstable : (prefixWord ++ tailWord_8270162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270162).length < 2 ^ (prefixWord ++ tailWord_8270162).sum := by decide
  have hdescent : baseEnd_8270162 < baseStart_8270162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270186 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_8270186 : Nat := 118140960795 + 8270186 * 2 ^ 59
def prefixEnd_8270186 : Nat := 4983230072969 + 3 ^ 40 * 8270186 * 2
def baseEnd_8270186 : Nat := 4246580520084485092941113

theorem tailTrace_8270186 : CollatzResearch.WordTrace tailWord_8270186 prefixEnd_8270186 4246580520084485092941113 := by
  unfold tailWord_8270186
  simp only [CollatzResearch.WordTrace]
  refine ⟨75409616004134008041047603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201092309344357354776126941 75409616004134008041047603)
  ·
    refine ⟨113114424006201012061571405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75409616004134008041047603 113114424006201012061571405)
    ·
      refine ⟨42417909002325379523089277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113114424006201012061571405 42417909002325379523089277)
      ·
        refine ⟨15906715875872017321158479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42417909002325379523089277 15906715875872017321158479)
        ·
          refine ⟨23860073813808025981737719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906715875872017321158479 23860073813808025981737719)
          ·
            refine ⟨35790110720712038972606579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23860073813808025981737719 35790110720712038972606579)
            ·
              refine ⟨53685166081068058458909869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35790110720712038972606579 53685166081068058458909869)
              ·
                refine ⟨20131937280400521922091201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53685166081068058458909869 20131937280400521922091201)
                ·
                  refine ⟨15098952960300391441568401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20131937280400521922091201 15098952960300391441568401)
                  ·
                    refine ⟨11324214720225293581176301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15098952960300391441568401 11324214720225293581176301)
                    ·
                      refine ⟨4246580520084485092941113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324214720225293581176301 4246580520084485092941113)
                      ·
                        rfl

theorem cell23_8270186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_8270186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270186 prefixEnd_8270186 := by exact prefixLift 8270186
  have htrace : WordTrace (prefixWord ++ tailWord_8270186) baseStart_8270186 baseEnd_8270186 := by
    simpa [prefixWord, tailWord_8270186, baseEnd_8270186] using wordTrace_append hprefix tailTrace_8270186
  have hstable : (prefixWord ++ tailWord_8270186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270186).length < 2 ^ (prefixWord ++ tailWord_8270186).sum := by decide
  have hdescent : baseEnd_8270186 < baseStart_8270186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270199 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_8270199 : Nat := 118140960795 + 8270199 * 2 ^ 59
def prefixEnd_8270199 : Nat := 4983230072969 + 3 ^ 40 * 8270199 * 2
def baseEnd_8270199 : Nat := 4246587195332993542078553

theorem tailTrace_8270199 : CollatzResearch.WordTrace tailWord_8270199 prefixEnd_8270199 4246587195332993542078553 := by
  unfold tailWord_8270199
  simp only [CollatzResearch.WordTrace]
  refine ⟨301638938165488935384413651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201092625443659290256275767 301638938165488935384413651)
  ·
    refine ⟨452458407248233403076620477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301638938165488935384413651 452458407248233403076620477)
    ·
      refine ⟨169671902718087526153732679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452458407248233403076620477 169671902718087526153732679)
      ·
        refine ⟨254507854077131289230599019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169671902718087526153732679 254507854077131289230599019)
        ·
          refine ⟨381761781115696933845898529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254507854077131289230599019 381761781115696933845898529)
          ·
            refine ⟨286321335836772700384423897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381761781115696933845898529 286321335836772700384423897)
            ·
              refine ⟨214741001877579525288317923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286321335836772700384423897 214741001877579525288317923)
              ·
                refine ⟨322111502816369287932476885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214741001877579525288317923 322111502816369287932476885)
                ·
                  refine ⟨7549488347258655185917427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 322111502816369287932476885 7549488347258655185917427)
                  ·
                    refine ⟨11324232520887982778876141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549488347258655185917427 11324232520887982778876141)
                    ·
                      refine ⟨4246587195332993542078553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324232520887982778876141 4246587195332993542078553)
                      ·
                        rfl

theorem cell23_8270199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_8270199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270199 prefixEnd_8270199 := by exact prefixLift 8270199
  have htrace : WordTrace (prefixWord ++ tailWord_8270199) baseStart_8270199 baseEnd_8270199 := by
    simpa [prefixWord, tailWord_8270199, baseEnd_8270199] using wordTrace_append hprefix tailTrace_8270199
  have hstable : (prefixWord ++ tailWord_8270199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270199).length < 2 ^ (prefixWord ++ tailWord_8270199).sum := by decide
  have hdescent : baseEnd_8270199 < baseStart_8270199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270202 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_8270202 : Nat := 118140960795 + 8270202 * 2 ^ 59
def prefixEnd_8270202 : Nat := 4983230072969 + 3 ^ 40 * 8270202 * 2
def baseEnd_8270202 : Nat := 1415529578591652343447013

theorem tailTrace_8270202 : CollatzResearch.WordTrace tailWord_8270202 prefixEnd_8270202 1415529578591652343447013 := by
  unfold tailWord_8270202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75409761896119516724193215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201092698389652044597848573 75409761896119516724193215)
  ·
    refine ⟨113114642844179275086289823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75409761896119516724193215 113114642844179275086289823)
    ·
      refine ⟨169671964266268912629434735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113114642844179275086289823 169671964266268912629434735)
      ·
        refine ⟨254507946399403368944152103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169671964266268912629434735 254507946399403368944152103)
        ·
          refine ⟨381761919599105053416228155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254507946399403368944152103 381761919599105053416228155)
          ·
            refine ⟨572642879398657580124342233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381761919599105053416228155 572642879398657580124342233)
            ·
              refine ⟨429482159548993185093256675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572642879398657580124342233 429482159548993185093256675)
              ·
                refine ⟨644223239323489777639885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429482159548993185093256675 644223239323489777639885013)
                ·
                  refine ⟨15098982171644291663434805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 644223239323489777639885013 15098982171644291663434805)
                  ·
                    refine ⟨1415529578591652343447013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15098982171644291663434805 1415529578591652343447013)
                    ·
                      rfl

theorem cell23_8270202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_8270202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270202 prefixEnd_8270202 := by exact prefixLift 8270202
  have htrace : WordTrace (prefixWord ++ tailWord_8270202) baseStart_8270202 baseEnd_8270202 := by
    simpa [prefixWord, tailWord_8270202, baseEnd_8270202] using wordTrace_append hprefix tailTrace_8270202
  have hstable : (prefixWord ++ tailWord_8270202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270202).length < 2 ^ (prefixWord ++ tailWord_8270202).sum := by decide
  have hdescent : baseEnd_8270202 < baseStart_8270202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270216 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_8270216 : Nat := 118140960795 + 8270216 * 2 ^ 59
def prefixEnd_8270216 : Nat := 4983230072969 + 3 ^ 40 * 8270216 * 2
def baseEnd_8270216 : Nat := 4246595924504119975565975

theorem tailTrace_8270216 : CollatzResearch.WordTrace tailWord_8270216 prefixEnd_8270216 4246595924504119975565975 := by
  unfold tailWord_8270216
  simp only [CollatzResearch.WordTrace]
  refine ⟨150819779103213673643891251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201093038804284898191855001 150819779103213673643891251)
  ·
    refine ⟨226229668654820510465836877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150819779103213673643891251 226229668654820510465836877)
    ·
      refine ⟨84836125745557691424688829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226229668654820510465836877 84836125745557691424688829)
      ·
        refine ⟨31813547154584134284258311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84836125745557691424688829 31813547154584134284258311)
        ·
          refine ⟨47720320731876201426387467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31813547154584134284258311 47720320731876201426387467)
          ·
            refine ⟨71580481097814302139581201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47720320731876201426387467 71580481097814302139581201)
            ·
              refine ⟨53685360823360726604685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71580481097814302139581201 53685360823360726604685901)
              ·
                refine ⟨20132010308760272476757213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53685360823360726604685901 20132010308760272476757213)
                ·
                  refine ⟨7549503865785102178783955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20132010308760272476757213 7549503865785102178783955)
                  ·
                    refine ⟨11324255798677653268175933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549503865785102178783955 11324255798677653268175933)
                    ·
                      refine ⟨4246595924504119975565975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324255798677653268175933 4246595924504119975565975)
                      ·
                        rfl

theorem cell23_8270216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_8270216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270216 prefixEnd_8270216 := by exact prefixLift 8270216
  have htrace : WordTrace (prefixWord ++ tailWord_8270216) baseStart_8270216 baseEnd_8270216 := by
    simpa [prefixWord, tailWord_8270216, baseEnd_8270216] using wordTrace_append hprefix tailTrace_8270216
  have hstable : (prefixWord ++ tailWord_8270216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270216).length < 2 ^ (prefixWord ++ tailWord_8270216).sum := by decide
  have hdescent : baseEnd_8270216 < baseStart_8270216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270239 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_8270239 : Nat := 118140960795 + 8270239 * 2 ^ 59
def prefixEnd_8270239 : Nat := 4983230072969 + 3 ^ 40 * 8270239 * 2
def baseEnd_8270239 : Nat := 4246607734559173385578369

theorem tailTrace_8270239 : CollatzResearch.WordTrace tailWord_8270239 prefixEnd_8270239 4246607734559173385578369 := by
  unfold tailWord_8270239
  simp only [CollatzResearch.WordTrace]
  refine ⟨301640397085344022215869771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201093598056896014810579847 301640397085344022215869771)
  ·
    refine ⟨452460595628016033323804657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301640397085344022215869771 452460595628016033323804657)
    ·
      refine ⟨339345446721012024992853493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452460595628016033323804657 339345446721012024992853493)
      ·
        refine ⟨31813635630094877343080015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339345446721012024992853493 31813635630094877343080015)
        ·
          refine ⟨47720453445142316014620023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31813635630094877343080015 47720453445142316014620023)
          ·
            refine ⟨71580680167713474021930035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47720453445142316014620023 71580680167713474021930035)
            ·
              refine ⟨107371020251570211032895053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71580680167713474021930035 107371020251570211032895053)
              ·
                refine ⟨40264132594338829137335645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107371020251570211032895053 40264132594338829137335645)
                ·
                  refine ⟨15099049722877060926500867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40264132594338829137335645 15099049722877060926500867)
                  ·
                    refine ⟨22648574584315591389751301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15099049722877060926500867 22648574584315591389751301)
                    ·
                      refine ⟨4246607734559173385578369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22648574584315591389751301 4246607734559173385578369)
                      ·
                        rfl

theorem cell23_8270239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_8270239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270239 prefixEnd_8270239 := by exact prefixLift 8270239
  have htrace : WordTrace (prefixWord ++ tailWord_8270239) baseStart_8270239 baseEnd_8270239 := by
    simpa [prefixWord, tailWord_8270239, baseEnd_8270239] using wordTrace_append hprefix tailTrace_8270239
  have hstable : (prefixWord ++ tailWord_8270239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270239).length < 2 ^ (prefixWord ++ tailWord_8270239).sum := by decide
  have hdescent : baseEnd_8270239 < baseStart_8270239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270243 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 2, 3, 2]
def baseStart_8270243 : Nat := 118140960795 + 8270243 * 2 ^ 59
def prefixEnd_8270243 : Nat := 4983230072969 + 3 ^ 40 * 8270243 * 2
def baseEnd_8270243 : Nat := 4246609788481791369928351

theorem tailTrace_8270243 : CollatzResearch.WordTrace tailWord_8270243 prefixEnd_8270243 4246609788481791369928351 := by
  unfold tailWord_8270243
  simp only [CollatzResearch.WordTrace]
  refine ⟨301640542977329530899015383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201093695318219687266010255 301640542977329530899015383)
  ·
    refine ⟨452460814465994296348523075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301640542977329530899015383 452460814465994296348523075)
    ·
      refine ⟨678691221698991444522784613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452460814465994296348523075 678691221698991444522784613)
      ·
        refine ⟨127254604068560895848022115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678691221698991444522784613 127254604068560895848022115)
        ·
          refine ⟨190881906102841343772033173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127254604068560895848022115 190881906102841343772033173)
          ·
            refine ⟨8947589348570687989314055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190881906102841343772033173 8947589348570687989314055)
            ·
              refine ⟨13421384022856031983971083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947589348570687989314055 13421384022856031983971083)
              ·
                refine ⟨20132076034284047975956625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13421384022856031983971083 20132076034284047975956625)
                ·
                  refine ⟨15099057025713035981967469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20132076034284047975956625 15099057025713035981967469)
                  ·
                    refine ⟨5662146384642388493237801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15099057025713035981967469 5662146384642388493237801)
                    ·
                      refine ⟨4246609788481791369928351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662146384642388493237801 4246609788481791369928351)
                      ·
                        rfl

theorem cell23_8270243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_8270243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270243 prefixEnd_8270243 := by exact prefixLift 8270243
  have htrace : WordTrace (prefixWord ++ tailWord_8270243) baseStart_8270243 baseEnd_8270243 := by
    simpa [prefixWord, tailWord_8270243, baseEnd_8270243] using wordTrace_append hprefix tailTrace_8270243
  have hstable : (prefixWord ++ tailWord_8270243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270243).length < 2 ^ (prefixWord ++ tailWord_8270243).sum := by decide
  have hdescent : baseEnd_8270243 < baseStart_8270243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270252 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_8270252 : Nat := 118140960795 + 8270252 * 2 ^ 59
def prefixEnd_8270252 : Nat := 4983230072969 + 3 ^ 40 * 8270252 * 2
def baseEnd_8270252 : Nat := 4246614409807681834715809

theorem tailTrace_8270252 : CollatzResearch.WordTrace tailWord_8270252 prefixEnd_8270252 4246614409807681834715809 := by
  unfold tailWord_8270252
  simp only [CollatzResearch.WordTrace]
  refine ⟨150820435617148462718046505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201093914156197950290728673 150820435617148462718046505)
  ·
    refine ⟨113115326712861347038534879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150820435617148462718046505 113115326712861347038534879)
    ·
      refine ⟨169672990069292020557802319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113115326712861347038534879 169672990069292020557802319)
      ·
        refine ⟨254509485103938030836703479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169672990069292020557802319 254509485103938030836703479)
        ·
          refine ⟨381764227655907046255055219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254509485103938030836703479 381764227655907046255055219)
          ·
            refine ⟨572646341483860569382582829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381764227655907046255055219 572646341483860569382582829)
            ·
              refine ⟨214742378056447713518468561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572646341483860569382582829 214742378056447713518468561)
              ·
                refine ⟨161056783542335785138851421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214742378056447713518468561 161056783542335785138851421)
                ·
                  refine ⟨60396293828375919427069283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161056783542335785138851421 60396293828375919427069283)
                  ·
                    refine ⟨90594440742563879140603925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60396293828375919427069283 90594440742563879140603925)
                    ·
                      refine ⟨4246614409807681834715809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90594440742563879140603925 4246614409807681834715809)
                      ·
                        rfl

theorem cell23_8270252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_8270252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270252 prefixEnd_8270252 := by exact prefixLift 8270252
  have htrace : WordTrace (prefixWord ++ tailWord_8270252) baseStart_8270252 baseEnd_8270252 := by
    simpa [prefixWord, tailWord_8270252, baseEnd_8270252] using wordTrace_append hprefix tailTrace_8270252
  have hstable : (prefixWord ++ tailWord_8270252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270252).length < 2 ^ (prefixWord ++ tailWord_8270252).sum := by decide
  have hdescent : baseEnd_8270252 < baseStart_8270252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270253 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_8270253 : Nat := 118140960795 + 8270253 * 2 ^ 59
def prefixEnd_8270253 : Nat := 4983230072969 + 3 ^ 40 * 8270253 * 2
def baseEnd_8270253 : Nat := 1415538307762778776934435

theorem tailTrace_8270253 : CollatzResearch.WordTrace tailWord_8270253 prefixEnd_8270253 1415538307762778776934435 := by
  unfold tailWord_8270253
  simp only [CollatzResearch.WordTrace]
  refine ⟨301640907707293302606879413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201093938471528868404586275 301640907707293302606879413)
  ·
    refine ⟨28278835097558747119394945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301640907707293302606879413 28278835097558747119394945)
    ·
      refine ⟨21209126323169060339546209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28278835097558747119394945 21209126323169060339546209)
      ·
        refine ⟨15906844742376795254659657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21209126323169060339546209 15906844742376795254659657)
        ·
          refine ⟨11930133556782596440994743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15906844742376795254659657 11930133556782596440994743)
          ·
            refine ⟨17895200335173894661492115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930133556782596440994743 17895200335173894661492115)
            ·
              refine ⟨26842800502760841992238173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895200335173894661492115 26842800502760841992238173)
              ·
                refine ⟨10066050188535315747089315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26842800502760841992238173 10066050188535315747089315)
                ·
                  refine ⟨15099075282802973620633973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066050188535315747089315 15099075282802973620633973)
                  ·
                    refine ⟨1415538307762778776934435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15099075282802973620633973 1415538307762778776934435)
                    ·
                      rfl

theorem cell23_8270253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_8270253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270253 prefixEnd_8270253 := by exact prefixLift 8270253
  have htrace : WordTrace (prefixWord ++ tailWord_8270253) baseStart_8270253 baseEnd_8270253 := by
    simpa [prefixWord, tailWord_8270253, baseEnd_8270253] using wordTrace_append hprefix tailTrace_8270253
  have hstable : (prefixWord ++ tailWord_8270253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270253).length < 2 ^ (prefixWord ++ tailWord_8270253).sum := by decide
  have hdescent : baseEnd_8270253 < baseStart_8270253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270272 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_8270272 : Nat := 118140960795 + 8270272 * 2 ^ 59
def prefixEnd_8270272 : Nat := 4983230072969 + 3 ^ 40 * 8270272 * 2
def baseEnd_8270272 : Nat := 4246624679420771756465717

theorem tailTrace_8270272 : CollatzResearch.WordTrace tailWord_8270272 prefixEnd_8270272 4246624679420771756465717 := by
  unfold tailWord_8270272
  simp only [CollatzResearch.WordTrace]
  refine ⟨150820800347112234425910535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201094400462816312567880713 150820800347112234425910535)
  ·
    refine ⟨226231200520668351638865803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150820800347112234425910535 226231200520668351638865803)
    ·
      refine ⟨339346800781002527458298705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226231200520668351638865803 339346800781002527458298705)
      ·
        refine ⟨254510100585751895593724029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339346800781002527458298705 254510100585751895593724029)
        ·
          refine ⟨95441287719656960847646511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254510100585751895593724029 95441287719656960847646511)
          ·
            refine ⟨143161931579485441271469767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95441287719656960847646511 143161931579485441271469767)
            ·
              refine ⟨214742897369228161907204651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143161931579485441271469767 214742897369228161907204651)
              ·
                refine ⟨322114346053842242860806977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214742897369228161907204651 322114346053842242860806977)
                ·
                  refine ⟨241585759540381682145605233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322114346053842242860806977 241585759540381682145605233)
                  ·
                    refine ⟨181189319655286261609203925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241585759540381682145605233 181189319655286261609203925)
                    ·
                      refine ⟨4246624679420771756465717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181189319655286261609203925 4246624679420771756465717)
                      ·
                        rfl

theorem cell23_8270272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_8270272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270272 prefixEnd_8270272 := by exact prefixLift 8270272
  have htrace : WordTrace (prefixWord ++ tailWord_8270272) baseStart_8270272 baseEnd_8270272 := by
    simpa [prefixWord, tailWord_8270272, baseEnd_8270272] using wordTrace_append hprefix tailTrace_8270272
  have hstable : (prefixWord ++ tailWord_8270272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270272).length < 2 ^ (prefixWord ++ tailWord_8270272).sum := by decide
  have hdescent : baseEnd_8270272 < baseStart_8270272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270290 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_8270290 : Nat := 118140960795 + 8270290 * 2 ^ 59
def prefixEnd_8270290 : Nat := 4983230072969 + 3 ^ 40 * 8270290 * 2
def baseEnd_8270290 : Nat := 4246633922072552686040635

theorem tailTrace_8270290 : CollatzResearch.WordTrace tailWord_8270290 prefixEnd_8270290 4246633922072552686040635 := by
  unfold tailWord_8270290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75410564302039814481494081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201094838138772838617317549 75410564302039814481494081)
  ·
    refine ⟨56557923226529860861120561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75410564302039814481494081 56557923226529860861120561)
    ·
      refine ⟨42418442419897395645840421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56557923226529860861120561 42418442419897395645840421)
      ·
        refine ⟨7953457953730761683595079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42418442419897395645840421 7953457953730761683595079)
        ·
          refine ⟨11930186930596142525392619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953457953730761683595079 11930186930596142525392619)
          ·
            refine ⟨17895280395894213788088929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930186930596142525392619 17895280395894213788088929)
            ·
              refine ⟨13421460296920660341066697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17895280395894213788088929 13421460296920660341066697)
              ·
                refine ⟨10066095222690495255800023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13421460296920660341066697 10066095222690495255800023)
                ·
                  refine ⟨15099142834035742883700035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066095222690495255800023 15099142834035742883700035)
                  ·
                    refine ⟨22648714251053614325550053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15099142834035742883700035 22648714251053614325550053)
                    ·
                      refine ⟨4246633922072552686040635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22648714251053614325550053 4246633922072552686040635)
                      ·
                        rfl

theorem cell23_8270290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_8270290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270290 prefixEnd_8270290 := by exact prefixLift 8270290
  have htrace : WordTrace (prefixWord ++ tailWord_8270290) baseStart_8270290 baseEnd_8270290 := by
    simpa [prefixWord, tailWord_8270290, baseEnd_8270290] using wordTrace_append hprefix tailTrace_8270290
  have hstable : (prefixWord ++ tailWord_8270290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270290).length < 2 ^ (prefixWord ++ tailWord_8270290).sum := by decide
  have hdescent : baseEnd_8270290 < baseStart_8270290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270293 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_8270293 : Nat := 118140960795 + 8270293 * 2 ^ 59
def prefixEnd_8270293 : Nat := 4983230072969 + 3 ^ 40 * 8270293 * 2
def baseEnd_8270293 : Nat := 4246635462514516174303121

theorem tailTrace_8270293 : CollatzResearch.WordTrace tailWord_8270293 prefixEnd_8270293 4246635462514516174303121 := by
  unfold tailWord_8270293
  simp only [CollatzResearch.WordTrace]
  refine ⟨301642366627148389438335533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201094911084765592958890355 301642366627148389438335533)
  ·
    refine ⟨113115887485180646039375825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301642366627148389438335533 113115887485180646039375825)
    ·
      refine ⟨84836915613885484529531869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113115887485180646039375825 84836915613885484529531869)
      ·
        refine ⟨31813843355207056698574451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84836915613885484529531869 31813843355207056698574451)
        ·
          refine ⟨47720765032810585047861677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31813843355207056698574451 47720765032810585047861677)
          ·
            refine ⟨17895286887303969392948129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47720765032810585047861677 17895286887303969392948129)
            ·
              refine ⟨13421465165477977044711097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17895286887303969392948129 13421465165477977044711097)
              ·
                refine ⟨10066098874108482783533323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13421465165477977044711097 10066098874108482783533323)
                ·
                  refine ⟨15099148311162724175299985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066098874108482783533323 15099148311162724175299985)
                  ·
                    refine ⟨11324361233372043131474989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15099148311162724175299985 11324361233372043131474989)
                    ·
                      refine ⟨4246635462514516174303121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324361233372043131474989 4246635462514516174303121)
                      ·
                        rfl

theorem cell23_8270293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_8270293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270293 prefixEnd_8270293 := by exact prefixLift 8270293
  have htrace : WordTrace (prefixWord ++ tailWord_8270293) baseStart_8270293 baseEnd_8270293 := by
    simpa [prefixWord, tailWord_8270293, baseEnd_8270293] using wordTrace_append hprefix tailTrace_8270293
  have hstable : (prefixWord ++ tailWord_8270293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270293).length < 2 ^ (prefixWord ++ tailWord_8270293).sum := by decide
  have hdescent : baseEnd_8270293 < baseStart_8270293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270340 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_8270340 : Nat := 118140960795 + 8270340 * 2 ^ 59
def prefixEnd_8270340 : Nat := 4983230072969 + 3 ^ 40 * 8270340 * 2
def baseEnd_8270340 : Nat := 4246659596105277490415405

theorem tailTrace_8270340 : CollatzResearch.WordTrace tailWord_8270340 prefixEnd_8270340 4246659596105277490415405 := by
  unfold tailWord_8270340
  simp only [CollatzResearch.WordTrace]
  refine ⟨150822040428989058232648237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201096053905318744310197649 150822040428989058232648237)
  ·
    refine ⟨56558265160870896837243089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150822040428989058232648237 56558265160870896837243089)
    ·
      refine ⟨42418698870653172627932317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56558265160870896837243089 42418698870653172627932317)
      ·
        refine ⟨15907012076494939735474619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42418698870653172627932317 15907012076494939735474619)
        ·
          refine ⟨23860518114742409603211929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907012076494939735474619 23860518114742409603211929)
          ·
            refine ⟨17895388586056807202408947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23860518114742409603211929 17895388586056807202408947)
            ·
              refine ⟨26843082879085210803613421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895388586056807202408947 26843082879085210803613421)
              ·
                refine ⟨10066156079656954051355033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26843082879085210803613421 10066156079656954051355033)
                ·
                  refine ⟨7549617059742715538516275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066156079656954051355033 7549617059742715538516275)
                  ·
                    refine ⟨11324425589614073307774413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549617059742715538516275 11324425589614073307774413)
                    ·
                      refine ⟨4246659596105277490415405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324425589614073307774413 4246659596105277490415405)
                      ·
                        rfl

theorem cell23_8270340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_8270340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270340 prefixEnd_8270340 := by exact prefixLift 8270340
  have htrace : WordTrace (prefixWord ++ tailWord_8270340) baseStart_8270340 baseEnd_8270340 := by
    simpa [prefixWord, tailWord_8270340, baseEnd_8270340] using wordTrace_append hprefix tailTrace_8270340
  have hstable : (prefixWord ++ tailWord_8270340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270340).length < 2 ^ (prefixWord ++ tailWord_8270340).sum := by decide
  have hdescent : baseEnd_8270340 < baseStart_8270340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270350 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_8270350 : Nat := 118140960795 + 8270350 * 2 ^ 59
def prefixEnd_8270350 : Nat := 4983230072969 + 3 ^ 40 * 8270350 * 2
def baseEnd_8270350 : Nat := 4246664730911822451290359

theorem tailTrace_8270350 : CollatzResearch.WordTrace tailWord_8270350 prefixEnd_8270350 4246664730911822451290359 := by
  unfold tailWord_8270350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705555698492736021645063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201096297058627925448773669 37705555698492736021645063)
  ·
    refine ⟨56558333547739104032467595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37705555698492736021645063 56558333547739104032467595)
    ·
      refine ⟨84837500321608656048701393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56558333547739104032467595 84837500321608656048701393)
      ·
        refine ⟨63628125241206492036526045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84837500321608656048701393 63628125241206492036526045)
        ·
          refine ⟨23860546965452434513697267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63628125241206492036526045 23860546965452434513697267)
          ·
            refine ⟨35790820448178651770545901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23860546965452434513697267 35790820448178651770545901)
            ·
              refine ⟨13421557668066994413954713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35790820448178651770545901 13421557668066994413954713)
              ·
                refine ⟨10066168251050245810466035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13421557668066994413954713 10066168251050245810466035)
                ·
                  refine ⟨15099252376575368715699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066168251050245810466035 15099252376575368715699053)
                  ·
                    refine ⟨5662219641215763268387145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15099252376575368715699053 5662219641215763268387145)
                    ·
                      refine ⟨4246664730911822451290359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662219641215763268387145 4246664730911822451290359)
                      ·
                        rfl

theorem cell23_8270350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_8270350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270350 prefixEnd_8270350 := by exact prefixLift 8270350
  have htrace : WordTrace (prefixWord ++ tailWord_8270350) baseStart_8270350 baseEnd_8270350 := by
    simpa [prefixWord, tailWord_8270350, baseEnd_8270350] using wordTrace_append hprefix tailTrace_8270350
  have hstable : (prefixWord ++ tailWord_8270350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270350).length < 2 ^ (prefixWord ++ tailWord_8270350).sum := by decide
  have hdescent : baseEnd_8270350 < baseStart_8270350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270379 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3]
def baseStart_8270379 : Nat := 118140960795 + 8270379 * 2 ^ 59
def prefixEnd_8270379 : Nat := 4983230072969 + 3 ^ 40 * 8270379 * 2
def baseEnd_8270379 : Nat := 4246679621850802837827725

theorem tailTrace_8270379 : CollatzResearch.WordTrace tailWord_8270379 prefixEnd_8270379 4246679621850802837827725 := by
  unfold tailWord_8270379
  simp only [CollatzResearch.WordTrace]
  refine ⟨301645503304836826125966191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201097002203224550750644127 301645503304836826125966191)
  ·
    refine ⟨452468254957255239188949287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301645503304836826125966191 452468254957255239188949287)
    ·
      refine ⟨678702382435882858783423931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452468254957255239188949287 678702382435882858783423931)
      ·
        refine ⟨1018053573653824288175135897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678702382435882858783423931 1018053573653824288175135897)
        ·
          refine ⟨763540180240368216131351923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018053573653824288175135897 763540180240368216131351923)
          ·
            refine ⟨1145310270360552324197027885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763540180240368216131351923 1145310270360552324197027885)
            ·
              refine ⟨429491351385207121573885457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145310270360552324197027885 429491351385207121573885457)
              ·
                refine ⟨322118513538905341180414093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429491351385207121573885457 322118513538905341180414093)
                ·
                  refine ⟨120794442577089502942655285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322118513538905341180414093 120794442577089502942655285)
                  ·
                    refine ⟨11324478991602140900873933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120794442577089502942655285 11324478991602140900873933)
                    ·
                      refine ⟨4246679621850802837827725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324478991602140900873933 4246679621850802837827725)
                      ·
                        rfl

theorem cell23_8270379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 3].length) (baseStart_8270379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270379 prefixEnd_8270379 := by exact prefixLift 8270379
  have htrace : WordTrace (prefixWord ++ tailWord_8270379) baseStart_8270379 baseEnd_8270379 := by
    simpa [prefixWord, tailWord_8270379, baseEnd_8270379] using wordTrace_append hprefix tailTrace_8270379
  have hstable : (prefixWord ++ tailWord_8270379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270379).length < 2 ^ (prefixWord ++ tailWord_8270379).sum := by decide
  have hdescent : baseEnd_8270379 < baseStart_8270379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270396 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_8270396 : Nat := 118140960795 + 8270396 * 2 ^ 59
def prefixEnd_8270396 : Nat := 4983230072969 + 3 ^ 40 * 8270396 * 2
def baseEnd_8270396 : Nat := 4246688351021929271315147

theorem tailTrace_8270396 : CollatzResearch.WordTrace tailWord_8270396 prefixEnd_8270396 4246688351021929271315147 := by
  unfold tailWord_8270396
  simp only [CollatzResearch.WordTrace]
  refine ⟨150823061672887619014667521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201097415563850158686223361 150823061672887619014667521)
  ·
    refine ⟨113117296254665714261000641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150823061672887619014667521 113117296254665714261000641)
    ·
      refine ⟨84837972190999285695750481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113117296254665714261000641 84837972190999285695750481)
      ·
        refine ⟨63628479143249464271812861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84837972190999285695750481 63628479143249464271812861)
        ·
          refine ⟨23860679678718549101929823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63628479143249464271812861 23860679678718549101929823)
          ·
            refine ⟨35791019518077823652894735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23860679678718549101929823 35791019518077823652894735)
            ·
              refine ⟨53686529277116735479342103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35791019518077823652894735 53686529277116735479342103)
              ·
                refine ⟨80529793915675103219013155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53686529277116735479342103 80529793915675103219013155)
                ·
                  refine ⟨120794690873512654828519733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80529793915675103219013155 120794690873512654828519733)
                  ·
                    refine ⟨11324502269391811390173725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120794690873512654828519733 11324502269391811390173725)
                    ·
                      refine ⟨4246688351021929271315147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324502269391811390173725 4246688351021929271315147)
                      ·
                        rfl

theorem cell23_8270396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_8270396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270396 prefixEnd_8270396 := by exact prefixLift 8270396
  have htrace : WordTrace (prefixWord ++ tailWord_8270396) baseStart_8270396 baseEnd_8270396 := by
    simpa [prefixWord, tailWord_8270396, baseEnd_8270396] using wordTrace_append hprefix tailTrace_8270396
  have hstable : (prefixWord ++ tailWord_8270396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270396).length < 2 ^ (prefixWord ++ tailWord_8270396).sum := by decide
  have hdescent : baseEnd_8270396 < baseStart_8270396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270399 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 7]
def baseStart_8270399 : Nat := 118140960795 + 8270399 * 2 ^ 59
def prefixEnd_8270399 : Nat := 4983230072969 + 3 ^ 40 * 8270399 * 2
def baseEnd_8270399 : Nat := 1415563297154630919859211

theorem tailTrace_8270399 : CollatzResearch.WordTrace tailWord_8270399 prefixEnd_8270399 1415563297154630919859211 := by
  unfold tailWord_8270399
  simp only [CollatzResearch.WordTrace]
  refine ⟨301646232764764369541694251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201097488509842913027796167 301646232764764369541694251)
  ·
    refine ⟨452469349147146554312541377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301646232764764369541694251 452469349147146554312541377)
    ·
      refine ⟨339352011860359915734406033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452469349147146554312541377 339352011860359915734406033)
      ·
        refine ⟨254514008895269936800804525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339352011860359915734406033 254514008895269936800804525)
        ·
          refine ⟨95442753335726226300301697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254514008895269936800804525 95442753335726226300301697)
          ·
            refine ⟨71582065001794669725226273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95442753335726226300301697 71582065001794669725226273)
            ·
              refine ⟨53686548751346002293919705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71582065001794669725226273 53686548751346002293919705)
              ·
                refine ⟨40264911563509501720439779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53686548751346002293919705 40264911563509501720439779)
                ·
                  refine ⟨60397367345264252580659669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40264911563509501720439779 60397367345264252580659669)
                  ·
                    refine ⟨1415563297154630919859211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60397367345264252580659669 1415563297154630919859211)
                    ·
                      rfl

theorem cell23_8270399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_8270399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270399 prefixEnd_8270399 := by exact prefixLift 8270399
  have htrace : WordTrace (prefixWord ++ tailWord_8270399) baseStart_8270399 baseEnd_8270399 := by
    simpa [prefixWord, tailWord_8270399, baseEnd_8270399] using wordTrace_append hprefix tailTrace_8270399
  have hstable : (prefixWord ++ tailWord_8270399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270399).length < 2 ^ (prefixWord ++ tailWord_8270399).sum := by decide
  have hdescent : baseEnd_8270399 < baseStart_8270399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270436 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_8270436 : Nat := 118140960795 + 8270436 * 2 ^ 59
def prefixEnd_8270436 : Nat := 4983230072969 + 3 ^ 40 * 8270436 * 2
def baseEnd_8270436 : Nat := 4246708890248109114814963

theorem tailTrace_8270436 : CollatzResearch.WordTrace tailWord_8270436 prefixEnd_8270436 4246708890248109114814963 := by
  unfold tailWord_8270436
  simp only [CollatzResearch.WordTrace]
  refine ⟨150823791132815162430395581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201098388177086883240527441 150823791132815162430395581)
  ·
    refine ⟨56558921674805685911398343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150823791132815162430395581 56558921674805685911398343)
    ·
      refine ⟨84838382512208528867097515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56558921674805685911398343 84838382512208528867097515)
      ·
        refine ⟨127257573768312793300646273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84838382512208528867097515 127257573768312793300646273)
        ·
          refine ⟨95443180326234594975484705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127257573768312793300646273 95443180326234594975484705)
          ·
            refine ⟨71582385244675946231613529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95443180326234594975484705 71582385244675946231613529)
            ·
              refine ⟨53686788933506959673710147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71582385244675946231613529 53686788933506959673710147)
              ·
                refine ⟨80530183400260439510565221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53686788933506959673710147 80530183400260439510565221)
                ·
                  refine ⟨15099409387548832408230979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80530183400260439510565221 15099409387548832408230979)
                  ·
                    refine ⟨22649114081323248612346469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15099409387548832408230979 22649114081323248612346469)
                    ·
                      refine ⟨4246708890248109114814963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22649114081323248612346469 4246708890248109114814963)
                      ·
                        rfl

theorem cell23_8270436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_8270436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270436 prefixEnd_8270436 := by exact prefixLift 8270436
  have htrace : WordTrace (prefixWord ++ tailWord_8270436) baseStart_8270436 baseEnd_8270436 := by
    simpa [prefixWord, tailWord_8270436, baseEnd_8270436] using wordTrace_append hprefix tailTrace_8270436
  have hstable : (prefixWord ++ tailWord_8270436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270436).length < 2 ^ (prefixWord ++ tailWord_8270436).sum := by decide
  have hdescent : baseEnd_8270436 < baseStart_8270436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270456 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_8270456 : Nat := 118140960795 + 8270456 * 2 ^ 59
def prefixEnd_8270456 : Nat := 4983230072969 + 3 ^ 40 * 8270456 * 2
def baseEnd_8270456 : Nat := 4246719159861199036564871

theorem tailTrace_8270456 : CollatzResearch.WordTrace tailWord_8270456 prefixEnd_8270456 4246719159861199036564871 := by
  unfold tailWord_8270456
  simp only [CollatzResearch.WordTrace]
  refine ⟨150824155862778934138259611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201098874483705245517679481 150824155862778934138259611)
  ·
    refine ⟨226236233794168401207389417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150824155862778934138259611 226236233794168401207389417)
    ·
      refine ⟨169677175345626300905542063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226236233794168401207389417 169677175345626300905542063)
      ·
        refine ⟨254515763018439451358313095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169677175345626300905542063 254515763018439451358313095)
        ·
          refine ⟨381773644527659177037469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254515763018439451358313095 381773644527659177037469643)
          ·
            refine ⟨572660466791488765556204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381773644527659177037469643 572660466791488765556204465)
            ·
              refine ⟨429495350093616574167153349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572660466791488765556204465 429495350093616574167153349)
              ·
                refine ⟨80530378142553107656341253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429495350093616574167153349 80530378142553107656341253)
                ·
                  refine ⟨15099445901728707685563985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80530378142553107656341253 15099445901728707685563985)
                  ·
                    refine ⟨11324584426296530764172989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15099445901728707685563985 11324584426296530764172989)
                    ·
                      refine ⟨4246719159861199036564871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11324584426296530764172989 4246719159861199036564871)
                      ·
                        rfl

theorem cell23_8270456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_8270456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270456 prefixEnd_8270456 := by exact prefixLift 8270456
  have htrace : WordTrace (prefixWord ++ tailWord_8270456) baseStart_8270456 baseEnd_8270456 := by
    simpa [prefixWord, tailWord_8270456, baseEnd_8270456] using wordTrace_append hprefix tailTrace_8270456
  have hstable : (prefixWord ++ tailWord_8270456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270456).length < 2 ^ (prefixWord ++ tailWord_8270456).sum := by decide
  have hdescent : baseEnd_8270456 < baseStart_8270456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_8270479 : Nat := 118140960795 + 8270479 * 2 ^ 59
def prefixEnd_8270479 : Nat := 4983230072969 + 3 ^ 40 * 8270479 * 2
def baseEnd_8270479 : Nat := 4246730969916252446577265

theorem tailTrace_8270479 : CollatzResearch.WordTrace tailWord_8270479 prefixEnd_8270479 4246730969916252446577265 := by
  unfold tailWord_8270479
  simp only [CollatzResearch.WordTrace]
  refine ⟨301649150604474543204606491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201099433736316362136404327 301649150604474543204606491)
  ·
    refine ⟨452473725906711814806909737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301649150604474543204606491 452473725906711814806909737)
    ·
      refine ⟨339355294430033861105182303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452473725906711814806909737 339355294430033861105182303)
      ·
        refine ⟨509032941645050791657773455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339355294430033861105182303 509032941645050791657773455)
        ·
          refine ⟨763549412467576187486660183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509032941645050791657773455 763549412467576187486660183)
          ·
            refine ⟨1145324118701364281229990275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763549412467576187486660183 1145324118701364281229990275)
            ·
              refine ⟨1717986178052046421844985413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145324118701364281229990275 1717986178052046421844985413)
              ·
                refine ⟨322122408384758704095934765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1717986178052046421844985413 322122408384758704095934765)
                ·
                  refine ⟨120795903144284514035975537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322122408384758704095934765 120795903144284514035975537)
                  ·
                    refine ⟨90596927358213385526981653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120795903144284514035975537 90596927358213385526981653)
                    ·
                      refine ⟨4246730969916252446577265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90596927358213385526981653 4246730969916252446577265)
                      ·
                        rfl

theorem cell23_8270479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_8270479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270479 prefixEnd_8270479 := by exact prefixLift 8270479
  have htrace : WordTrace (prefixWord ++ tailWord_8270479) baseStart_8270479 baseEnd_8270479 := by
    simpa [prefixWord, tailWord_8270479, baseEnd_8270479] using wordTrace_append hprefix tailTrace_8270479
  have hstable : (prefixWord ++ tailWord_8270479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270479).length < 2 ^ (prefixWord ++ tailWord_8270479).sum := by decide
  have hdescent : baseEnd_8270479 < baseStart_8270479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270497 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_8270497 : Nat := 118140960795 + 8270497 * 2 ^ 59
def prefixEnd_8270497 : Nat := 4983230072969 + 3 ^ 40 * 8270497 * 2
def baseEnd_8270497 : Nat := 1415580070856011125384061

theorem tailTrace_8270497 : CollatzResearch.WordTrace tailWord_8270497 prefixEnd_8270497 1415580070856011125384061 := by
  unfold tailWord_8270497
  simp only [CollatzResearch.WordTrace]
  refine ⟨301649807118409332278761745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201099871412272888185841163 301649807118409332278761745)
  ·
    refine ⟨226237355338806999209071309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301649807118409332278761745 226237355338806999209071309)
    ·
      refine ⟨84839008252052624703401741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226237355338806999209071309 84839008252052624703401741)
      ·
        refine ⟨31814628094519734263775653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84839008252052624703401741 31814628094519734263775653)
        ·
          refine ⟨5965242767722450174457935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31814628094519734263775653 5965242767722450174457935)
          ·
            refine ⟨8947864151583675261686903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965242767722450174457935 8947864151583675261686903)
            ·
              refine ⟨13421796227375512892530355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947864151583675261686903 13421796227375512892530355)
              ·
                refine ⟨20132694341063269338795533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13421796227375512892530355 20132694341063269338795533)
                ·
                  refine ⟨7549760377898726002048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20132694341063269338795533 7549760377898726002048325)
                  ·
                    refine ⟨1415580070856011125384061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549760377898726002048325 1415580070856011125384061)
                    ·
                      rfl

theorem cell23_8270497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_8270497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270497 prefixEnd_8270497 := by exact prefixLift 8270497
  have htrace : WordTrace (prefixWord ++ tailWord_8270497) baseStart_8270497 baseEnd_8270497 := by
    simpa [prefixWord, tailWord_8270497, baseEnd_8270497] using wordTrace_append hprefix tailTrace_8270497
  have hstable : (prefixWord ++ tailWord_8270497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270497).length < 2 ^ (prefixWord ++ tailWord_8270497).sum := by decide
  have hdescent : baseEnd_8270497 < baseStart_8270497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270510 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_8270510 : Nat := 118140960795 + 8270510 * 2 ^ 59
def prefixEnd_8270510 : Nat := 4983230072969 + 3 ^ 40 * 8270510 * 2
def baseEnd_8270510 : Nat := 471860765312949091698847

theorem tailTrace_8270510 : CollatzResearch.WordTrace tailWord_8270510 prefixEnd_8270510 471860765312949091698847 := by
  unfold tailWord_8270510
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706285158420279437373123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201100187511574823665989989 37706285158420279437373123)
  ·
    refine ⟨56559427737630419156059685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37706285158420279437373123 56559427737630419156059685)
    ·
      refine ⟨10604892700805703591761191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56559427737630419156059685 10604892700805703591761191)
      ·
        refine ⟨15907339051208555387641787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604892700805703591761191 15907339051208555387641787)
        ·
          refine ⟨23861008576812833081462681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907339051208555387641787 23861008576812833081462681)
          ·
            refine ⟨17895756432609624811097011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23861008576812833081462681 17895756432609624811097011)
            ·
              refine ⟨26843634648914437216645517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895756432609624811097011 26843634648914437216645517)
              ·
                refine ⟨10066362993342913956242069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26843634648914437216645517 10066362993342913956242069)
                ·
                  refine ⟨471860765312949091698847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10066362993342913956242069 471860765312949091698847)
                  ·
                    rfl

theorem cell23_8270510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_8270510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270510 prefixEnd_8270510 := by exact prefixLift 8270510
  have htrace : WordTrace (prefixWord ++ tailWord_8270510) baseStart_8270510 baseEnd_8270510 := by
    simpa [prefixWord, tailWord_8270510, baseEnd_8270510] using wordTrace_append hprefix tailTrace_8270510
  have hstable : (prefixWord ++ tailWord_8270510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270510).length < 2 ^ (prefixWord ++ tailWord_8270510).sum := by decide
  have hdescent : baseEnd_8270510 < baseStart_8270510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270536 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 6]
def baseStart_8270536 : Nat := 118140960795 + 8270536 * 2 ^ 59
def prefixEnd_8270536 : Nat := 4983230072969 + 3 ^ 40 * 8270536 * 2
def baseEnd_8270536 : Nat := 1415586746104519574521501

theorem tailTrace_8270536 : CollatzResearch.WordTrace tailWord_8270536 prefixEnd_8270536 1415586746104519574521501 := by
  unfold tailWord_8270536
  simp only [CollatzResearch.WordTrace]
  refine ⟨150825614782634020969715731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201100819710178694626287641 150825614782634020969715731)
  ·
    refine ⟨226238422173951031454573597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150825614782634020969715731 226238422173951031454573597)
    ·
      refine ⟨84839408315231636795465099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226238422173951031454573597 84839408315231636795465099)
      ·
        refine ⟨127259112472847455193197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84839408315231636795465099 127259112472847455193197649)
        ·
          refine ⟨95444334354635591394898237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127259112472847455193197649 95444334354635591394898237)
          ·
            refine ⟨35791625382988346773086839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95444334354635591394898237 35791625382988346773086839)
            ·
              refine ⟨53687438074482520159630259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35791625382988346773086839 53687438074482520159630259)
              ·
                refine ⟨80531157111723780239445389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53687438074482520159630259 80531157111723780239445389)
                ·
                  refine ⟨30199183916896417589792021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80531157111723780239445389 30199183916896417589792021)
                  ·
                    refine ⟨1415586746104519574521501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30199183916896417589792021 1415586746104519574521501)
                    ·
                      rfl

theorem cell23_8270536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_8270536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270536 prefixEnd_8270536 := by exact prefixLift 8270536
  have htrace : WordTrace (prefixWord ++ tailWord_8270536) baseStart_8270536 baseEnd_8270536 := by
    simpa [prefixWord, tailWord_8270536, baseEnd_8270536] using wordTrace_append hprefix tailTrace_8270536
  have hstable : (prefixWord ++ tailWord_8270536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270536).length < 2 ^ (prefixWord ++ tailWord_8270536).sum := by decide
  have hdescent : baseEnd_8270536 < baseStart_8270536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270560 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2]
def baseStart_8270560 : Nat := 118140960795 + 8270560 * 2 ^ 59
def prefixEnd_8270560 : Nat := 4983230072969 + 3 ^ 40 * 8270560 * 2
def baseEnd_8270560 : Nat := 4246772561849266629664393

theorem tailTrace_8270560 : CollatzResearch.WordTrace tailWord_8270560 prefixEnd_8270560 4246772561849266629664393 := by
  unfold tailWord_8270560
  simp only [CollatzResearch.WordTrace]
  refine ⟨150826052458590547019152567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201101403278120729358870089 150826052458590547019152567)
  ·
    refine ⟨226239078687885820528728851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150826052458590547019152567 226239078687885820528728851)
    ·
      refine ⟨339358618031828730793093277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226239078687885820528728851 339358618031828730793093277)
      ·
        refine ⟨127259481761935774047409979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339358618031828730793093277 127259481761935774047409979)
        ·
          refine ⟨190889222642903661071114969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127259481761935774047409979 190889222642903661071114969)
          ·
            refine ⟨143166916982177745803336227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190889222642903661071114969 143166916982177745803336227)
            ·
              refine ⟨214750375473266618705004341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143166916982177745803336227 214750375473266618705004341)
              ·
                refine ⟨20132847700618745503594157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214750375473266618705004341 20132847700618745503594157)
                ·
                  refine ⟨7549817887732029563847809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20132847700618745503594157 7549817887732029563847809)
                  ·
                    refine ⟨5662363415799022172885857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549817887732029563847809 5662363415799022172885857)
                    ·
                      refine ⟨4246772561849266629664393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662363415799022172885857 4246772561849266629664393)
                      ·
                        rfl

theorem cell23_8270560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_8270560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270560 prefixEnd_8270560 := by exact prefixLift 8270560
  have htrace : WordTrace (prefixWord ++ tailWord_8270560) baseStart_8270560 baseEnd_8270560 := by
    simpa [prefixWord, tailWord_8270560, baseEnd_8270560] using wordTrace_append hprefix tailTrace_8270560
  have hstable : (prefixWord ++ tailWord_8270560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270560).length < 2 ^ (prefixWord ++ tailWord_8270560).sum := by decide
  have hdescent : baseEnd_8270560 < baseStart_8270560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270590 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_8270590 : Nat := 118140960795 + 8270590 * 2 ^ 59
def prefixEnd_8270590 : Nat := 4983230072969 + 3 ^ 40 * 8270590 * 2
def baseEnd_8270590 : Nat := 4246787966268901512289255

theorem tailTrace_8270590 : CollatzResearch.WordTrace tailWord_8270590 prefixEnd_8270590 4246787966268901512289255 := by
  unfold tailWord_8270590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706649888384051145237153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201102132738048272774598149 37706649888384051145237153)
  ·
    refine ⟨28279987416288038358927865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37706649888384051145237153 28279987416288038358927865)
    ·
      refine ⟨21209990562216028769195899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28279987416288038358927865 21209990562216028769195899)
      ·
        refine ⟨31814985843324043153793849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21209990562216028769195899 31814985843324043153793849)
        ·
          refine ⟨23861239382493032365345387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31814985843324043153793849 23861239382493032365345387)
          ·
            refine ⟨35791859073739548548018081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23861239382493032365345387 35791859073739548548018081)
            ·
              refine ⟨26843894305304661411013561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35791859073739548548018081 26843894305304661411013561)
              ·
                refine ⟨20132920728978496058260171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26843894305304661411013561 20132920728978496058260171)
                ·
                  refine ⟨30199381093467744087390257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20132920728978496058260171 30199381093467744087390257)
                  ·
                    refine ⟨22649535820100808065542693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30199381093467744087390257 22649535820100808065542693)
                    ·
                      refine ⟨4246787966268901512289255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22649535820100808065542693 4246787966268901512289255)
                      ·
                        rfl

theorem cell23_8270590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_8270590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270590 prefixEnd_8270590 := by exact prefixLift 8270590
  have htrace : WordTrace (prefixWord ++ tailWord_8270590) baseStart_8270590 baseEnd_8270590 := by
    simpa [prefixWord, tailWord_8270590, baseEnd_8270590] using wordTrace_append hprefix tailTrace_8270590
  have hstable : (prefixWord ++ tailWord_8270590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270590).length < 2 ^ (prefixWord ++ tailWord_8270590).sum := by decide
  have hdescent : baseEnd_8270590 < baseStart_8270590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270594 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_8270594 : Nat := 118140960795 + 8270594 * 2 ^ 59
def prefixEnd_8270594 : Nat := 4983230072969 + 3 ^ 40 * 8270594 * 2
def baseEnd_8270594 : Nat := 4246790020191519496639237

theorem tailTrace_8270594 : CollatzResearch.WordTrace tailWord_8270594 prefixEnd_8270594 4246790020191519496639237 := by
  unfold tailWord_8270594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75413336249764479461260709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201102229999371945230028557 75413336249764479461260709)
  ·
    refine ⟨14140000546830839898986383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75413336249764479461260709 14140000546830839898986383)
    ·
      refine ⟨21210000820246259848479575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14140000546830839898986383 21210000820246259848479575)
      ·
        refine ⟨31815001230369389772719363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21210000820246259848479575 31815001230369389772719363)
        ·
          refine ⟨47722501845554084659079045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31815001230369389772719363 47722501845554084659079045)
          ·
            refine ⟨8947969096041390873577321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47722501845554084659079045 8947969096041390873577321)
            ·
              refine ⟨6710976822031043155182991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8947969096041390873577321 6710976822031043155182991)
              ·
                refine ⟨10066465233046564732774487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710976822031043155182991 10066465233046564732774487)
                ·
                  refine ⟨15099697849569847099161731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066465233046564732774487 15099697849569847099161731)
                  ·
                    refine ⟨22649546774354770648742597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15099697849569847099161731 22649546774354770648742597)
                    ·
                      refine ⟨4246790020191519496639237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22649546774354770648742597 4246790020191519496639237)
                      ·
                        rfl

theorem cell23_8270594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_8270594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270594 prefixEnd_8270594 := by exact prefixLift 8270594
  have htrace : WordTrace (prefixWord ++ tailWord_8270594) baseStart_8270594 baseEnd_8270594 := by
    simpa [prefixWord, tailWord_8270594, baseEnd_8270594] using wordTrace_append hprefix tailTrace_8270594
  have hstable : (prefixWord ++ tailWord_8270594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270594).length < 2 ^ (prefixWord ++ tailWord_8270594).sum := by decide
  have hdescent : baseEnd_8270594 < baseStart_8270594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270634 : List Nat := [3, 1, 4, 3, 2, 1, 2, 7]
def baseStart_8270634 : Nat := 118140960795 + 8270634 * 2 ^ 59
def prefixEnd_8270634 : Nat := 4983230072969 + 3 ^ 40 * 8270634 * 2
def baseEnd_8270634 : Nat := 157289279978433308894039

theorem tailTrace_8270634 : CollatzResearch.WordTrace tailWord_8270634 prefixEnd_8270634 157289279978433308894039 := by
  unfold tailWord_8270634
  simp only [CollatzResearch.WordTrace]
  refine ⟨75413700979728251169124739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201103202612608669784332637 75413700979728251169124739)
  ·
    refine ⟨113120551469592376753687109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75413700979728251169124739 113120551469592376753687109)
    ·
      refine ⟨21210103400548570641316333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113120551469592376753687109 21210103400548570641316333)
      ·
        refine ⟨7953788775205713990493625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21210103400548570641316333 7953788775205713990493625)
        ·
          refine ⟨5965341581404285492870219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7953788775205713990493625 5965341581404285492870219)
          ·
            refine ⟨8948012372106428239305329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965341581404285492870219 8948012372106428239305329)
            ·
              refine ⟨6711009279079821179478997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948012372106428239305329 6711009279079821179478997)
              ·
                refine ⟨157289279978433308894039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6711009279079821179478997 157289279978433308894039)
                ·
                  rfl

theorem cell23_8270634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_8270634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270634 prefixEnd_8270634 := by exact prefixLift 8270634
  have htrace : WordTrace (prefixWord ++ tailWord_8270634) baseStart_8270634 baseEnd_8270634 := by
    simpa [prefixWord, tailWord_8270634, baseEnd_8270634] using wordTrace_append hprefix tailTrace_8270634
  have hstable : (prefixWord ++ tailWord_8270634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270634).length < 2 ^ (prefixWord ++ tailWord_8270634).sum := by decide
  have hdescent : baseEnd_8270634 < baseStart_8270634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270656 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 9]
def baseStart_8270656 : Nat := 118140960795 + 8270656 * 2 ^ 59
def prefixEnd_8270656 : Nat := 4983230072969 + 3 ^ 40 * 8270656 * 2
def baseEnd_8270656 : Nat := 471869095110233139340439

theorem tailTrace_8270656 : CollatzResearch.WordTrace tailWord_8270656 prefixEnd_8270656 471869095110233139340439 := by
  unfold tailWord_8270656
  simp only [CollatzResearch.WordTrace]
  refine ⟨150827803162416651216899911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201103737549888868289199881 150827803162416651216899911)
  ·
    refine ⟨226241704743624976825349867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150827803162416651216899911 226241704743624976825349867)
    ·
      refine ⟨339362557115437465238024801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226241704743624976825349867 339362557115437465238024801)
      ·
        refine ⟨254521917836578098928518601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339362557115437465238024801 254521917836578098928518601)
        ·
          refine ⟨190891438377433574196388951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254521917836578098928518601 190891438377433574196388951)
          ·
            refine ⟨286337157566150361294583427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190891438377433574196388951 286337157566150361294583427)
            ·
              refine ⟨429505736349225541941875141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286337157566150361294583427 429505736349225541941875141)
              ·
                refine ⟨80532325565479789114101589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429505736349225541941875141 80532325565479789114101589)
                ·
                  refine ⟨471869095110233139340439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80532325565479789114101589 471869095110233139340439)
                  ·
                    rfl

theorem cell23_8270656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_8270656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270656 prefixEnd_8270656 := by exact prefixLift 8270656
  have htrace : WordTrace (prefixWord ++ tailWord_8270656) baseStart_8270656 baseEnd_8270656 := by
    simpa [prefixWord, tailWord_8270656, baseEnd_8270656] using wordTrace_append hprefix tailTrace_8270656
  have hstable : (prefixWord ++ tailWord_8270656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270656).length < 2 ^ (prefixWord ++ tailWord_8270656).sum := by decide
  have hdescent : baseEnd_8270656 < baseStart_8270656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270713 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_8270713 : Nat := 118140960795 + 8270713 * 2 ^ 59
def prefixEnd_8270713 : Nat := 4983230072969 + 3 ^ 40 * 8270713 * 2
def baseEnd_8270713 : Nat := 4246851124389404531051189

theorem tailTrace_8270713 : CollatzResearch.WordTrace tailWord_8270713 prefixEnd_8270713 4246851124389404531051189 := by
  unfold tailWord_8270713
  simp only [CollatzResearch.WordTrace]
  refine ⟨301657685285626801168624793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201105123523751200779083195 301657685285626801168624793)
  ·
    refine ⟨226243263964220100876468595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301657685285626801168624793 226243263964220100876468595)
    ·
      refine ⟨339364895946330151314702893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226243263964220100876468595 339364895946330151314702893)
      ·
        refine ⟨127261835979873806743013585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339364895946330151314702893 127261835979873806743013585)
        ·
          refine ⟨95446376984905355057260189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127261835979873806743013585 95446376984905355057260189)
          ·
            refine ⟨35792391369339508146472571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95446376984905355057260189 35792391369339508146472571)
            ·
              refine ⟨53688587054009262219708857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35792391369339508146472571 53688587054009262219708857)
              ·
                refine ⟨40266440290506946664781643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53688587054009262219708857 40266440290506946664781643)
                ·
                  refine ⟨60399660435760419997172465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40266440290506946664781643 60399660435760419997172465)
                  ·
                    refine ⟨45299745326820314997879349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60399660435760419997172465 45299745326820314997879349)
                    ·
                      refine ⟨4246851124389404531051189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45299745326820314997879349 4246851124389404531051189)
                      ·
                        rfl

theorem cell23_8270713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_8270713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270713 prefixEnd_8270713 := by exact prefixLift 8270713
  have htrace : WordTrace (prefixWord ++ tailWord_8270713) baseStart_8270713 baseEnd_8270713 := by
    simpa [prefixWord, tailWord_8270713, baseEnd_8270713] using wordTrace_append hprefix tailTrace_8270713
  have hstable : (prefixWord ++ tailWord_8270713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270713).length < 2 ^ (prefixWord ++ tailWord_8270713).sum := by decide
  have hdescent : baseEnd_8270713 < baseStart_8270713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270718 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8270718 : Nat := 118140960795 + 8270718 * 2 ^ 59
def prefixEnd_8270718 : Nat := 4983230072969 + 3 ^ 40 * 8270718 * 2
def baseEnd_8270718 : Nat := 4246853691792677011488667

theorem tailTrace_8270718 : CollatzResearch.WordTrace tailWord_8270718 prefixEnd_8270718 4246853691792677011488667 := by
  unfold tailWord_8270718
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707233456326085877819601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201105245100405791348371205 37707233456326085877819601)
  ·
    refine ⟨28280425092244564408364701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37707233456326085877819601 28280425092244564408364701)
    ·
      refine ⟨10605159409591711653136763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28280425092244564408364701 10605159409591711653136763)
      ·
        refine ⟨15907739114387567479705145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605159409591711653136763 15907739114387567479705145)
        ·
          refine ⟨11930804335790675609778859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15907739114387567479705145 11930804335790675609778859)
          ·
            refine ⟨17896206503686013414668289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930804335790675609778859 17896206503686013414668289)
            ·
              refine ⟨13422154877764510061001217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17896206503686013414668289 13422154877764510061001217)
              ·
                refine ⟨10066616158323382545750913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13422154877764510061001217 10066616158323382545750913)
                ·
                  refine ⟨7549962118742536909313185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066616158323382545750913 7549962118742536909313185)
                  ·
                    refine ⟨5662471589056902681984889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7549962118742536909313185 5662471589056902681984889)
                    ·
                      refine ⟨4246853691792677011488667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662471589056902681984889 4246853691792677011488667)
                      ·
                        rfl

theorem cell23_8270718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8270718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270718 prefixEnd_8270718 := by exact prefixLift 8270718
  have htrace : WordTrace (prefixWord ++ tailWord_8270718) baseStart_8270718 baseEnd_8270718 := by
    simpa [prefixWord, tailWord_8270718, baseEnd_8270718] using wordTrace_append hprefix tailTrace_8270718
  have hstable : (prefixWord ++ tailWord_8270718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270718).length < 2 ^ (prefixWord ++ tailWord_8270718).sum := by decide
  have hdescent : baseEnd_8270718 < baseStart_8270718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270730 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8270730 : Nat := 118140960795 + 8270730 * 2 ^ 59
def prefixEnd_8270730 : Nat := 4983230072969 + 3 ^ 40 * 8270730 * 2
def baseEnd_8270730 : Nat := 4246859853560530964538611

theorem tailTrace_8270730 : CollatzResearch.WordTrace tailWord_8270730 prefixEnd_8270730 4246859853560530964538611 := by
  unfold tailWord_8270730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75414576331641303267998411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201105536884376808714662429 75414576331641303267998411)
  ·
    refine ⟨113121864497461954901997617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75414576331641303267998411 113121864497461954901997617)
    ·
      refine ⟨84841398373096466176498213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113121864497461954901997617 84841398373096466176498213)
      ·
        refine ⟨15907762194955587408093415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84841398373096466176498213 15907762194955587408093415)
        ·
          refine ⟨23861643292433381112140123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907762194955587408093415 23861643292433381112140123)
          ·
            refine ⟨35792464938650071668210185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23861643292433381112140123 35792464938650071668210185)
            ·
              refine ⟨26844348703987553751157639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35792464938650071668210185 26844348703987553751157639)
              ·
                refine ⟨40266523055981330626736459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26844348703987553751157639 40266523055981330626736459)
                ·
                  refine ⟨60399784583971995940104689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40266523055981330626736459 60399784583971995940104689)
                  ·
                    refine ⟨45299838437978996955078517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60399784583971995940104689 45299838437978996955078517)
                    ·
                      refine ⟨4246859853560530964538611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45299838437978996955078517 4246859853560530964538611)
                      ·
                        rfl

theorem cell23_8270730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8270730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270730 prefixEnd_8270730 := by exact prefixLift 8270730
  have htrace : WordTrace (prefixWord ++ tailWord_8270730) baseStart_8270730 baseEnd_8270730 := by
    simpa [prefixWord, tailWord_8270730, baseEnd_8270730] using wordTrace_append hprefix tailTrace_8270730
  have hstable : (prefixWord ++ tailWord_8270730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270730).length < 2 ^ (prefixWord ++ tailWord_8270730).sum := by decide
  have hdescent : baseEnd_8270730 < baseStart_8270730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270740 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_8270740 : Nat := 118140960795 + 8270740 * 2 ^ 59
def prefixEnd_8270740 : Nat := 4983230072969 + 3 ^ 40 * 8270740 * 2
def baseEnd_8270740 : Nat := 4246864988367075925413565

theorem tailTrace_8270740 : CollatzResearch.WordTrace tailWord_8270740 prefixEnd_8270740 4246864988367075925413565 := by
  unfold tailWord_8270740
  simp only [CollatzResearch.WordTrace]
  refine ⟨150829335028264492389928837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201105780037685989853238449 150829335028264492389928837)
  ·
    refine ⟨28280500317799592323111657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150829335028264492389928837 28280500317799592323111657)
    ·
      refine ⟨21210375238349694242333743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28280500317799592323111657 21210375238349694242333743)
      ·
        refine ⟨31815562857524541363500615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21210375238349694242333743 31815562857524541363500615)
        ·
          refine ⟨47723344286286812045250923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31815562857524541363500615 47723344286286812045250923)
          ·
            refine ⟨71585016429430218067876385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47723344286286812045250923 71585016429430218067876385)
            ·
              refine ⟨53688762322072663550907289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71585016429430218067876385 53688762322072663550907289)
              ·
                refine ⟨40266571741554497663180467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53688762322072663550907289 40266571741554497663180467)
                ·
                  refine ⟨60399857612331746494770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40266571741554497663180467 60399857612331746494770701)
                  ·
                    refine ⟨22649946604624404935539013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60399857612331746494770701 22649946604624404935539013)
                    ·
                      refine ⟨4246864988367075925413565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22649946604624404935539013 4246864988367075925413565)
                      ·
                        rfl

theorem cell23_8270740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_8270740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270740 prefixEnd_8270740 := by exact prefixLift 8270740
  have htrace : WordTrace (prefixWord ++ tailWord_8270740) baseStart_8270740 baseEnd_8270740 := by
    simpa [prefixWord, tailWord_8270740, baseEnd_8270740] using wordTrace_append hprefix tailTrace_8270740
  have hstable : (prefixWord ++ tailWord_8270740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270740).length < 2 ^ (prefixWord ++ tailWord_8270740).sum := by decide
  have hdescent : baseEnd_8270740 < baseStart_8270740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270817 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_8270817 : Nat := 118140960795 + 8270817 * 2 ^ 59
def prefixEnd_8270817 : Nat := 4983230072969 + 3 ^ 40 * 8270817 * 2
def baseEnd_8270817 : Nat := 4246904526377472124150711

theorem tailTrace_8270817 : CollatzResearch.WordTrace tailWord_8270817 prefixEnd_8270817 4246904526377472124150711 := by
  unfold tailWord_8270817
  simp only [CollatzResearch.WordTrace]
  refine ⟨301661478477250026930410705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201107652318166684620273803 301661478477250026930410705)
  ·
    refine ⟨226246108857937520197808029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301661478477250026930410705 226246108857937520197808029)
    ·
      refine ⟨84842290821726570074178011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226246108857937520197808029 84842290821726570074178011)
      ·
        refine ⟨127263436232589855111267017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84842290821726570074178011 127263436232589855111267017)
        ·
          refine ⟨95447577174442391333450263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127263436232589855111267017 95447577174442391333450263)
          ·
            refine ⟨143171365761663587000175395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95447577174442391333450263 143171365761663587000175395)
            ·
              refine ⟨214757048642495380500263093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143171365761663587000175395 214757048642495380500263093)
              ·
                refine ⟨20133473310233941921899665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214757048642495380500263093 20133473310233941921899665)
                ·
                  refine ⟨15100104982675456441424749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20133473310233941921899665 15100104982675456441424749)
                  ·
                    refine ⟨5662539368503296165534281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15100104982675456441424749 5662539368503296165534281)
                    ·
                      refine ⟨4246904526377472124150711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662539368503296165534281 4246904526377472124150711)
                      ·
                        rfl

theorem cell23_8270817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_8270817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270817 prefixEnd_8270817 := by exact prefixLift 8270817
  have htrace : WordTrace (prefixWord ++ tailWord_8270817) baseStart_8270817 baseEnd_8270817 := by
    simpa [prefixWord, tailWord_8270817, baseEnd_8270817] using wordTrace_append hprefix tailTrace_8270817
  have hstable : (prefixWord ++ tailWord_8270817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270817).length < 2 ^ (prefixWord ++ tailWord_8270817).sum := by decide
  have hdescent : baseEnd_8270817 < baseStart_8270817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270818 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_8270818 : Nat := 118140960795 + 8270818 * 2 ^ 59
def prefixEnd_8270818 : Nat := 4983230072969 + 3 ^ 40 * 8270818 * 2
def baseEnd_8270818 : Nat := 1415635013286042206746069

theorem tailTrace_8270818 : CollatzResearch.WordTrace tailWord_8270818 prefixEnd_8270818 1415635013286042206746069 := by
  unfold tailWord_8270818
  simp only [CollatzResearch.WordTrace]
  refine ⟨75415378737561601025299277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201107676633497602734131405 75415378737561601025299277)
  ·
    refine ⟨28280767026585600384487229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75415378737561601025299277 28280767026585600384487229)
    ·
      refine ⟨10605287634969600144182711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28280767026585600384487229 10605287634969600144182711)
      ·
        refine ⟨15907931452454400216274067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605287634969600144182711 15907931452454400216274067)
        ·
          refine ⟨23861897178681600324411101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907931452454400216274067 23861897178681600324411101)
          ·
            refine ⟨8948211442005600121654163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23861897178681600324411101 8948211442005600121654163)
            ·
              refine ⟨13422317163008400182481245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948211442005600121654163 13422317163008400182481245)
              ·
                refine ⟨5033368936128150068430467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13422317163008400182481245 5033368936128150068430467)
                ·
                  refine ⟨7550053404192225102645701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033368936128150068430467 7550053404192225102645701)
                  ·
                    refine ⟨1415635013286042206746069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550053404192225102645701 1415635013286042206746069)
                    ·
                      rfl

theorem cell23_8270818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_8270818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270818 prefixEnd_8270818 := by exact prefixLift 8270818
  have htrace : WordTrace (prefixWord ++ tailWord_8270818) baseStart_8270818 baseEnd_8270818 := by
    simpa [prefixWord, tailWord_8270818, baseEnd_8270818] using wordTrace_append hprefix tailTrace_8270818
  have hstable : (prefixWord ++ tailWord_8270818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270818).length < 2 ^ (prefixWord ++ tailWord_8270818).sum := by decide
  have hdescent : baseEnd_8270818 < baseStart_8270818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270841 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 1, 1, 3]
def baseStart_8270841 : Nat := 118140960795 + 8270841 * 2 ^ 59
def prefixEnd_8270841 : Nat := 4983230072969 + 3 ^ 40 * 8270841 * 2
def baseEnd_8270841 : Nat := 4246916849913180030250601

theorem tailTrace_8270841 : CollatzResearch.WordTrace tailWord_8270841 prefixEnd_8270841 4246916849913180030250601 := by
  unfold tailWord_8270841
  simp only [CollatzResearch.WordTrace]
  refine ⟨301662353829163079029284377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201108235886108719352856251 301662353829163079029284377)
  ·
    refine ⟨226246765371872309271963283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301662353829163079029284377 226246765371872309271963283)
    ·
      refine ⟨339370148057808463907944925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226246765371872309271963283 339370148057808463907944925)
      ·
        refine ⟨127263805521678173965479347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339370148057808463907944925 127263805521678173965479347)
        ·
          refine ⟨190895708282517260948219021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127263805521678173965479347 190895708282517260948219021)
          ·
            refine ⟨71585890605943972855582133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190895708282517260948219021 71585890605943972855582133)
            ·
              refine ⟨6711177244307247455210825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71585890605943972855582133 6711177244307247455210825)
              ·
                refine ⟨5033382933230435591408119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711177244307247455210825 5033382933230435591408119)
                ·
                  refine ⟨7550074399845653387112179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033382933230435591408119 7550074399845653387112179)
                  ·
                    refine ⟨11325111599768480080668269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550074399845653387112179 11325111599768480080668269)
                    ·
                      refine ⟨4246916849913180030250601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11325111599768480080668269 4246916849913180030250601)
                      ·
                        rfl

theorem cell23_8270841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_8270841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270841 prefixEnd_8270841 := by exact prefixLift 8270841
  have htrace : WordTrace (prefixWord ++ tailWord_8270841) baseStart_8270841 baseEnd_8270841 := by
    simpa [prefixWord, tailWord_8270841, baseEnd_8270841] using wordTrace_append hprefix tailTrace_8270841
  have hstable : (prefixWord ++ tailWord_8270841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270841).length < 2 ^ (prefixWord ++ tailWord_8270841).sum := by decide
  have hdescent : baseEnd_8270841 < baseStart_8270841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270860 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_8270860 : Nat := 118140960795 + 8270860 * 2 ^ 59
def prefixEnd_8270860 : Nat := 4983230072969 + 3 ^ 40 * 8270860 * 2
def baseEnd_8270860 : Nat := 4246926606045615455913013

theorem tailTrace_8270860 : CollatzResearch.WordTrace tailWord_8270860 prefixEnd_8270860 4246926606045615455913013 := by
  unfold tailWord_8270860
  simp only [CollatzResearch.WordTrace]
  refine ⟨150831523408047122637113017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201108697877396163516150689 150831523408047122637113017)
  ·
    refine ⟨113123642556035341977834763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150831523408047122637113017 113123642556035341977834763)
    ·
      refine ⟨169685463834053012966752145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113123642556035341977834763 169685463834053012966752145)
      ·
        refine ⟨127264097875539759725064109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169685463834053012966752145 127264097875539759725064109)
        ·
          refine ⟨47724036703327409896899041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127264097875539759725064109 47724036703327409896899041)
          ·
            refine ⟨35793027527495557422674281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47724036703327409896899041 35793027527495557422674281)
            ·
              refine ⟨26844770645621668067005711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35793027527495557422674281 26844770645621668067005711)
              ·
                refine ⟨40267155968432502100508567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26844770645621668067005711 40267155968432502100508567)
                ·
                  refine ⟨60400733952648753150762851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40267155968432502100508567 60400733952648753150762851)
                  ·
                    refine ⟨90601100928973129726144277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60400733952648753150762851 90601100928973129726144277)
                    ·
                      refine ⟨4246926606045615455913013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90601100928973129726144277 4246926606045615455913013)
                      ·
                        rfl

theorem cell23_8270860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_8270860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270860 prefixEnd_8270860 := by exact prefixLift 8270860
  have htrace : WordTrace (prefixWord ++ tailWord_8270860) baseStart_8270860 baseEnd_8270860 := by
    simpa [prefixWord, tailWord_8270860, baseEnd_8270860] using wordTrace_append hprefix tailTrace_8270860
  have hstable : (prefixWord ++ tailWord_8270860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270860).length < 2 ^ (prefixWord ++ tailWord_8270860).sum := by decide
  have hdescent : baseEnd_8270860 < baseStart_8270860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270863 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_8270863 : Nat := 118140960795 + 8270863 * 2 ^ 59
def prefixEnd_8270863 : Nat := 4983230072969 + 3 ^ 40 * 8270863 * 2
def baseEnd_8270863 : Nat := 4246928146487578944175499

theorem tailTrace_8270863 : CollatzResearch.WordTrace tailWord_8270863 prefixEnd_8270863 4246928146487578944175499 := by
  unfold tailWord_8270863
  simp only [CollatzResearch.WordTrace]
  refine ⟨301663156235083376786585243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201108770823388917857723495 301663156235083376786585243)
  ·
    refine ⟨452494734352625065179877865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301663156235083376786585243 452494734352625065179877865)
    ·
      refine ⟨339371050764468798884908399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452494734352625065179877865 339371050764468798884908399)
      ·
        refine ⟨509056576146703198327362599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339371050764468798884908399 509056576146703198327362599)
        ·
          refine ⟨763584864220054797491043899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509056576146703198327362599 763584864220054797491043899)
          ·
            refine ⟨1145377296330082196236565849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763584864220054797491043899 1145377296330082196236565849)
            ·
              refine ⟨859032972247561647177424387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145377296330082196236565849 859032972247561647177424387)
              ·
                refine ⟨1288549458371342470766136581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859032972247561647177424387 1288549458371342470766136581)
                ·
                  refine ⟨241603023444626713268650609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1288549458371342470766136581 241603023444626713268650609)
                  ·
                    refine ⟨181202267583470034951487957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241603023444626713268650609 181202267583470034951487957)
                    ·
                      refine ⟨4246928146487578944175499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181202267583470034951487957 4246928146487578944175499)
                      ·
                        rfl

theorem cell23_8270863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_8270863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270863 prefixEnd_8270863 := by exact prefixLift 8270863
  have htrace : WordTrace (prefixWord ++ tailWord_8270863) baseStart_8270863 baseEnd_8270863 := by
    simpa [prefixWord, tailWord_8270863, baseEnd_8270863] using wordTrace_append hprefix tailTrace_8270863
  have hstable : (prefixWord ++ tailWord_8270863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270863).length < 2 ^ (prefixWord ++ tailWord_8270863).sum := by decide
  have hdescent : baseEnd_8270863 < baseStart_8270863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270884 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_8270884 : Nat := 118140960795 + 8270884 * 2 ^ 59
def prefixEnd_8270884 : Nat := 4983230072969 + 3 ^ 40 * 8270884 * 2
def baseEnd_8270884 : Nat := 4246938929581323362012903

theorem tailTrace_8270884 : CollatzResearch.WordTrace tailWord_8270884 prefixEnd_8270884 4246938929581323362012903 := by
  unfold tailWord_8270884
  simp only [CollatzResearch.WordTrace]
  refine ⟨150831961084003648686549853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201109281445338198248733137 150831961084003648686549853)
  ·
    refine ⟨56561985406501368257456195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150831961084003648686549853 56561985406501368257456195)
    ·
      refine ⟨84842978109752052386184293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56561985406501368257456195 84842978109752052386184293)
      ·
        refine ⟨15908058395578509822409555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84842978109752052386184293 15908058395578509822409555)
        ·
          refine ⟨23862087593367764733614333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908058395578509822409555 23862087593367764733614333)
          ·
            refine ⟨8948282847512911775105375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23862087593367764733614333 8948282847512911775105375)
            ·
              refine ⟨13422424271269367662658063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948282847512911775105375 13422424271269367662658063)
              ·
                refine ⟨20133636406904051493987095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13422424271269367662658063 20133636406904051493987095)
                ·
                  refine ⟨30200454610356077240980643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20133636406904051493987095 30200454610356077240980643)
                  ·
                    refine ⟨45300681915534115861470965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30200454610356077240980643 45300681915534115861470965)
                    ·
                      refine ⟨4246938929581323362012903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45300681915534115861470965 4246938929581323362012903)
                      ·
                        rfl

theorem cell23_8270884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_8270884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270884 prefixEnd_8270884 := by exact prefixLift 8270884
  have htrace : WordTrace (prefixWord ++ tailWord_8270884) baseStart_8270884 baseEnd_8270884 := by
    simpa [prefixWord, tailWord_8270884, baseEnd_8270884] using wordTrace_append hprefix tailTrace_8270884
  have hstable : (prefixWord ++ tailWord_8270884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270884).length < 2 ^ (prefixWord ++ tailWord_8270884).sum := by decide
  have hdescent : baseEnd_8270884 < baseStart_8270884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270920 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_8270920 : Nat := 118140960795 + 8270920 * 2 ^ 59
def prefixEnd_8270920 : Nat := 4983230072969 + 3 ^ 40 * 8270920 * 2
def baseEnd_8270920 : Nat := 4246957414884885221162737

theorem tailTrace_8270920 : CollatzResearch.WordTrace tailWord_8270920 prefixEnd_8270920 4246957414884885221162737 := by
  unfold tailWord_8270920
  simp only [CollatzResearch.WordTrace]
  refine ⟨150832617597938437760705107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201110156797251250347606809 150832617597938437760705107)
  ·
    refine ⟨226248926396907656641057661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150832617597938437760705107 226248926396907656641057661)
    ·
      refine ⟨84843347398840371240396623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226248926396907656641057661 84843347398840371240396623)
      ·
        refine ⟨127265021098260556860594935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84843347398840371240396623 127265021098260556860594935)
        ·
          refine ⟨190897531647390835290892403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127265021098260556860594935 190897531647390835290892403)
          ·
            refine ⟨286346297471086252936338605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190897531647390835290892403 286346297471086252936338605)
            ·
              refine ⟨107379861551657344851126977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286346297471086252936338605 107379861551657344851126977)
              ·
                refine ⟨80534896163743008638345233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107379861551657344851126977 80534896163743008638345233)
                ·
                  refine ⟨60401172122807256478758925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80534896163743008638345233 60401172122807256478758925)
                  ·
                    refine ⟨22650439546052721179534597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60401172122807256478758925 22650439546052721179534597)
                    ·
                      refine ⟨4246957414884885221162737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22650439546052721179534597 4246957414884885221162737)
                      ·
                        rfl

theorem cell23_8270920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_8270920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270920 prefixEnd_8270920 := by exact prefixLift 8270920
  have htrace : WordTrace (prefixWord ++ tailWord_8270920) baseStart_8270920 baseEnd_8270920 := by
    simpa [prefixWord, tailWord_8270920, baseEnd_8270920] using wordTrace_append hprefix tailTrace_8270920
  have hstable : (prefixWord ++ tailWord_8270920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270920).length < 2 ^ (prefixWord ++ tailWord_8270920).sum := by decide
  have hdescent : baseEnd_8270920 < baseStart_8270920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270924 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_8270924 : Nat := 118140960795 + 8270924 * 2 ^ 59
def prefixEnd_8270924 : Nat := 4983230072969 + 3 ^ 40 * 8270924 * 2
def baseEnd_8270924 : Nat := 4246959468807503205512719

theorem tailTrace_8270924 : CollatzResearch.WordTrace tailWord_8270924 prefixEnd_8270924 4246959468807503205512719 := by
  unfold tailWord_8270924
  simp only [CollatzResearch.WordTrace]
  refine ⟨150832690543931192102277913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201110254058574922803037217 150832690543931192102277913)
  ·
    refine ⟨113124517907948394076708435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150832690543931192102277913 113124517907948394076708435)
    ·
      refine ⟨169686776861922591115062653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113124517907948394076708435 169686776861922591115062653)
      ·
        refine ⟨63632541323220971668148495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169686776861922591115062653 63632541323220971668148495)
        ·
          refine ⟨95448811984831457502222743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63632541323220971668148495 95448811984831457502222743)
          ·
            refine ⟨143173217977247186253334115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95448811984831457502222743 143173217977247186253334115)
            ·
              refine ⟨214759826965870779380001173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143173217977247186253334115 214759826965870779380001173)
              ·
                refine ⟨10066866889025192783437555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214759826965870779380001173 10066866889025192783437555)
                ·
                  refine ⟨15100300333537789175156333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066866889025192783437555 15100300333537789175156333)
                  ·
                    refine ⟨5662612625076670940683625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15100300333537789175156333 5662612625076670940683625)
                    ·
                      refine ⟨4246959468807503205512719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662612625076670940683625 4246959468807503205512719)
                      ·
                        rfl

theorem cell23_8270924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_8270924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270924 prefixEnd_8270924 := by exact prefixLift 8270924
  have htrace : WordTrace (prefixWord ++ tailWord_8270924) baseStart_8270924 baseEnd_8270924 := by
    simpa [prefixWord, tailWord_8270924, baseEnd_8270924] using wordTrace_append hprefix tailTrace_8270924
  have hstable : (prefixWord ++ tailWord_8270924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270924).length < 2 ^ (prefixWord ++ tailWord_8270924).sum := by decide
  have hdescent : baseEnd_8270924 < baseStart_8270924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270937 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 4, 2]
def baseStart_8270937 : Nat := 118140960795 + 8270937 * 2 ^ 59
def prefixEnd_8270937 : Nat := 4983230072969 + 3 ^ 40 * 8270937 * 2
def baseEnd_8270937 : Nat := 4246966144056011654650159

theorem tailTrace_8270937 : CollatzResearch.WordTrace tailWord_8270937 prefixEnd_8270937 4246966144056011654650159 := by
  unfold tailWord_8270937
  simp only [CollatzResearch.WordTrace]
  refine ⟨301665855236815287424779065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201110570157876858283186043 301665855236815287424779065)
  ·
    refine ⟨226249391427611465568584299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301665855236815287424779065 226249391427611465568584299)
    ·
      refine ⟨339374087141417198352876449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226249391427611465568584299 339374087141417198352876449)
      ·
        refine ⟨254530565356062898764657337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339374087141417198352876449 254530565356062898764657337)
        ·
          refine ⟨190897924017047174073493003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254530565356062898764657337 190897924017047174073493003)
          ·
            refine ⟨286346886025570761110239505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190897924017047174073493003 286346886025570761110239505)
            ·
              refine ⟨214760164519178070832679629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286346886025570761110239505 214760164519178070832679629)
              ·
                refine ⟨80535061694691776562254861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214760164519178070832679629 80535061694691776562254861)
                ·
                  refine ⟨30200648135509416210845573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80535061694691776562254861 30200648135509416210845573)
                  ·
                    refine ⟨5662621525408015539533545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30200648135509416210845573 5662621525408015539533545)
                    ·
                      refine ⟨4246966144056011654650159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662621525408015539533545 4246966144056011654650159)
                      ·
                        rfl

theorem cell23_8270937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_8270937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270937 prefixEnd_8270937 := by exact prefixLift 8270937
  have htrace : WordTrace (prefixWord ++ tailWord_8270937) baseStart_8270937 baseEnd_8270937 := by
    simpa [prefixWord, tailWord_8270937, baseEnd_8270937] using wordTrace_append hprefix tailTrace_8270937
  have hstable : (prefixWord ++ tailWord_8270937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270937).length < 2 ^ (prefixWord ++ tailWord_8270937).sum := by decide
  have hdescent : baseEnd_8270937 < baseStart_8270937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270965 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8270965 : Nat := 118140960795 + 8270965 * 2 ^ 59
def prefixEnd_8270965 : Nat := 4983230072969 + 3 ^ 40 * 8270965 * 2
def baseEnd_8270965 : Nat := 4246980521514337545100031

theorem tailTrace_8270965 : CollatzResearch.WordTrace tailWord_8270965 prefixEnd_8270965 4246980521514337545100031 := by
  unfold tailWord_8270965
  simp only [CollatzResearch.WordTrace]
  refine ⟨301666876480713848206798349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201111250987142565471198899 301666876480713848206798349)
  ·
    refine ⟨113125078680267693077549381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301666876480713848206798349 113125078680267693077549381)
    ·
      refine ⟨21210952252550192452040509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113125078680267693077549381 21210952252550192452040509)
      ·
        refine ⟨7954107094706322169515191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21210952252550192452040509 7954107094706322169515191)
        ·
          refine ⟨11931160642059483254272787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954107094706322169515191 11931160642059483254272787)
          ·
            refine ⟨17896740963089224881409181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931160642059483254272787 17896740963089224881409181)
            ·
              refine ⟨6711277861158459330528443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17896740963089224881409181 6711277861158459330528443)
              ·
                refine ⟨10066916791737688995792665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711277861158459330528443 10066916791737688995792665)
                ·
                  refine ⟨7550187593803266746844499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066916791737688995792665 7550187593803266746844499)
                  ·
                    refine ⟨11325281390704900120266749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550187593803266746844499 11325281390704900120266749)
                    ·
                      refine ⟨4246980521514337545100031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11325281390704900120266749 4246980521514337545100031)
                      ·
                        rfl

theorem cell23_8270965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8270965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270965 prefixEnd_8270965 := by exact prefixLift 8270965
  have htrace : WordTrace (prefixWord ++ tailWord_8270965) baseStart_8270965 baseEnd_8270965 := by
    simpa [prefixWord, tailWord_8270965, baseEnd_8270965] using wordTrace_append hprefix tailTrace_8270965
  have hstable : (prefixWord ++ tailWord_8270965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270965).length < 2 ^ (prefixWord ++ tailWord_8270965).sum := by decide
  have hdescent : baseEnd_8270965 < baseStart_8270965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8270977 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 7]
def baseStart_8270977 : Nat := 118140960795 + 8270977 * 2 ^ 59
def prefixEnd_8270977 : Nat := 4983230072969 + 3 ^ 40 * 8270977 * 2
def baseEnd_8270977 : Nat := 471887409253576833127775

theorem tailTrace_8270977 : CollatzResearch.WordTrace tailWord_8270977 prefixEnd_8270977 471887409253576833127775 := by
  unfold tailWord_8270977
  simp only [CollatzResearch.WordTrace]
  refine ⟨301667314156670374256235185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201111542771113582837490123 301667314156670374256235185)
  ·
    refine ⟨226250485617502780692176389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301667314156670374256235185 226250485617502780692176389)
    ·
      refine ⟨42421966053281771379783073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226250485617502780692176389 42421966053281771379783073)
      ·
        refine ⟨31816474539961328534837305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42421966053281771379783073 31816474539961328534837305)
        ·
          refine ⟨23862355904970996401127979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31816474539961328534837305 23862355904970996401127979)
          ·
            refine ⟨35793533857456494601691969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862355904970996401127979 35793533857456494601691969)
            ·
              refine ⟨26845150393092370951268977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35793533857456494601691969 26845150393092370951268977)
              ·
                refine ⟨20133862794819278213451733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26845150393092370951268977 20133862794819278213451733)
                ·
                  refine ⟨471887409253576833127775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20133862794819278213451733 471887409253576833127775)
                  ·
                    rfl

theorem cell23_8270977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_8270977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8270977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8270977 prefixEnd_8270977 := by exact prefixLift 8270977
  have htrace : WordTrace (prefixWord ++ tailWord_8270977) baseStart_8270977 baseEnd_8270977 := by
    simpa [prefixWord, tailWord_8270977, baseEnd_8270977] using wordTrace_append hprefix tailTrace_8270977
  have hstable : (prefixWord ++ tailWord_8270977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8270977).length < 2 ^ (prefixWord ++ tailWord_8270977).sum := by decide
  have hdescent : baseEnd_8270977 < baseStart_8270977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8270977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271020 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_8271020 : Nat := 118140960795 + 8271020 * 2 ^ 59
def prefixEnd_8271020 : Nat := 4983230072969 + 3 ^ 40 * 8271020 * 2
def baseEnd_8271020 : Nat := 1415669587650111609970759

theorem tailTrace_8271020 : CollatzResearch.WordTrace tailWord_8271020 prefixEnd_8271020 1415669587650111609970759 := by
  unfold tailWord_8271020
  simp only [CollatzResearch.WordTrace]
  refine ⟨150834441247757296300025257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201112588330343061733367009 150834441247757296300025257)
  ·
    refine ⟨113125830935817972225018943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150834441247757296300025257 113125830935817972225018943)
    ·
      refine ⟨169688746403726958337528415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113125830935817972225018943 169688746403726958337528415)
      ·
        refine ⟨254533119605590437506292623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169688746403726958337528415 254533119605590437506292623)
        ·
          refine ⟨381799679408385656259438935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254533119605590437506292623 381799679408385656259438935)
          ·
            refine ⟨572699519112578484389158403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381799679408385656259438935 572699519112578484389158403)
            ·
              refine ⟨859049278668867726583737605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572699519112578484389158403 859049278668867726583737605)
              ·
                refine ⟨161071739750412698734450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 859049278668867726583737605 161071739750412698734450801)
                ·
                  refine ⟨120803804812809524050838101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161071739750412698734450801 120803804812809524050838101)
                  ·
                    refine ⟨1415669587650111609970759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120803804812809524050838101 1415669587650111609970759)
                    ·
                      rfl

theorem cell23_8271020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_8271020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271020 prefixEnd_8271020 := by exact prefixLift 8271020
  have htrace : WordTrace (prefixWord ++ tailWord_8271020) baseStart_8271020 baseEnd_8271020 := by
    simpa [prefixWord, tailWord_8271020, baseEnd_8271020] using wordTrace_append hprefix tailTrace_8271020
  have hstable : (prefixWord ++ tailWord_8271020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271020).length < 2 ^ (prefixWord ++ tailWord_8271020).sum := by decide
  have hdescent : baseEnd_8271020 < baseStart_8271020 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271041 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_8271041 : Nat := 118140960795 + 8271041 * 2 ^ 59
def prefixEnd_8271041 : Nat := 4983230072969 + 3 ^ 40 * 8271041 * 2
def baseEnd_8271041 : Nat := 1415673182014693082583227

theorem tailTrace_8271041 : CollatzResearch.WordTrace tailWord_8271041 prefixEnd_8271041 1415673182014693082583227 := by
  unfold tailWord_8271041
  simp only [CollatzResearch.WordTrace]
  refine ⟨301669648428438513186564977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201113098952292342124376651 301669648428438513186564977)
  ·
    refine ⟨226252236321328884889923733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301669648428438513186564977 226252236321328884889923733)
    ·
      refine ⟨10605573577562291479215175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226252236321328884889923733 10605573577562291479215175)
      ·
        refine ⟨15908360366343437218822763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605573577562291479215175 15908360366343437218822763)
        ·
          refine ⟨23862540549515155828234145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908360366343437218822763 23862540549515155828234145)
          ·
            refine ⟨17896905412136366871175609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23862540549515155828234145 17896905412136366871175609)
            ·
              refine ⟨13422679059102275153381707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17896905412136366871175609 13422679059102275153381707)
              ·
                refine ⟨20134018588653412730072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13422679059102275153381707 20134018588653412730072561)
                ·
                  refine ⟨15100513941490059547554421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20134018588653412730072561 15100513941490059547554421)
                  ·
                    refine ⟨1415673182014693082583227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15100513941490059547554421 1415673182014693082583227)
                    ·
                      rfl

theorem cell23_8271041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_8271041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271041 prefixEnd_8271041 := by exact prefixLift 8271041
  have htrace : WordTrace (prefixWord ++ tailWord_8271041) baseStart_8271041 baseEnd_8271041 := by
    simpa [prefixWord, tailWord_8271041, baseEnd_8271041] using wordTrace_append hprefix tailTrace_8271041
  have hstable : (prefixWord ++ tailWord_8271041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271041).length < 2 ^ (prefixWord ++ tailWord_8271041).sum := by decide
  have hdescent : baseEnd_8271041 < baseStart_8271041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271047 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_8271047 : Nat := 118140960795 + 8271047 * 2 ^ 59
def prefixEnd_8271047 : Nat := 4983230072969 + 3 ^ 40 * 8271047 * 2
def baseEnd_8271047 : Nat := 4247022626928006224274653

theorem tailTrace_8271047 : CollatzResearch.WordTrace tailWord_8271047 prefixEnd_8271047 4247022626928006224274653 := by
  unfold tailWord_8271047
  simp only [CollatzResearch.WordTrace]
  refine ⟨301669867266416776211283395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201113244844277850807522263 301669867266416776211283395)
  ·
    refine ⟨452504800899625164316925093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301669867266416776211283395 452504800899625164316925093)
    ·
      refine ⟨84844650168679718309423455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452504800899625164316925093 84844650168679718309423455)
      ·
        refine ⟨127266975253019577464135183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84844650168679718309423455 127266975253019577464135183)
        ·
          refine ⟨190900462879529366196202775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127266975253019577464135183 190900462879529366196202775)
          ·
            refine ⟨286350694319294049294304163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190900462879529366196202775 286350694319294049294304163)
            ·
              refine ⟨429526041478941073941456245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286350694319294049294304163 429526041478941073941456245)
              ·
                refine ⟨40268066388650725682011523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429526041478941073941456245 40268066388650725682011523)
                ·
                  refine ⟨60402099582976088523017285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40268066388650725682011523 60402099582976088523017285)
                  ·
                    refine ⟨11325393671808016598065741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60402099582976088523017285 11325393671808016598065741)
                    ·
                      refine ⟨4247022626928006224274653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11325393671808016598065741 4247022626928006224274653)
                      ·
                        rfl

theorem cell23_8271047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_8271047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271047 prefixEnd_8271047 := by exact prefixLift 8271047
  have htrace : WordTrace (prefixWord ++ tailWord_8271047) baseStart_8271047 baseEnd_8271047 := by
    simpa [prefixWord, tailWord_8271047, baseEnd_8271047] using wordTrace_append hprefix tailTrace_8271047
  have hstable : (prefixWord ++ tailWord_8271047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271047).length < 2 ^ (prefixWord ++ tailWord_8271047).sum := by decide
  have hdescent : baseEnd_8271047 < baseStart_8271047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271062 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_8271062 : Nat := 118140960795 + 8271062 * 2 ^ 59
def prefixEnd_8271062 : Nat := 4983230072969 + 3 ^ 40 * 8271062 * 2
def baseEnd_8271062 : Nat := 471892258793091518398565

theorem tailTrace_8271062 : CollatzResearch.WordTrace tailWord_8271062 prefixEnd_8271062 471892258793091518398565 := by
  unfold tailWord_8271062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854400897585152110817465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201113609574241622515386293 18854400897585152110817465)
  ·
    refine ⟨14140800673188864083113099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18854400897585152110817465 14140800673188864083113099)
    ·
      refine ⟨21211201009783296124669649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14140800673188864083113099 21211201009783296124669649)
      ·
        refine ⟨15908400757337472093502237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21211201009783296124669649 15908400757337472093502237)
        ·
          refine ⟨5965650284001552035063339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15908400757337472093502237 5965650284001552035063339)
          ·
            refine ⟨8948475426002328052595009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965650284001552035063339 8948475426002328052595009)
            ·
              refine ⟨6711356569501746039446257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948475426002328052595009 6711356569501746039446257)
              ·
                refine ⟨5033517427126309529584693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711356569501746039446257 5033517427126309529584693)
                ·
                  refine ⟨471892258793091518398565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033517427126309529584693 471892258793091518398565)
                  ·
                    rfl

theorem cell23_8271062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_8271062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271062 prefixEnd_8271062 := by exact prefixLift 8271062
  have htrace : WordTrace (prefixWord ++ tailWord_8271062) baseStart_8271062 baseEnd_8271062 := by
    simpa [prefixWord, tailWord_8271062, baseEnd_8271062] using wordTrace_append hprefix tailTrace_8271062
  have hstable : (prefixWord ++ tailWord_8271062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271062).length < 2 ^ (prefixWord ++ tailWord_8271062).sum := by decide
  have hdescent : baseEnd_8271062 < baseStart_8271062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271092 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8271092 : Nat := 118140960795 + 8271092 * 2 ^ 59
def prefixEnd_8271092 : Nat := 4983230072969 + 3 ^ 40 * 8271092 * 2
def baseEnd_8271092 : Nat := 1415681911185819516070649

theorem tailTrace_8271092 : CollatzResearch.WordTrace tailWord_8271092 prefixEnd_8271092 1415681911185819516070649 := by
  unfold tailWord_8271092
  simp only [CollatzResearch.WordTrace]
  refine ⟨150835754275626874448335765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201114339034169165931114353 150835754275626874448335765)
  ·
    refine ⟨7070425981670009739765739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150835754275626874448335765 7070425981670009739765739)
    ·
      refine ⟨10605638972505014609648609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070425981670009739765739 10605638972505014609648609)
      ·
        refine ⟨7954229229378760957236457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605638972505014609648609 7954229229378760957236457)
        ·
          refine ⟨5965671922034070717927343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954229229378760957236457 5965671922034070717927343)
          ·
            refine ⟨8948507883051106076891015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965671922034070717927343 8948507883051106076891015)
            ·
              refine ⟨13422761824576659115336523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948507883051106076891015 13422761824576659115336523)
              ·
                refine ⟨20134142736864988673004785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13422761824576659115336523 20134142736864988673004785)
                ·
                  refine ⟨15100607052648741504753589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20134142736864988673004785 15100607052648741504753589)
                  ·
                    refine ⟨1415681911185819516070649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15100607052648741504753589 1415681911185819516070649)
                    ·
                      rfl

theorem cell23_8271092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8271092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271092 prefixEnd_8271092 := by exact prefixLift 8271092
  have htrace : WordTrace (prefixWord ++ tailWord_8271092) baseStart_8271092 baseEnd_8271092 := by
    simpa [prefixWord, tailWord_8271092, baseEnd_8271092] using wordTrace_append hprefix tailTrace_8271092
  have hstable : (prefixWord ++ tailWord_8271092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271092).length < 2 ^ (prefixWord ++ tailWord_8271092).sum := by decide
  have hdescent : baseEnd_8271092 < baseStart_8271092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271097 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_8271097 : Nat := 118140960795 + 8271097 * 2 ^ 59
def prefixEnd_8271097 : Nat := 4983230072969 + 3 ^ 40 * 8271097 * 2
def baseEnd_8271097 : Nat := 1415682766986910342883141

theorem tailTrace_8271097 : CollatzResearch.WordTrace tailWord_8271097 prefixEnd_8271097 1415682766986910342883141 := by
  unfold tailWord_8271097
  simp only [CollatzResearch.WordTrace]
  refine ⟨301671690916235634750603545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201114460610823756500402363 301671690916235634750603545)
  ·
    refine ⟨226253768187176726062952659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301671690916235634750603545 226253768187176726062952659)
    ·
      refine ⟨339380652280765089094428989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226253768187176726062952659 339380652280765089094428989)
      ·
        refine ⟨127267744605286908410410871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339380652280765089094428989 127267744605286908410410871)
        ·
          refine ⟨190901616907930362615616307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127267744605286908410410871 190901616907930362615616307)
          ·
            refine ⟨286352425361895543923424461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190901616907930362615616307 286352425361895543923424461)
            ·
              refine ⟨107382159510710828971284173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286352425361895543923424461 107382159510710828971284173)
              ·
                refine ⟨40268309816516560864231565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107382159510710828971284173 40268309816516560864231565)
                ·
                  refine ⟨15100616181193710324086837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40268309816516560864231565 15100616181193710324086837)
                  ·
                    refine ⟨1415682766986910342883141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15100616181193710324086837 1415682766986910342883141)
                    ·
                      rfl

theorem cell23_8271097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_8271097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271097 prefixEnd_8271097 := by exact prefixLift 8271097
  have htrace : WordTrace (prefixWord ++ tailWord_8271097) baseStart_8271097 baseEnd_8271097 := by
    simpa [prefixWord, tailWord_8271097, baseEnd_8271097] using wordTrace_append hprefix tailTrace_8271097
  have hstable : (prefixWord ++ tailWord_8271097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271097).length < 2 ^ (prefixWord ++ tailWord_8271097).sum := by decide
  have hdescent : baseEnd_8271097 < baseStart_8271097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271128 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_8271128 : Nat := 118140960795 + 8271128 * 2 ^ 59
def prefixEnd_8271128 : Nat := 4983230072969 + 3 ^ 40 * 8271128 * 2
def baseEnd_8271128 : Nat := 4247064218861020407361781

theorem tailTrace_8271128 : CollatzResearch.WordTrace tailWord_8271128 prefixEnd_8271128 4247064218861020407361781 := by
  unfold tailWord_8271128
  simp only [CollatzResearch.WordTrace]
  refine ⟨150836410789561663522491019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201115214386082218029988025 150836410789561663522491019)
  ·
    refine ⟨226254616184342495283736529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150836410789561663522491019 226254616184342495283736529)
    ·
      refine ⟨169690962138256871462802397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226254616184342495283736529 169690962138256871462802397)
      ·
        refine ⟨63634110801846326798550899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169690962138256871462802397 63634110801846326798550899)
        ·
          refine ⟨95451166202769490197826349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63634110801846326798550899 95451166202769490197826349)
          ·
            refine ⟨35794187326038558824184881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95451166202769490197826349 35794187326038558824184881)
            ·
              refine ⟨26845640494528919118138661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35794187326038558824184881 26845640494528919118138661)
              ·
                refine ⟨5033557592724172334650999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26845640494528919118138661 5033557592724172334650999)
                ·
                  refine ⟨7550336389086258501976499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033557592724172334650999 7550336389086258501976499)
                  ·
                    refine ⟨11325504583629387752964749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550336389086258501976499 11325504583629387752964749)
                    ·
                      refine ⟨4247064218861020407361781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11325504583629387752964749 4247064218861020407361781)
                      ·
                        rfl

theorem cell23_8271128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_8271128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271128 prefixEnd_8271128 := by exact prefixLift 8271128
  have htrace : WordTrace (prefixWord ++ tailWord_8271128) baseStart_8271128 baseEnd_8271128 := by
    simpa [prefixWord, tailWord_8271128, baseEnd_8271128] using wordTrace_append hprefix tailTrace_8271128
  have hstable : (prefixWord ++ tailWord_8271128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271128).length < 2 ^ (prefixWord ++ tailWord_8271128).sum := by decide
  have hdescent : baseEnd_8271128 < baseStart_8271128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271147 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_8271147 : Nat := 118140960795 + 8271147 * 2 ^ 59
def prefixEnd_8271147 : Nat := 4983230072969 + 3 ^ 40 * 8271147 * 2
def baseEnd_8271147 : Nat := 4247073974993455833024193

theorem tailTrace_8271147 : CollatzResearch.WordTrace tailWord_8271147 prefixEnd_8271147 4247073974993455833024193 := by
  unfold tailWord_8271147
  simp only [CollatzResearch.WordTrace]
  refine ⟨301673514566054493289923695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201115676377369662193282463 301673514566054493289923695)
  ·
    refine ⟨452510271849081739934885543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301673514566054493289923695 452510271849081739934885543)
    ·
      refine ⟨678765407773622609902328315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452510271849081739934885543 678765407773622609902328315)
      ·
        refine ⟨1018148111660433914853492473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678765407773622609902328315 1018148111660433914853492473)
        ·
          refine ⟨763611083745325436140119355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018148111660433914853492473 763611083745325436140119355)
          ·
            refine ⟨1145416625617988154210179033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763611083745325436140119355 1145416625617988154210179033)
            ·
              refine ⟨859062469213491115657634275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145416625617988154210179033 859062469213491115657634275)
              ·
                refine ⟨1288593703820236673486451413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859062469213491115657634275 1288593703820236673486451413)
                ·
                  refine ⟨30201414933286797034838705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1288593703820236673486451413 30201414933286797034838705)
                  ·
                    refine ⟨22651061199965097776129029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30201414933286797034838705 22651061199965097776129029)
                    ·
                      refine ⟨4247073974993455833024193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22651061199965097776129029 4247073974993455833024193)
                      ·
                        rfl

theorem cell23_8271147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_8271147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271147 prefixEnd_8271147 := by exact prefixLift 8271147
  have htrace : WordTrace (prefixWord ++ tailWord_8271147) baseStart_8271147 baseEnd_8271147 := by
    simpa [prefixWord, tailWord_8271147, baseEnd_8271147] using wordTrace_append hprefix tailTrace_8271147
  have hstable : (prefixWord ++ tailWord_8271147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271147).length < 2 ^ (prefixWord ++ tailWord_8271147).sum := by decide
  have hdescent : baseEnd_8271147 < baseStart_8271147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271187 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 7]
def baseStart_8271187 : Nat := 118140960795 + 8271187 * 2 ^ 59
def prefixEnd_8271187 : Nat := 4983230072969 + 3 ^ 40 * 8271187 * 2
def baseEnd_8271187 : Nat := 1415698171406545225508003

theorem tailTrace_8271187 : CollatzResearch.WordTrace tailWord_8271187 prefixEnd_8271187 1415698171406545225508003 := by
  unfold tailWord_8271187
  simp only [CollatzResearch.WordTrace]
  refine ⟨301674973485909580121379815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201116648990606386747586543 301674973485909580121379815)
  ·
    refine ⟨452512460228864370182069723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301674973485909580121379815 452512460228864370182069723)
    ·
      refine ⟨678768690343296555273104585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452512460228864370182069723 678768690343296555273104585)
      ·
        refine ⟨509076517757472416454828439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678768690343296555273104585 509076517757472416454828439)
        ·
          refine ⟨763614776636208624682242659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509076517757472416454828439 763614776636208624682242659)
          ·
            refine ⟨1145422164954312937023363989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763614776636208624682242659 1145422164954312937023363989)
            ·
              refine ⟨53691663982233418922970187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1145422164954312937023363989 53691663982233418922970187)
              ·
                refine ⟨80537495973350128384455281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53691663982233418922970187 80537495973350128384455281)
                ·
                  refine ⟨60403121980012596288341461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80537495973350128384455281 60403121980012596288341461)
                  ·
                    refine ⟨1415698171406545225508003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60403121980012596288341461 1415698171406545225508003)
                    ·
                      rfl

theorem cell23_8271187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_8271187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271187 prefixEnd_8271187 := by exact prefixLift 8271187
  have htrace : WordTrace (prefixWord ++ tailWord_8271187) baseStart_8271187 baseEnd_8271187 := by
    simpa [prefixWord, tailWord_8271187, baseEnd_8271187] using wordTrace_append hprefix tailTrace_8271187
  have hstable : (prefixWord ++ tailWord_8271187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271187).length < 2 ^ (prefixWord ++ tailWord_8271187).sum := by decide
  have hdescent : baseEnd_8271187 < baseStart_8271187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271244 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_8271244 : Nat := 118140960795 + 8271244 * 2 ^ 59
def prefixEnd_8271244 : Nat := 4983230072969 + 3 ^ 40 * 8271244 * 2
def baseEnd_8271244 : Nat := 4247123782616941953511247

theorem tailTrace_8271244 : CollatzResearch.WordTrace tailWord_8271244 prefixEnd_8271244 4247123782616941953511247 := by
  unfold tailWord_8271244
  simp only [CollatzResearch.WordTrace]
  refine ⟨150838526223351539428102393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201118034964468719237469857 150838526223351539428102393)
  ·
    refine ⟨113128894667513654571076795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150838526223351539428102393 113128894667513654571076795)
    ·
      refine ⟨169693342001270481856615193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113128894667513654571076795 169693342001270481856615193)
      ·
        refine ⟨127270006500952861392461395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169693342001270481856615193 127270006500952861392461395)
        ·
          refine ⟨190905009751429292088692093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127270006500952861392461395 190905009751429292088692093)
          ·
            refine ⟨71589378656785984533259535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190905009751429292088692093 71589378656785984533259535)
            ·
              refine ⟨107384067985178976799889303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71589378656785984533259535 107384067985178976799889303)
              ·
                refine ⟨161076101977768465199833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107384067985178976799889303 161076101977768465199833955)
                ·
                  refine ⟨241614152966652697799750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161076101977768465199833955 241614152966652697799750933)
                  ·
                    refine ⟨11325663420311845209363325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241614152966652697799750933 11325663420311845209363325)
                    ·
                      refine ⟨4247123782616941953511247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11325663420311845209363325 4247123782616941953511247)
                      ·
                        rfl

theorem cell23_8271244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_8271244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271244 prefixEnd_8271244 := by exact prefixLift 8271244
  have htrace : WordTrace (prefixWord ++ tailWord_8271244) baseStart_8271244 baseEnd_8271244 := by
    simpa [prefixWord, tailWord_8271244, baseEnd_8271244] using wordTrace_append hprefix tailTrace_8271244
  have hstable : (prefixWord ++ tailWord_8271244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271244).length < 2 ^ (prefixWord ++ tailWord_8271244).sum := by decide
  have hdescent : baseEnd_8271244 < baseStart_8271244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271258 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_8271258 : Nat := 118140960795 + 8271258 * 2 ^ 59
def prefixEnd_8271258 : Nat := 4983230072969 + 3 ^ 40 * 8271258 * 2
def baseEnd_8271258 : Nat := 4247130971346104898736183

theorem tailTrace_8271258 : CollatzResearch.WordTrace tailWord_8271258 prefixEnd_8271258 4247130971346104898736183 := by
  unfold tailWord_8271258
  simp only [CollatzResearch.WordTrace]
  refine ⟨75419390767163089811803607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201118375379101572831476285 75419390767163089811803607)
  ·
    refine ⟨113129086150744634717705411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75419390767163089811803607 113129086150744634717705411)
    ·
      refine ⟨169693629226116952076558117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113129086150744634717705411 169693629226116952076558117)
      ·
        refine ⟨31817555479896928514354647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169693629226116952076558117 31817555479896928514354647)
        ·
          refine ⟨47726333219845392771531971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31817555479896928514354647 47726333219845392771531971)
          ·
            refine ⟨71589499829768089157297957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47726333219845392771531971 71589499829768089157297957)
            ·
              refine ⟨13423031218081516716993367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71589499829768089157297957 13423031218081516716993367)
              ·
                refine ⟨20134546827122275075490051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423031218081516716993367 20134546827122275075490051)
                ·
                  refine ⟨30201820240683412613235077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20134546827122275075490051 30201820240683412613235077)
                  ·
                    refine ⟨5662841295128139864981577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30201820240683412613235077 5662841295128139864981577)
                    ·
                      refine ⟨4247130971346104898736183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662841295128139864981577 4247130971346104898736183)
                      ·
                        rfl

theorem cell23_8271258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_8271258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271258 prefixEnd_8271258 := by exact prefixLift 8271258
  have htrace : WordTrace (prefixWord ++ tailWord_8271258) baseStart_8271258 baseEnd_8271258 := by
    simpa [prefixWord, tailWord_8271258, baseEnd_8271258] using wordTrace_append hprefix tailTrace_8271258
  have hstable : (prefixWord ++ tailWord_8271258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271258).length < 2 ^ (prefixWord ++ tailWord_8271258).sum := by decide
  have hdescent : baseEnd_8271258 < baseStart_8271258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271264 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 7]
def baseStart_8271264 : Nat := 118140960795 + 8271264 * 2 ^ 59
def prefixEnd_8271264 : Nat := 4983230072969 + 3 ^ 40 * 8271264 * 2
def baseEnd_8271264 : Nat := 471903783581114652806795

theorem tailTrace_8271264 : CollatzResearch.WordTrace tailWord_8271264 prefixEnd_8271264 471903783581114652806795 := by
  unfold tailWord_8271264
  simp only [CollatzResearch.WordTrace]
  refine ⟨150838890953315311135966423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201118521271087081514621897 150838890953315311135966423)
  ·
    refine ⟨226258336429972966703949635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150838890953315311135966423 226258336429972966703949635)
    ·
      refine ⟨339387504644959450055924453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226258336429972966703949635 339387504644959450055924453)
      ·
        refine ⟨63635157120929896885485835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339387504644959450055924453 63635157120929896885485835)
        ·
          refine ⟨95452735681394845328228753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63635157120929896885485835 95452735681394845328228753)
          ·
            refine ⟨71589551761046133996171565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95452735681394845328228753 71589551761046133996171565)
            ·
              refine ⟨26846081910392300248564337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71589551761046133996171565 26846081910392300248564337)
              ·
                refine ⟨20134561432794225186423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26846081910392300248564337 20134561432794225186423253)
                ·
                  refine ⟨471903783581114652806795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20134561432794225186423253 471903783581114652806795)
                  ·
                    rfl

theorem cell23_8271264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_8271264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271264 prefixEnd_8271264 := by exact prefixLift 8271264
  have htrace : WordTrace (prefixWord ++ tailWord_8271264) baseStart_8271264 baseEnd_8271264 := by
    simpa [prefixWord, tailWord_8271264, baseEnd_8271264] using wordTrace_append hprefix tailTrace_8271264
  have hstable : (prefixWord ++ tailWord_8271264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271264).length < 2 ^ (prefixWord ++ tailWord_8271264).sum := by decide
  have hdescent : baseEnd_8271264 < baseStart_8271264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271304 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_8271304 : Nat := 118140960795 + 8271304 * 2 ^ 59
def prefixEnd_8271304 : Nat := 4983230072969 + 3 ^ 40 * 8271304 * 2
def baseEnd_8271304 : Nat := 4247154591456211718760971

theorem tailTrace_8271304 : CollatzResearch.WordTrace tailWord_8271304 prefixEnd_8271304 4247154591456211718760971 := by
  unfold tailWord_8271304
  simp only [CollatzResearch.WordTrace]
  refine ⟨150839620413242854551694483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201119493884323806068925977 150839620413242854551694483)
  ·
    refine ⟨226259430619864281827541725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150839620413242854551694483 226259430619864281827541725)
    ·
      refine ⟨84847286482449105685328147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226259430619864281827541725 84847286482449105685328147)
      ·
        refine ⟨127270929723673658527992221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84847286482449105685328147 127270929723673658527992221)
        ·
          refine ⟨47726598646377621947997083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127270929723673658527992221 47726598646377621947997083)
          ·
            refine ⟨71589897969566432921995625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47726598646377621947997083 71589897969566432921995625)
            ·
              refine ⟨53692423477174824691496719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71589897969566432921995625 53692423477174824691496719)
              ·
                refine ⟨80538635215762237037245079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53692423477174824691496719 80538635215762237037245079)
                ·
                  refine ⟨120807952823643355555867619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80538635215762237037245079 120807952823643355555867619)
                  ·
                    refine ⟨181211929235465033333801429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120807952823643355555867619 181211929235465033333801429)
                    ·
                      refine ⟨4247154591456211718760971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181211929235465033333801429 4247154591456211718760971)
                      ·
                        rfl

theorem cell23_8271304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_8271304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271304 prefixEnd_8271304 := by exact prefixLift 8271304
  have htrace : WordTrace (prefixWord ++ tailWord_8271304) baseStart_8271304 baseEnd_8271304 := by
    simpa [prefixWord, tailWord_8271304, baseEnd_8271304] using wordTrace_append hprefix tailTrace_8271304
  have hstable : (prefixWord ++ tailWord_8271304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271304).length < 2 ^ (prefixWord ++ tailWord_8271304).sum := by decide
  have hdescent : baseEnd_8271304 < baseStart_8271304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271331 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8271331 : Nat := 118140960795 + 8271331 * 2 ^ 59
def prefixEnd_8271331 : Nat := 4983230072969 + 3 ^ 40 * 8271331 * 2
def baseEnd_8271331 : Nat := 4247168455433883113123347

theorem tailTrace_8271331 : CollatzResearch.WordTrace tailWord_8271331 prefixEnd_8271331 4247168455433883113123347 := by
  unfold tailWord_8271331
  simp only [CollatzResearch.WordTrace]
  refine ⟨301680225597387892714621847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201120150398258595143081231 301680225597387892714621847)
  ·
    refine ⟨452520338396081839071932771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301680225597387892714621847 452520338396081839071932771)
    ·
      refine ⟨678780507594122758607899157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452520338396081839071932771 678780507594122758607899157)
      ·
        refine ⟨31817836293474504309745273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 678780507594122758607899157 31817836293474504309745273)
        ·
          refine ⟨23863377220105878232308955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31817836293474504309745273 23863377220105878232308955)
          ·
            refine ⟨35795065830158817348463433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23863377220105878232308955 35795065830158817348463433)
            ·
              refine ⟨26846299372619113011347575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35795065830158817348463433 26846299372619113011347575)
              ·
                refine ⟨40269449058928669517021363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26846299372619113011347575 40269449058928669517021363)
                ·
                  refine ⟨60404173588393004275532045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40269449058928669517021363 60404173588393004275532045)
                  ·
                    refine ⟨22651565095647376603324517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60404173588393004275532045 22651565095647376603324517)
                    ·
                      refine ⟨4247168455433883113123347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22651565095647376603324517 4247168455433883113123347)
                      ·
                        rfl

theorem cell23_8271331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8271331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271331 prefixEnd_8271331 := by exact prefixLift 8271331
  have htrace : WordTrace (prefixWord ++ tailWord_8271331) baseStart_8271331 baseEnd_8271331 := by
    simpa [prefixWord, tailWord_8271331, baseEnd_8271331] using wordTrace_append hprefix tailTrace_8271331
  have hstable : (prefixWord ++ tailWord_8271331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271331).length < 2 ^ (prefixWord ++ tailWord_8271331).sum := by decide
  have hdescent : baseEnd_8271331 < baseStart_8271331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271354 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 8]
def baseStart_8271354 : Nat := 118140960795 + 8271354 * 2 ^ 59
def prefixEnd_8271354 : Nat := 4983230072969 + 3 ^ 40 * 8271354 * 2
def baseEnd_8271354 : Nat := 471908918387659613681749

theorem tailTrace_8271354 : CollatzResearch.WordTrace tailWord_8271354 prefixEnd_8271354 471908918387659613681749 := by
  unfold tailWord_8271354
  simp only [CollatzResearch.WordTrace]
  refine ⟨75420266119076141910677279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201120709650869711761806077 75420266119076141910677279)
  ·
    refine ⟨113130399178614212866015919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75420266119076141910677279 113130399178614212866015919)
    ·
      refine ⟨169695598767921319299023879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113130399178614212866015919 169695598767921319299023879)
      ·
        refine ⟨254543398151881978948535819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169695598767921319299023879 254543398151881978948535819)
        ·
          refine ⟨381815097227822968422803729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254543398151881978948535819 381815097227822968422803729)
          ·
            refine ⟨286361322920867226317102797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381815097227822968422803729 286361322920867226317102797)
            ·
              refine ⟨107385496095325209868913549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286361322920867226317102797 107385496095325209868913549)
              ·
                refine ⟨40269561035746953700842581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107385496095325209868913549 40269561035746953700842581)
                ·
                  refine ⟨471908918387659613681749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40269561035746953700842581 471908918387659613681749)
                  ·
                    rfl

theorem cell23_8271354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_8271354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271354 prefixEnd_8271354 := by exact prefixLift 8271354
  have htrace : WordTrace (prefixWord ++ tailWord_8271354) baseStart_8271354 baseEnd_8271354 := by
    simpa [prefixWord, tailWord_8271354, baseEnd_8271354] using wordTrace_append hprefix tailTrace_8271354
  have hstable : (prefixWord ++ tailWord_8271354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271354).length < 2 ^ (prefixWord ++ tailWord_8271354).sum := by decide
  have hdescent : baseEnd_8271354 < baseStart_8271354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_8271438 : Nat := 118140960795 + 8271438 * 2 ^ 59
def prefixEnd_8271438 : Nat := 4983230072969 + 3 ^ 40 * 8271438 * 2
def baseEnd_8271438 : Nat := 4247223397863914194485355

theorem tailTrace_8271438 : CollatzResearch.WordTrace tailWord_8271438 prefixEnd_8271438 4247223397863914194485355 := by
  unfold tailWord_8271438
  simp only [CollatzResearch.WordTrace]
  refine ⟨37710516026000031248595871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201122752138666833325844645 37710516026000031248595871)
  ·
    refine ⟨56565774039000046872893807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37710516026000031248595871 56565774039000046872893807)
    ·
      refine ⟨84848661058500070309340711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56565774039000046872893807 84848661058500070309340711)
      ·
        refine ⟨127272991587750105464011067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84848661058500070309340711 127272991587750105464011067)
        ·
          refine ⟨190909487381625158196016601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127272991587750105464011067 190909487381625158196016601)
          ·
            refine ⟨143182115536218868647012451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190909487381625158196016601 143182115536218868647012451)
            ·
              refine ⟨214773173304328302970518677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143182115536218868647012451 214773173304328302970518677)
              ·
                refine ⟨10067492498640389201743063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214773173304328302970518677 10067492498640389201743063)
                ·
                  refine ⟨15101238747960583802614595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067492498640389201743063 15101238747960583802614595)
                  ·
                    refine ⟨22651858121940875703921893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15101238747960583802614595 22651858121940875703921893)
                    ·
                      refine ⟨4247223397863914194485355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22651858121940875703921893 4247223397863914194485355)
                      ·
                        rfl

theorem cell23_8271438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_8271438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271438 prefixEnd_8271438 := by exact prefixLift 8271438
  have htrace : WordTrace (prefixWord ++ tailWord_8271438) baseStart_8271438 baseEnd_8271438 := by
    simpa [prefixWord, tailWord_8271438, baseEnd_8271438] using wordTrace_append hprefix tailTrace_8271438
  have hstable : (prefixWord ++ tailWord_8271438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271438).length < 2 ^ (prefixWord ++ tailWord_8271438).sum := by decide
  have hdescent : baseEnd_8271438 < baseStart_8271438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271442 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_8271442 : Nat := 118140960795 + 8271442 * 2 ^ 59
def prefixEnd_8271442 : Nat := 4983230072969 + 3 ^ 40 * 8271442 * 2
def baseEnd_8271442 : Nat := 4247225451786532178835337

theorem tailTrace_8271442 : CollatzResearch.WordTrace tailWord_8271442 prefixEnd_8271442 4247225451786532178835337 := by
  unfold tailWord_8271442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75421068524996439667978145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201122849399990505781275053 75421068524996439667978145)
  ·
    refine ⟨56565801393747329750983609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75421068524996439667978145 56565801393747329750983609)
    ·
      refine ⟨42424351045310497313237707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56565801393747329750983609 42424351045310497313237707)
      ·
        refine ⟨63636526567965745969856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424351045310497313237707 63636526567965745969856561)
        ·
          refine ⟨47727394925974309477392421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63636526567965745969856561 47727394925974309477392421)
          ·
            refine ⟨8948886548620183027011079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47727394925974309477392421 8948886548620183027011079)
            ·
              refine ⟨13423329822930274540516619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948886548620183027011079 13423329822930274540516619)
              ·
                refine ⟨20134994734395411810774929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423329822930274540516619 20134994734395411810774929)
                ·
                  refine ⟨15101246050796558858081197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20134994734395411810774929 15101246050796558858081197)
                  ·
                    refine ⟨5662967269048709571780449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15101246050796558858081197 5662967269048709571780449)
                    ·
                      refine ⟨4247225451786532178835337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662967269048709571780449 4247225451786532178835337)
                      ·
                        rfl

theorem cell23_8271442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_8271442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271442 prefixEnd_8271442 := by exact prefixLift 8271442
  have htrace : WordTrace (prefixWord ++ tailWord_8271442) baseStart_8271442 baseEnd_8271442 := by
    simpa [prefixWord, tailWord_8271442, baseEnd_8271442] using wordTrace_append hprefix tailTrace_8271442
  have hstable : (prefixWord ++ tailWord_8271442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271442).length < 2 ^ (prefixWord ++ tailWord_8271442).sum := by decide
  have hdescent : baseEnd_8271442 < baseStart_8271442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271452 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_8271452 : Nat := 118140960795 + 8271452 * 2 ^ 59
def prefixEnd_8271452 : Nat := 4983230072969 + 3 ^ 40 * 8271452 * 2
def baseEnd_8271452 : Nat := 1415743528864359046570097

theorem tailTrace_8271452 : CollatzResearch.WordTrace tailWord_8271452 prefixEnd_8271452 1415743528864359046570097 := by
  unfold tailWord_8271452
  simp only [CollatzResearch.WordTrace]
  refine ⟨150842319414974765189888305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201123092553299686919851073 150842319414974765189888305)
  ·
    refine ⟨113131739561231073892416229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150842319414974765189888305 113131739561231073892416229)
    ·
      refine ⟨21212201167730826354828043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113131739561231073892416229 21212201167730826354828043)
      ·
        refine ⟨31818301751596239532242065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21212201167730826354828043 31818301751596239532242065)
        ·
          refine ⟨23863726313697179649181549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31818301751596239532242065 23863726313697179649181549)
          ·
            refine ⟨8948897367636442368443081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23863726313697179649181549 8948897367636442368443081)
            ·
              refine ⟨6711673025727331776332311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948897367636442368443081 6711673025727331776332311)
              ·
                refine ⟨10067509538590997664498467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711673025727331776332311 10067509538590997664498467)
                ·
                  refine ⟨15101264307886496496747701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067509538590997664498467 15101264307886496496747701)
                  ·
                    refine ⟨1415743528864359046570097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15101264307886496496747701 1415743528864359046570097)
                    ·
                      rfl

theorem cell23_8271452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_8271452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271452 prefixEnd_8271452 := by exact prefixLift 8271452
  have htrace : WordTrace (prefixWord ++ tailWord_8271452) baseStart_8271452 baseEnd_8271452 := by
    simpa [prefixWord, tailWord_8271452, baseEnd_8271452] using wordTrace_append hprefix tailTrace_8271452
  have hstable : (prefixWord ++ tailWord_8271452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271452).length < 2 ^ (prefixWord ++ tailWord_8271452).sum := by decide
  have hdescent : baseEnd_8271452 < baseStart_8271452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271461 : List Nat := [1, 3, 1, 3, 3, 2, 10]
def baseStart_8271461 : Nat := 118140960795 + 8271461 * 2 ^ 59
def prefixEnd_8271461 : Nat := 4983230072969 + 3 ^ 40 * 8271461 * 2
def baseEnd_8271461 : Nat := 52435002566900834623429

theorem tailTrace_8271461 : CollatzResearch.WordTrace tailWord_8271461 prefixEnd_8271461 52435002566900834623429 := by
  unfold tailWord_8271461
  simp only [CollatzResearch.WordTrace]
  refine ⟨301684967086916924916854237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201123311391277949944569491 301684967086916924916854237)
  ·
    refine ⟨113131862657593846843820339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301684967086916924916854237 113131862657593846843820339)
    ·
      refine ⟨169697793986390770265730509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113131862657593846843820339 169697793986390770265730509)
      ·
        refine ⟨63636672744896538849648941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169697793986390770265730509 63636672744896538849648941)
        ·
          refine ⟨23863752279336202068618353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63636672744896538849648941 23863752279336202068618353)
          ·
            refine ⟨17897814209502151551463765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23863752279336202068618353 17897814209502151551463765)
            ·
              refine ⟨52435002566900834623429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17897814209502151551463765 52435002566900834623429)
              ·
                rfl

theorem cell23_8271461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 10].length) (baseStart_8271461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271461 prefixEnd_8271461 := by exact prefixLift 8271461
  have htrace : WordTrace (prefixWord ++ tailWord_8271461) baseStart_8271461 baseEnd_8271461 := by
    simpa [prefixWord, tailWord_8271461, baseEnd_8271461] using wordTrace_append hprefix tailTrace_8271461
  have hstable : (prefixWord ++ tailWord_8271461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271461).length < 2 ^ (prefixWord ++ tailWord_8271461).sum := by decide
  have hdescent : baseEnd_8271461 < baseStart_8271461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271472 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2]
def baseStart_8271472 : Nat := 118140960795 + 8271472 * 2 ^ 59
def prefixEnd_8271472 : Nat := 4983230072969 + 3 ^ 40 * 8271472 * 2
def baseEnd_8271472 : Nat := 4247240856206167061460199

theorem tailTrace_8271472 : CollatzResearch.WordTrace tailWord_8271472 prefixEnd_8271472 4247240856206167061460199 := by
  unfold tailWord_8271472
  simp only [CollatzResearch.WordTrace]
  refine ⟨150842684144938536897752335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201123578859918049197003113 150842684144938536897752335)
  ·
    refine ⟨226264026217407805346628503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150842684144938536897752335 226264026217407805346628503)
    ·
      refine ⟨339396039326111708019942755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226264026217407805346628503 339396039326111708019942755)
      ·
        refine ⟨509094058989167562029914133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339396039326111708019942755 509094058989167562029914133)
        ·
          refine ⟨23863784015117229470152225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 509094058989167562029914133 23863784015117229470152225)
          ·
            refine ⟨17897838011337922102614169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23863784015117229470152225 17897838011337922102614169)
            ·
              refine ⟨13423378508503441576960627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17897838011337922102614169 13423378508503441576960627)
              ·
                refine ⟨20135067762755162365440941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423378508503441576960627 20135067762755162365440941)
                ·
                  refine ⟨7550650411033185887040353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20135067762755162365440941 7550650411033185887040353)
                  ·
                    refine ⟨5662987808274889415280265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7550650411033185887040353 5662987808274889415280265)
                    ·
                      refine ⟨4247240856206167061460199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5662987808274889415280265 4247240856206167061460199)
                      ·
                        rfl

theorem cell23_8271472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 2, 2].length) (baseStart_8271472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271472 prefixEnd_8271472 := by exact prefixLift 8271472
  have htrace : WordTrace (prefixWord ++ tailWord_8271472) baseStart_8271472 baseEnd_8271472 := by
    simpa [prefixWord, tailWord_8271472, baseEnd_8271472] using wordTrace_append hprefix tailTrace_8271472
  have hstable : (prefixWord ++ tailWord_8271472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271472).length < 2 ^ (prefixWord ++ tailWord_8271472).sum := by decide
  have hdescent : baseEnd_8271472 < baseStart_8271472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271485 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_8271485 : Nat := 118140960795 + 8271485 * 2 ^ 59
def prefixEnd_8271485 : Nat := 4983230072969 + 3 ^ 40 * 8271485 * 2
def baseEnd_8271485 : Nat := 4247247531454675510597639

theorem tailTrace_8271485 : CollatzResearch.WordTrace tailWord_8271485 prefixEnd_8271485 4247247531454675510597639 := by
  unfold tailWord_8271485
  simp only [CollatzResearch.WordTrace]
  refine ⟨301685842438829977015727909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201123894959219984677151939 301685842438829977015727909)
  ·
    refine ⟨56566095457280620690448983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301685842438829977015727909 56566095457280620690448983)
    ·
      refine ⟨84849143185920931035673475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56566095457280620690448983 84849143185920931035673475)
      ·
        refine ⟨127273714778881396553510213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84849143185920931035673475 127273714778881396553510213)
        ·
          refine ⟨23863821521040261853783165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127273714778881396553510213 23863821521040261853783165)
          ·
            refine ⟨8948933070390098195168687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23863821521040261853783165 8948933070390098195168687)
            ·
              refine ⟨13423399605585147292753031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948933070390098195168687 13423399605585147292753031)
              ·
                refine ⟨20135099408377720939129547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423399605585147292753031 20135099408377720939129547)
                ·
                  refine ⟨30202649112566581408694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20135099408377720939129547 30202649112566581408694321)
                  ·
                    refine ⟨22651986834424936056520741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30202649112566581408694321 22651986834424936056520741)
                    ·
                      refine ⟨4247247531454675510597639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22651986834424936056520741 4247247531454675510597639)
                      ·
                        rfl

theorem cell23_8271485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_8271485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271485 prefixEnd_8271485 := by exact prefixLift 8271485
  have htrace : WordTrace (prefixWord ++ tailWord_8271485) baseStart_8271485 baseEnd_8271485 := by
    simpa [prefixWord, tailWord_8271485, baseEnd_8271485] using wordTrace_append hprefix tailTrace_8271485
  have hstable : (prefixWord ++ tailWord_8271485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271485).length < 2 ^ (prefixWord ++ tailWord_8271485).sum := by decide
  have hdescent : baseEnd_8271485 < baseStart_8271485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271492 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_8271492 : Nat := 118140960795 + 8271492 * 2 ^ 59
def prefixEnd_8271492 : Nat := 4983230072969 + 3 ^ 40 * 8271492 * 2
def baseEnd_8271492 : Nat := 4247251125819256983210107

theorem tailTrace_8271492 : CollatzResearch.WordTrace tailWord_8271492 prefixEnd_8271492 4247251125819256983210107 := by
  unfold tailWord_8271492
  simp only [CollatzResearch.WordTrace]
  refine ⟨150843048874902308605616365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201124065166536411474155153 150843048874902308605616365)
  ·
    refine ⟨56566143328088365727106137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150843048874902308605616365 56566143328088365727106137)
    ·
      refine ⟨42424607496066274295329603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56566143328088365727106137 42424607496066274295329603)
      ·
        refine ⟨63636911244099411442994405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424607496066274295329603 63636911244099411442994405)
        ·
          refine ⟨11931920858268639645561451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63636911244099411442994405 11931920858268639645561451)
          ·
            refine ⟨17897881287402959468342177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931920858268639645561451 17897881287402959468342177)
            ·
              refine ⟨13423410965552219601256633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17897881287402959468342177 13423410965552219601256633)
              ·
                refine ⟨10067558224164164700942475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13423410965552219601256633 10067558224164164700942475)
                ·
                  refine ⟨15101337336246247051413713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067558224164164700942475 15101337336246247051413713)
                  ·
                    refine ⟨11326003002184685288560285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15101337336246247051413713 11326003002184685288560285)
                    ·
                      refine ⟨4247251125819256983210107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11326003002184685288560285 4247251125819256983210107)
                      ·
                        rfl

theorem cell23_8271492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_8271492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271492 prefixEnd_8271492 := by exact prefixLift 8271492
  have htrace : WordTrace (prefixWord ++ tailWord_8271492) baseStart_8271492 baseEnd_8271492 := by
    simpa [prefixWord, tailWord_8271492, baseEnd_8271492] using wordTrace_append hprefix tailTrace_8271492
  have hstable : (prefixWord ++ tailWord_8271492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271492).length < 2 ^ (prefixWord ++ tailWord_8271492).sum := by decide
  have hdescent : baseEnd_8271492 < baseStart_8271492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271548 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_8271548 : Nat := 118140960795 + 8271548 * 2 ^ 59
def prefixEnd_8271548 : Nat := 4983230072969 + 3 ^ 40 * 8271548 * 2
def baseEnd_8271548 : Nat := 4247279880735908764109849

theorem tailTrace_8271548 : CollatzResearch.WordTrace tailWord_8271548 prefixEnd_8271548 4247279880735908764109849 := by
  unfold tailWord_8271548
  simp only [CollatzResearch.WordTrace]
  refine ⟨150844070118800869387635649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201125426825067825850180865 150844070118800869387635649)
  ·
    refine ⟨113133052589100652040726737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150844070118800869387635649 113133052589100652040726737)
    ·
      refine ⟨84849789441825489030545053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113133052589100652040726737 84849789441825489030545053)
      ·
        refine ⟨31818671040684558386454395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84849789441825489030545053 31818671040684558386454395)
        ·
          refine ⟨47728006561026837579681593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31818671040684558386454395 47728006561026837579681593)
          ·
            refine ⟨35796004920770128184761195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47728006561026837579681593 35796004920770128184761195)
            ·
              refine ⟨53694007381155192277141793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35796004920770128184761195 53694007381155192277141793)
              ·
                refine ⟨40270505535866394207856345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53694007381155192277141793 40270505535866394207856345)
                ·
                  refine ⟨30202879151899795655892259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40270505535866394207856345 30202879151899795655892259)
                  ·
                    refine ⟨45304318727849693483838389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30202879151899795655892259 45304318727849693483838389)
                    ·
                      refine ⟨4247279880735908764109849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45304318727849693483838389 4247279880735908764109849)
                      ·
                        rfl

theorem cell23_8271548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_8271548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271548 prefixEnd_8271548 := by exact prefixLift 8271548
  have htrace : WordTrace (prefixWord ++ tailWord_8271548) baseStart_8271548 baseEnd_8271548 := by
    simpa [prefixWord, tailWord_8271548, baseEnd_8271548] using wordTrace_append hprefix tailTrace_8271548
  have hstable : (prefixWord ++ tailWord_8271548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271548).length < 2 ^ (prefixWord ++ tailWord_8271548).sum := by decide
  have hdescent : baseEnd_8271548 < baseStart_8271548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271551 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 9]
def baseStart_8271551 : Nat := 118140960795 + 8271551 * 2 ^ 59
def prefixEnd_8271551 : Nat := 4983230072969 + 3 ^ 40 * 8271551 * 2
def baseEnd_8271551 : Nat := 471920157908652472485815

theorem tailTrace_8271551 : CollatzResearch.WordTrace tailWord_8271551 prefixEnd_8271551 471920157908652472485815 := by
  unfold tailWord_8271551
  simp only [CollatzResearch.WordTrace]
  refine ⟨301688249656590870287630507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201125499771060580191753671 301688249656590870287630507)
  ·
    refine ⟨452532374484886305431445761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301688249656590870287630507 452532374484886305431445761)
    ·
      refine ⟨339399280863664729073584321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452532374484886305431445761 339399280863664729073584321)
      ·
        refine ⟨254549460647748546805188241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339399280863664729073584321 254549460647748546805188241)
        ·
          refine ⟨190912095485811410103891181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254549460647748546805188241 190912095485811410103891181)
          ·
            refine ⟨71592035807179278788959193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190912095485811410103891181 71592035807179278788959193)
            ·
              refine ⟨53694026855384459091719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71592035807179278788959193 53694026855384459091719395)
              ·
                refine ⟨80541040283076688637579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53694026855384459091719395 80541040283076688637579093)
                ·
                  refine ⟨471920157908652472485815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80541040283076688637579093 471920157908652472485815)
                  ·
                    rfl

theorem cell23_8271551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 9].length) (baseStart_8271551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271551 prefixEnd_8271551 := by exact prefixLift 8271551
  have htrace : WordTrace (prefixWord ++ tailWord_8271551) baseStart_8271551 baseEnd_8271551 := by
    simpa [prefixWord, tailWord_8271551, baseEnd_8271551] using wordTrace_append hprefix tailTrace_8271551
  have hstable : (prefixWord ++ tailWord_8271551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271551).length < 2 ^ (prefixWord ++ tailWord_8271551).sum := by decide
  have hdescent : baseEnd_8271551 < baseStart_8271551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271562 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_8271562 : Nat := 118140960795 + 8271562 * 2 ^ 59
def prefixEnd_8271562 : Nat := 4983230072969 + 3 ^ 40 * 8271562 * 2
def baseEnd_8271562 : Nat := 4247287069465071709334785

theorem tailTrace_8271562 : CollatzResearch.WordTrace tailWord_8271562 prefixEnd_8271562 4247287069465071709334785 := by
  unfold tailWord_8271562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75422162714887754791570235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201125767239700679444187293 75422162714887754791570235)
  ·
    refine ⟨113133244072331632187355353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75422162714887754791570235 113133244072331632187355353)
    ·
      refine ⟨84849933054248724140516515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113133244072331632187355353 84849933054248724140516515)
      ·
        refine ⟨127274899581373086210774773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84849933054248724140516515 127274899581373086210774773)
        ·
          refine ⟨11932021835753726832260135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127274899581373086210774773 11932021835753726832260135)
          ·
            refine ⟨17898032753630590248390203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932021835753726832260135 17898032753630590248390203)
            ·
              refine ⟨26847049130445885372585305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17898032753630590248390203 26847049130445885372585305)
              ·
                refine ⟨20135286847834414029438979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26847049130445885372585305 20135286847834414029438979)
                ·
                  refine ⟨30202930271751621044158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20135286847834414029438979 30202930271751621044158469)
                  ·
                    refine ⟨5663049425953428945779713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30202930271751621044158469 5663049425953428945779713)
                    ·
                      refine ⟨4247287069465071709334785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663049425953428945779713 4247287069465071709334785)
                      ·
                        rfl

theorem cell23_8271562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_8271562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271562 prefixEnd_8271562 := by exact prefixLift 8271562
  have htrace : WordTrace (prefixWord ++ tailWord_8271562) baseStart_8271562 baseEnd_8271562 := by
    simpa [prefixWord, tailWord_8271562, baseEnd_8271562] using wordTrace_append hprefix tailTrace_8271562
  have hstable : (prefixWord ++ tailWord_8271562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271562).length < 2 ^ (prefixWord ++ tailWord_8271562).sum := by decide
  have hdescent : baseEnd_8271562 < baseStart_8271562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271598 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_8271598 : Nat := 118140960795 + 8271598 * 2 ^ 59
def prefixEnd_8271598 : Nat := 4983230072969 + 3 ^ 40 * 8271598 * 2
def baseEnd_8271598 : Nat := 1415768518256211189494873

theorem tailTrace_8271598 : CollatzResearch.WordTrace tailWord_8271598 prefixEnd_8271598 1415768518256211189494873 := by
  unfold tailWord_8271598
  simp only [CollatzResearch.WordTrace]
  refine ⟨37711245485927574664323931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201126642591613731543060965 37711245485927574664323931)
  ·
    refine ⟨56566868228891361996485897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37711245485927574664323931 56566868228891361996485897)
    ·
      refine ⟨42425151171668521497364423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56566868228891361996485897 42425151171668521497364423)
      ·
        refine ⟨63637726757502782246046635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42425151171668521497364423 63637726757502782246046635)
        ·
          refine ⟨95456590136254173369069953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63637726757502782246046635 95456590136254173369069953)
          ·
            refine ⟨71592442602190630026802465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95456590136254173369069953 71592442602190630026802465)
            ·
              refine ⟨53694331951642972520101849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71592442602190630026802465 53694331951642972520101849)
              ·
                refine ⟨40270748963732229390076387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53694331951642972520101849 40270748963732229390076387)
                ·
                  refine ⟨60406123445598344085114581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40270748963732229390076387 60406123445598344085114581)
                  ·
                    refine ⟨1415768518256211189494873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60406123445598344085114581 1415768518256211189494873)
                    ·
                      rfl

theorem cell23_8271598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_8271598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271598 prefixEnd_8271598 := by exact prefixLift 8271598
  have htrace : WordTrace (prefixWord ++ tailWord_8271598) baseStart_8271598 baseEnd_8271598 := by
    simpa [prefixWord, tailWord_8271598, baseEnd_8271598] using wordTrace_append hprefix tailTrace_8271598
  have hstable : (prefixWord ++ tailWord_8271598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271598).length < 2 ^ (prefixWord ++ tailWord_8271598).sum := by decide
  have hdescent : baseEnd_8271598 < baseStart_8271598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271611 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 10]
def baseStart_8271611 : Nat := 118140960795 + 8271611 * 2 ^ 59
def prefixEnd_8271611 : Nat := 4983230072969 + 3 ^ 40 * 8271611 * 2
def baseEnd_8271611 : Nat := 1415770743339047339207353

theorem tailTrace_8271611 : CollatzResearch.WordTrace tailWord_8271611 prefixEnd_8271611 1415770743339047339207353 := by
  unfold tailWord_8271611
  simp only [CollatzResearch.WordTrace]
  refine ⟨301690438036373500534814687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201126958690915667023209791 301690438036373500534814687)
  ·
    refine ⟨452535657054560250802222031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301690438036373500534814687 452535657054560250802222031)
    ·
      refine ⟨678803485581840376203333047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452535657054560250802222031 678803485581840376203333047)
      ·
        refine ⟨1018205228372760564304999571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678803485581840376203333047 1018205228372760564304999571)
        ·
          refine ⟨1527307842559140846457499357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018205228372760564304999571 1527307842559140846457499357)
          ·
            refine ⟨572740440959677817421562259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1527307842559140846457499357 572740440959677817421562259)
            ·
              refine ⟨859110661439516726132343389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572740440959677817421562259 859110661439516726132343389)
              ·
                refine ⟨322166498039818772299628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859110661439516726132343389 322166498039818772299628771)
                ·
                  refine ⟨483249747059728158449443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322166498039818772299628771 483249747059728158449443157)
                  ·
                    refine ⟨1415770743339047339207353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 483249747059728158449443157 1415770743339047339207353)
                    ·
                      rfl

theorem cell23_8271611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_8271611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271611 prefixEnd_8271611 := by exact prefixLift 8271611
  have htrace : WordTrace (prefixWord ++ tailWord_8271611) baseStart_8271611 baseEnd_8271611 := by
    simpa [prefixWord, tailWord_8271611, baseEnd_8271611] using wordTrace_append hprefix tailTrace_8271611
  have hstable : (prefixWord ++ tailWord_8271611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271611).length < 2 ^ (prefixWord ++ tailWord_8271611).sum := by decide
  have hdescent : baseEnd_8271611 < baseStart_8271611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271648 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_8271648 : Nat := 118140960795 + 8271648 * 2 ^ 59
def prefixEnd_8271648 : Nat := 4983230072969 + 3 ^ 40 * 8271648 * 2
def baseEnd_8271648 : Nat := 4247331228801358372859389

theorem tailTrace_8271648 : CollatzResearch.WordTrace tailWord_8271648 prefixEnd_8271648 4247331228801358372859389 := by
  unfold tailWord_8271648
  simp only [CollatzResearch.WordTrace]
  refine ⟨150845893768619727926955799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201127858358159637235941065 150845893768619727926955799)
  ·
    refine ⟨226268840652929591890433699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150845893768619727926955799 226268840652929591890433699)
    ·
      refine ⟨339403260979394387835650549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226268840652929591890433699 339403260979394387835650549)
      ·
        refine ⟨31819055716818223859592239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339403260979394387835650549 31819055716818223859592239)
        ·
          refine ⟨47728583575227335789388359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31819055716818223859592239 47728583575227335789388359)
          ·
            refine ⟨71592875362841003684082539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47728583575227335789388359 71592875362841003684082539)
            ·
              refine ⟨107389313044261505526123809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71592875362841003684082539 107389313044261505526123809)
              ·
                refine ⟨80541984783196129144592857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107389313044261505526123809 80541984783196129144592857)
                ·
                  refine ⟨60406488587397096858444643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80541984783196129144592857 60406488587397096858444643)
                  ·
                    refine ⟨90609732881095645287666965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60406488587397096858444643 90609732881095645287666965)
                    ·
                      refine ⟨4247331228801358372859389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90609732881095645287666965 4247331228801358372859389)
                      ·
                        rfl

theorem cell23_8271648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_8271648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271648 prefixEnd_8271648 := by exact prefixLift 8271648
  have htrace : WordTrace (prefixWord ++ tailWord_8271648) baseStart_8271648 baseEnd_8271648 := by
    simpa [prefixWord, tailWord_8271648, baseEnd_8271648] using wordTrace_append hprefix tailTrace_8271648
  have hstable : (prefixWord ++ tailWord_8271648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271648).length < 2 ^ (prefixWord ++ tailWord_8271648).sum := by decide
  have hdescent : baseEnd_8271648 < baseStart_8271648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271652 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_8271652 : Nat := 118140960795 + 8271652 * 2 ^ 59
def prefixEnd_8271652 : Nat := 4983230072969 + 3 ^ 40 * 8271652 * 2
def baseEnd_8271652 : Nat := 4247333282723976357209371

theorem tailTrace_8271652 : CollatzResearch.WordTrace tailWord_8271652 prefixEnd_8271652 4247333282723976357209371 := by
  unfold tailWord_8271652
  simp only [CollatzResearch.WordTrace]
  refine ⟨150845966714612482268528605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201127955619483309691371473 150845966714612482268528605)
  ·
    refine ⟨56567237517979680850698227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150845966714612482268528605 56567237517979680850698227)
    ·
      refine ⟨84850856276969521276047341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56567237517979680850698227 84850856276969521276047341)
      ·
        refine ⟨31819071103863570478517753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84850856276969521276047341 31819071103863570478517753)
        ·
          refine ⟨23864303327897677858888315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31819071103863570478517753 23864303327897677858888315)
          ·
            refine ⟨35796454991846516788332473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23864303327897677858888315 35796454991846516788332473)
            ·
              refine ⟨26847341243884887591249355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35796454991846516788332473 26847341243884887591249355)
              ·
                refine ⟨40271011865827331386874033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26847341243884887591249355 40271011865827331386874033)
                ·
                  refine ⟨30203258899370498540155525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40271011865827331386874033 30203258899370498540155525)
                  ·
                    refine ⟨5663111043631968476279161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30203258899370498540155525 5663111043631968476279161)
                    ·
                      refine ⟨4247333282723976357209371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663111043631968476279161 4247333282723976357209371)
                      ·
                        rfl

theorem cell23_8271652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_8271652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271652 prefixEnd_8271652 := by exact prefixLift 8271652
  have htrace : WordTrace (prefixWord ++ tailWord_8271652) baseStart_8271652 baseEnd_8271652 := by
    simpa [prefixWord, tailWord_8271652, baseEnd_8271652] using wordTrace_append hprefix tailTrace_8271652
  have hstable : (prefixWord ++ tailWord_8271652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271652).length < 2 ^ (prefixWord ++ tailWord_8271652).sum := by decide
  have hdescent : baseEnd_8271652 < baseStart_8271652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271772 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8271772 : Nat := 118140960795 + 8271772 * 2 ^ 59
def prefixEnd_8271772 : Nat := 4983230072969 + 3 ^ 40 * 8271772 * 2
def baseEnd_8271772 : Nat := 4247394900402515887708819

theorem tailTrace_8271772 : CollatzResearch.WordTrace tailWord_8271772 prefixEnd_8271772 4247394900402515887708819 := by
  unfold tailWord_8271772
  simp only [CollatzResearch.WordTrace]
  refine ⟨150848155094395112515712785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201130873459193483354283713 150848155094395112515712785)
  ·
    refine ⟨113136116320796334386784589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150848155094395112515712785 113136116320796334386784589)
    ·
      refine ⟨42426043620298625395044221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113136116320796334386784589 42426043620298625395044221)
      ·
        refine ⟨15909766357611984523141583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42426043620298625395044221 15909766357611984523141583)
        ·
          refine ⟨23864649536417976784712375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15909766357611984523141583 23864649536417976784712375)
          ·
            refine ⟨35796974304626965177068563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23864649536417976784712375 35796974304626965177068563)
            ·
              refine ⟨53695461456940447765602845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35796974304626965177068563 53695461456940447765602845)
              ·
                refine ⟨20135798046352667912101067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53695461456940447765602845 20135798046352667912101067)
                ·
                  refine ⟨30203697069529001868151601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20135798046352667912101067 30203697069529001868151601)
                  ·
                    refine ⟨22652772802146751401113701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30203697069529001868151601 22652772802146751401113701)
                    ·
                      refine ⟨4247394900402515887708819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22652772802146751401113701 4247394900402515887708819)
                      ·
                        rfl

theorem cell23_8271772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8271772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271772 prefixEnd_8271772 := by exact prefixLift 8271772
  have htrace : WordTrace (prefixWord ++ tailWord_8271772) baseStart_8271772 baseEnd_8271772 := by
    simpa [prefixWord, tailWord_8271772, baseEnd_8271772] using wordTrace_append hprefix tailTrace_8271772
  have hstable : (prefixWord ++ tailWord_8271772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271772).length < 2 ^ (prefixWord ++ tailWord_8271772).sum := by decide
  have hdescent : baseEnd_8271772 < baseStart_8271772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271790 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8271790 : Nat := 118140960795 + 8271790 * 2 ^ 59
def prefixEnd_8271790 : Nat := 4983230072969 + 3 ^ 40 * 8271790 * 2
def baseEnd_8271790 : Nat := 1415801381018098939094579

theorem tailTrace_8271790 : CollatzResearch.WordTrace tailWord_8271790 prefixEnd_8271790 1415801381018098939094579 := by
  unfold tailWord_8271790
  simp only [CollatzResearch.WordTrace]
  refine ⟨37712120837840626763197603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201131311135150009403720549 37712120837840626763197603)
  ·
    refine ⟨56568181256760940144796405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37712120837840626763197603 56568181256760940144796405)
    ·
      refine ⟨5303266992821338138574663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56568181256760940144796405 5303266992821338138574663)
      ·
        refine ⟨7954900489232007207861995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303266992821338138574663 7954900489232007207861995)
        ·
          refine ⟨11932350733848010811792993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954900489232007207861995 11932350733848010811792993)
          ·
            refine ⟨8949263050386008108844745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11932350733848010811792993 8949263050386008108844745)
            ·
              refine ⟨6711947287789506081633559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949263050386008108844745 6711947287789506081633559)
              ·
                refine ⟨10067920931684259122450339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711947287789506081633559 10067920931684259122450339)
                ·
                  refine ⟨15101881397526388683675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067920931684259122450339 15101881397526388683675509)
                  ·
                    refine ⟨1415801381018098939094579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15101881397526388683675509 1415801381018098939094579)
                    ·
                      rfl

theorem cell23_8271790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8271790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271790 prefixEnd_8271790 := by exact prefixLift 8271790
  have htrace : WordTrace (prefixWord ++ tailWord_8271790) baseStart_8271790 baseEnd_8271790 := by
    simpa [prefixWord, tailWord_8271790, baseEnd_8271790] using wordTrace_append hprefix tailTrace_8271790
  have hstable : (prefixWord ++ tailWord_8271790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271790).length < 2 ^ (prefixWord ++ tailWord_8271790).sum := by decide
  have hdescent : baseEnd_8271790 < baseStart_8271790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271793 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_8271793 : Nat := 118140960795 + 8271793 * 2 ^ 59
def prefixEnd_8271793 : Nat := 4983230072969 + 3 ^ 40 * 8271793 * 2
def baseEnd_8271793 : Nat := 4247405683496260305546223

theorem tailTrace_8271793 : CollatzResearch.WordTrace tailWord_8271793 prefixEnd_8271793 4247405683496260305546223 := by
  unfold tailWord_8271793
  simp only [CollatzResearch.WordTrace]
  refine ⟨301697076121714145617940033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201131384081142763745293355 301697076121714145617940033)
  ·
    refine ⟨226272807091285609213455025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301697076121714145617940033 226272807091285609213455025)
    ·
      refine ⟨169704605318464206910091269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226272807091285609213455025 169704605318464206910091269)
      ·
        refine ⟨31819613497212038795642113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169704605318464206910091269 31819613497212038795642113)
        ·
          refine ⟨23864710122909029096731585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31819613497212038795642113 23864710122909029096731585)
          ·
            refine ⟨17898532592181771822548689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23864710122909029096731585 17898532592181771822548689)
            ·
              refine ⟨13423899444136328866911517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17898532592181771822548689 13423899444136328866911517)
              ·
                refine ⟨5033962291551123325091819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13423899444136328866911517 5033962291551123325091819)
                ·
                  refine ⟨7550943437326684987637729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033962291551123325091819 7550943437326684987637729)
                  ·
                    refine ⟨5663207577995013740728297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7550943437326684987637729 5663207577995013740728297)
                    ·
                      refine ⟨4247405683496260305546223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663207577995013740728297 4247405683496260305546223)
                      ·
                        rfl

theorem cell23_8271793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_8271793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271793 prefixEnd_8271793 := by exact prefixLift 8271793
  have htrace : WordTrace (prefixWord ++ tailWord_8271793) baseStart_8271793 baseEnd_8271793 := by
    simpa [prefixWord, tailWord_8271793, baseEnd_8271793] using wordTrace_append hprefix tailTrace_8271793
  have hstable : (prefixWord ++ tailWord_8271793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271793).length < 2 ^ (prefixWord ++ tailWord_8271793).sum := by decide
  have hdescent : baseEnd_8271793 < baseStart_8271793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271802 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_8271802 : Nat := 118140960795 + 8271802 * 2 ^ 59
def prefixEnd_8271802 : Nat := 4983230072969 + 3 ^ 40 * 8271802 * 2
def baseEnd_8271802 : Nat := 4247410304822150770333681

theorem tailTrace_8271802 : CollatzResearch.WordTrace tailWord_8271802 prefixEnd_8271802 4247410304822150770333681 := by
  unfold tailWord_8271802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424351094670385038754415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201131602919121026770011773 75424351094670385038754415)
  ·
    refine ⟨113136526642005577558131623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75424351094670385038754415 113136526642005577558131623)
    ·
      refine ⟨169704789963008366337197435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113136526642005577558131623 169704789963008366337197435)
      ·
        refine ⟨254557184944512549505796153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169704789963008366337197435 254557184944512549505796153)
        ·
          refine ⟨190917888708384412129347115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254557184944512549505796153 190917888708384412129347115)
          ·
            refine ⟨286376833062576618194020673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190917888708384412129347115 286376833062576618194020673)
            ·
              refine ⟨214782624796932463645515505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286376833062576618194020673 214782624796932463645515505)
              ·
                refine ⟨161086968597699347734136629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214782624796932463645515505 161086968597699347734136629)
                ·
                  refine ⟨15101903306034313850075309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161086968597699347734136629 15101903306034313850075309)
                  ·
                    refine ⟨5663213739762867693778241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15101903306034313850075309 5663213739762867693778241)
                    ·
                      refine ⟨4247410304822150770333681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663213739762867693778241 4247410304822150770333681)
                      ·
                        rfl

theorem cell23_8271802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_8271802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271802 prefixEnd_8271802 := by exact prefixLift 8271802
  have htrace : WordTrace (prefixWord ++ tailWord_8271802) baseStart_8271802 baseEnd_8271802 := by
    simpa [prefixWord, tailWord_8271802, baseEnd_8271802] using wordTrace_append hprefix tailTrace_8271802
  have hstable : (prefixWord ++ tailWord_8271802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271802).length < 2 ^ (prefixWord ++ tailWord_8271802).sum := by decide
  have hdescent : baseEnd_8271802 < baseStart_8271802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271826 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_8271826 : Nat := 118140960795 + 8271826 * 2 ^ 59
def prefixEnd_8271826 : Nat := 4983230072969 + 3 ^ 40 * 8271826 * 2
def baseEnd_8271826 : Nat := 4247422628357858676433571

theorem tailTrace_8271826 : CollatzResearch.WordTrace tailWord_8271826 prefixEnd_8271826 4247422628357858676433571 := by
  unfold tailWord_8271826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424569932648648063472833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201132186487063061502594221 75424569932648648063472833)
  ·
    refine ⟨56568427449486486047604625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75424569932648648063472833 56568427449486486047604625)
    ·
      refine ⟨42426320587114864535703469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56568427449486486047604625 42426320587114864535703469)
      ·
        refine ⟨15909870220168074200888801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42426320587114864535703469 15909870220168074200888801)
        ·
          refine ⟨11932402665126055650666601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15909870220168074200888801 11932402665126055650666601)
          ·
            refine ⟨8949301998844541737999951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11932402665126055650666601 8949301998844541737999951)
            ·
              refine ⟨13423952998266812606999927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8949301998844541737999951 13423952998266812606999927)
              ·
                refine ⟨20135929497400218910499891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423952998266812606999927 20135929497400218910499891)
                ·
                  refine ⟨30203894246100328365749837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20135929497400218910499891 30203894246100328365749837)
                  ·
                    refine ⟨11326460342287623137156189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30203894246100328365749837 11326460342287623137156189)
                    ·
                      refine ⟨4247422628357858676433571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11326460342287623137156189 4247422628357858676433571)
                      ·
                        rfl

theorem cell23_8271826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_8271826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271826 prefixEnd_8271826 := by exact prefixLift 8271826
  have htrace : WordTrace (prefixWord ++ tailWord_8271826) baseStart_8271826 baseEnd_8271826 := by
    simpa [prefixWord, tailWord_8271826, baseEnd_8271826] using wordTrace_append hprefix tailTrace_8271826
  have hstable : (prefixWord ++ tailWord_8271826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271826).length < 2 ^ (prefixWord ++ tailWord_8271826).sum := by decide
  have hdescent : baseEnd_8271826 < baseStart_8271826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271959 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_8271959 : Nat := 118140960795 + 8271959 * 2 ^ 59
def prefixEnd_8271959 : Nat := 4983230072969 + 3 ^ 40 * 8271959 * 2
def baseEnd_8271959 : Nat := 4247490921284906656070459

theorem tailTrace_8271959 : CollatzResearch.WordTrace tailWord_8271959 prefixEnd_8271959 4247490921284906656070459 := by
  unfold tailWord_8271959
  simp only [CollatzResearch.WordTrace]
  refine ⟨301703130639112755968482931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201135420426075170645655287 301703130639112755968482931)
  ·
    refine ⟨452554695958669133952724397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301703130639112755968482931 452554695958669133952724397)
    ·
      refine ⟨169708010984500925232271649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452554695958669133952724397 169708010984500925232271649)
      ·
        refine ⟨127281008238375693924203737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169708010984500925232271649 127281008238375693924203737)
        ·
          refine ⟨95460756178781770443152803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127281008238375693924203737 95460756178781770443152803)
          ·
            refine ⟨143191134268172655664729205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95460756178781770443152803 143191134268172655664729205)
            ·
              refine ⟨13424168837641186468568363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143191134268172655664729205 13424168837641186468568363)
              ·
                refine ⟨20136253256461779702852545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13424168837641186468568363 20136253256461779702852545)
                ·
                  refine ⟨15102189942346334777139409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20136253256461779702852545 15102189942346334777139409)
                  ·
                    refine ⟨11326642456759751082854557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15102189942346334777139409 11326642456759751082854557)
                    ·
                      refine ⟨4247490921284906656070459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11326642456759751082854557 4247490921284906656070459)
                      ·
                        rfl

theorem cell23_8271959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_8271959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271959 prefixEnd_8271959 := by exact prefixLift 8271959
  have htrace : WordTrace (prefixWord ++ tailWord_8271959) baseStart_8271959 baseEnd_8271959 := by
    simpa [prefixWord, tailWord_8271959, baseEnd_8271959] using wordTrace_append hprefix tailTrace_8271959
  have hstable : (prefixWord ++ tailWord_8271959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271959).length < 2 ^ (prefixWord ++ tailWord_8271959).sum := by decide
  have hdescent : baseEnd_8271959 < baseStart_8271959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8271982 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_8271982 : Nat := 118140960795 + 8271982 * 2 ^ 59
def prefixEnd_8271982 : Nat := 4983230072969 + 3 ^ 40 * 8271982 * 2
def baseEnd_8271982 : Nat := 4247502731339960066082853

theorem tailTrace_8271982 : CollatzResearch.WordTrace tailWord_8271982 prefixEnd_8271982 4247502731339960066082853 := by
  unfold tailWord_8271982
  simp only [CollatzResearch.WordTrace]
  refine ⟨37712996189753678862071275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201135979678686287264380133 37712996189753678862071275)
  ·
    refine ⟨56569494284630518293106913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37712996189753678862071275 56569494284630518293106913)
    ·
      refine ⟨42427120713472888719830185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56569494284630518293106913 42427120713472888719830185)
      ·
        refine ⟨31820340535104666539872639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42427120713472888719830185 31820340535104666539872639)
        ·
          refine ⟨47730510802656999809808959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31820340535104666539872639 47730510802656999809808959)
          ·
            refine ⟨71595766203985499714713439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47730510802656999809808959 71595766203985499714713439)
            ·
              refine ⟨107393649305978249572070159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71595766203985499714713439 107393649305978249572070159)
              ·
                refine ⟨161090473958967374358105239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107393649305978249572070159 161090473958967374358105239)
                ·
                  refine ⟨241635710938451061537157859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161090473958967374358105239 241635710938451061537157859)
                  ·
                    refine ⟨362453566407676592305736789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241635710938451061537157859 362453566407676592305736789)
                    ·
                      refine ⟨4247502731339960066082853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362453566407676592305736789 4247502731339960066082853)
                      ·
                        rfl

theorem cell23_8271982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_8271982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8271982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8271982 prefixEnd_8271982 := by exact prefixLift 8271982
  have htrace : WordTrace (prefixWord ++ tailWord_8271982) baseStart_8271982 baseEnd_8271982 := by
    simpa [prefixWord, tailWord_8271982, baseEnd_8271982] using wordTrace_append hprefix tailTrace_8271982
  have hstable : (prefixWord ++ tailWord_8271982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8271982).length < 2 ^ (prefixWord ++ tailWord_8271982).sum := by decide
  have hdescent : baseEnd_8271982 < baseStart_8271982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8271982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272009 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_8272009 : Nat := 118140960795 + 8272009 * 2 ^ 59
def prefixEnd_8272009 : Nat := 4983230072969 + 3 ^ 40 * 8272009 * 2
def baseEnd_8272009 : Nat := 1415838865105877153481743

theorem tailTrace_8272009 : CollatzResearch.WordTrace tailWord_8272009 prefixEnd_8272009 1415838865105877153481743 := by
  unfold tailWord_8272009
  simp only [CollatzResearch.WordTrace]
  refine ⟨301704954288931614507803081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201136636192621076338535387 301704954288931614507803081)
  ·
    refine ⟨226278715716698710880852311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301704954288931614507803081 226278715716698710880852311)
    ·
      refine ⟨339418073575048066321278467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226278715716698710880852311 339418073575048066321278467)
      ·
        refine ⟨509127110362572099481917701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339418073575048066321278467 509127110362572099481917701)
        ·
          refine ⟨95461333192982268652859569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509127110362572099481917701 95461333192982268652859569)
          ·
            refine ⟨71595999894736701489644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95461333192982268652859569 71595999894736701489644677)
            ·
              refine ⟨13424249980263131529308377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71595999894736701489644677 13424249980263131529308377)
              ·
                refine ⟨10068187485197348646981283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13424249980263131529308377 10068187485197348646981283)
                ·
                  refine ⟨15102281227796022970471925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068187485197348646981283 15102281227796022970471925)
                  ·
                    refine ⟨1415838865105877153481743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15102281227796022970471925 1415838865105877153481743)
                    ·
                      rfl

theorem cell23_8272009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_8272009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272009 prefixEnd_8272009 := by exact prefixLift 8272009
  have htrace : WordTrace (prefixWord ++ tailWord_8272009) baseStart_8272009 baseEnd_8272009 := by
    simpa [prefixWord, tailWord_8272009, baseEnd_8272009] using wordTrace_append hprefix tailTrace_8272009
  have hstable : (prefixWord ++ tailWord_8272009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272009).length < 2 ^ (prefixWord ++ tailWord_8272009).sum := by decide
  have hdescent : baseEnd_8272009 < baseStart_8272009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272079 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_8272079 : Nat := 118140960795 + 8272079 * 2 ^ 59
def prefixEnd_8272079 : Nat := 4983230072969 + 3 ^ 40 * 8272079 * 2
def baseEnd_8272079 : Nat := 4247552538963446186569907

theorem tailTrace_8272079 : CollatzResearch.WordTrace tailWord_8272079 prefixEnd_8272079 4247552538963446186569907 := by
  unfold tailWord_8272079
  simp only [CollatzResearch.WordTrace]
  refine ⟨301707507398678016462851291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201138338265785344308567527 301707507398678016462851291)
  ·
    refine ⟨452561261098017024694276937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301707507398678016462851291 452561261098017024694276937)
    ·
      refine ⟨339420945823512768520707703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452561261098017024694276937 339420945823512768520707703)
      ·
        refine ⟨509131418735269152781061555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339420945823512768520707703 509131418735269152781061555)
        ·
          refine ⟨763697128102903729171592333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509131418735269152781061555 763697128102903729171592333)
          ·
            refine ⟨286386423038588898439347125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763697128102903729171592333 286386423038588898439347125)
            ·
              refine ⟨26848727159867709228688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286386423038588898439347125 26848727159867709228688793)
              ·
                refine ⟨20136545369900781921516595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26848727159867709228688793 20136545369900781921516595)
                ·
                  refine ⟨30204818054851172882274893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20136545369900781921516595 30204818054851172882274893)
                  ·
                    refine ⟨11326806770569189830853085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30204818054851172882274893 11326806770569189830853085)
                    ·
                      refine ⟨4247552538963446186569907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11326806770569189830853085 4247552538963446186569907)
                      ·
                        rfl

theorem cell23_8272079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_8272079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272079 prefixEnd_8272079 := by exact prefixLift 8272079
  have htrace : WordTrace (prefixWord ++ tailWord_8272079) baseStart_8272079 baseEnd_8272079 := by
    simpa [prefixWord, tailWord_8272079, baseEnd_8272079] using wordTrace_append hprefix tailTrace_8272079
  have hstable : (prefixWord ++ tailWord_8272079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272079).length < 2 ^ (prefixWord ++ tailWord_8272079).sum := by decide
  have hdescent : baseEnd_8272079 < baseStart_8272079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272106 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_8272106 : Nat := 118140960795 + 8272106 * 2 ^ 59
def prefixEnd_8272106 : Nat := 4983230072969 + 3 ^ 40 * 8272106 * 2
def baseEnd_8272106 : Nat := 4247566402941117580932283

theorem tailTrace_8272106 : CollatzResearch.WordTrace tailWord_8272106 prefixEnd_8272106 4247566402941117580932283 := by
  unfold tailWord_8272106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75427123042395050018521043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201138994779720133382722781 75427123042395050018521043)
  ·
    refine ⟨113140684563592575027781565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75427123042395050018521043 113140684563592575027781565)
    ·
      refine ⟨42427756711347215635418087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113140684563592575027781565 42427756711347215635418087)
      ·
        refine ⟨63641635067020823453127131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42427756711347215635418087 63641635067020823453127131)
        ·
          refine ⟨95462452600531235179690697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63641635067020823453127131 95462452600531235179690697)
          ·
            refine ⟨71596839450398426384768023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95462452600531235179690697 71596839450398426384768023)
            ·
              refine ⟨107395259175597639577152035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71596839450398426384768023 107395259175597639577152035)
              ·
                refine ⟨161092888763396459365728053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107395259175597639577152035 161092888763396459365728053)
                ·
                  refine ⟨15102458321568418065537005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161092888763396459365728053 15102458321568418065537005)
                  ·
                    refine ⟨5663421870588156774576377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15102458321568418065537005 5663421870588156774576377)
                    ·
                      refine ⟨4247566402941117580932283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663421870588156774576377 4247566402941117580932283)
                      ·
                        rfl

theorem cell23_8272106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_8272106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272106 prefixEnd_8272106 := by exact prefixLift 8272106
  have htrace : WordTrace (prefixWord ++ tailWord_8272106) baseStart_8272106 baseEnd_8272106 := by
    simpa [prefixWord, tailWord_8272106, baseEnd_8272106] using wordTrace_append hprefix tailTrace_8272106
  have hstable : (prefixWord ++ tailWord_8272106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272106).length < 2 ^ (prefixWord ++ tailWord_8272106).sum := by decide
  have hdescent : baseEnd_8272106 < baseStart_8272106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272149 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_8272149 : Nat := 118140960795 + 8272149 * 2 ^ 59
def prefixEnd_8272149 : Nat := 4983230072969 + 3 ^ 40 * 8272149 * 2
def baseEnd_8272149 : Nat := 4247588482609260912694585

theorem tailTrace_8272149 : CollatzResearch.WordTrace tailWord_8272149 prefixEnd_8272149 4247588482609260912694585 := by
  unfold tailWord_8272149
  simp only [CollatzResearch.WordTrace]
  refine ⟨301710060508424418417899501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201140040338949612278599667 301710060508424418417899501)
  ·
    refine ⟨113141272690659156906712313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301710060508424418417899501 113141272690659156906712313)
    ·
      refine ⟨84855954517994367680034235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113141272690659156906712313 84855954517994367680034235)
      ·
        refine ⟨127283931776991551520051353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84855954517994367680034235 127283931776991551520051353)
        ·
          refine ⟨95462948832743663640038515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127283931776991551520051353 95462948832743663640038515)
          ·
            refine ⟨143194423249115495460057773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95462948832743663640038515 143194423249115495460057773)
            ·
              refine ⟨53697908718418310797521665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143194423249115495460057773 53697908718418310797521665)
              ·
                refine ⟨40273431538813733098141249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53697908718418310797521665 40273431538813733098141249)
                ·
                  refine ⟨30205073654110299823605937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40273431538813733098141249 30205073654110299823605937)
                  ·
                    refine ⟨22653805240582724867704453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30205073654110299823605937 22653805240582724867704453)
                    ·
                      refine ⟨4247588482609260912694585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22653805240582724867704453 4247588482609260912694585)
                      ·
                        rfl

theorem cell23_8272149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_8272149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272149 prefixEnd_8272149 := by exact prefixLift 8272149
  have htrace : WordTrace (prefixWord ++ tailWord_8272149) baseStart_8272149 baseEnd_8272149 := by
    simpa [prefixWord, tailWord_8272149, baseEnd_8272149] using wordTrace_append hprefix tailTrace_8272149
  have hstable : (prefixWord ++ tailWord_8272149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272149).length < 2 ^ (prefixWord ++ tailWord_8272149).sum := by decide
  have hdescent : baseEnd_8272149 < baseStart_8272149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272159 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 7]
def baseStart_8272159 : Nat := 118140960795 + 8272159 * 2 ^ 59
def prefixEnd_8272159 : Nat := 4983230072969 + 3 ^ 40 * 8272159 * 2
def baseEnd_8272159 : Nat := 471954846379533985952171

theorem tailTrace_8272159 : CollatzResearch.WordTrace tailWord_8272159 prefixEnd_8272159 471954846379533985952171 := by
  unfold tailWord_8272159
  simp only [CollatzResearch.WordTrace]
  refine ⟨301710425238388190125763531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201140283492258793417175687 301710425238388190125763531)
  ·
    refine ⟨452565637857582285188645297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301710425238388190125763531 452565637857582285188645297)
    ·
      refine ⟨339424228393186713891483973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452565637857582285188645297 339424228393186713891483973)
      ·
        refine ⟨63642042823722508854653245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339424228393186713891483973 63642042823722508854653245)
        ·
          refine ⟨23865766058895940820494967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63642042823722508854653245 23865766058895940820494967)
          ·
            refine ⟨35798649088343911230742451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23865766058895940820494967 35798649088343911230742451)
            ·
              refine ⟨53697973632515866846113677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35798649088343911230742451 53697973632515866846113677)
              ·
                refine ⟨20136740112193450067292629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53697973632515866846113677 20136740112193450067292629)
                ·
                  refine ⟨471954846379533985952171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20136740112193450067292629 471954846379533985952171)
                  ·
                    rfl

theorem cell23_8272159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 7].length) (baseStart_8272159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272159 prefixEnd_8272159 := by exact prefixLift 8272159
  have htrace : WordTrace (prefixWord ++ tailWord_8272159) baseStart_8272159 baseEnd_8272159 := by
    simpa [prefixWord, tailWord_8272159, baseEnd_8272159] using wordTrace_append hprefix tailTrace_8272159
  have hstable : (prefixWord ++ tailWord_8272159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272159).length < 2 ^ (prefixWord ++ tailWord_8272159).sum := by decide
  have hdescent : baseEnd_8272159 < baseStart_8272159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272199 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_8272199 : Nat := 118140960795 + 8272199 * 2 ^ 59
def prefixEnd_8272199 : Nat := 4983230072969 + 3 ^ 40 * 8272199 * 2
def baseEnd_8272199 : Nat := 4247614156641985717069355

theorem tailTrace_8272199 : CollatzResearch.WordTrace tailWord_8272199 prefixEnd_8272199 4247614156641985717069355 := by
  unfold tailWord_8272199
  simp only [CollatzResearch.WordTrace]
  refine ⟨301711884158243276957219651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201141256105495517971479767 301711884158243276957219651)
  ·
    refine ⟨452567826237364915435829477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301711884158243276957219651 452567826237364915435829477)
    ·
      refine ⟨84856467419505921644218027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452567826237364915435829477 84856467419505921644218027)
      ·
        refine ⟨127284701129258882466327041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84856467419505921644218027 127284701129258882466327041)
        ·
          refine ⟨95463525846944161849745281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127284701129258882466327041 95463525846944161849745281)
          ·
            refine ⟨71597644385208121387308961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95463525846944161849745281 71597644385208121387308961)
            ·
              refine ⟨53698233288906091040481721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71597644385208121387308961 53698233288906091040481721)
              ·
                refine ⟨40273674966679568280361291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53698233288906091040481721 40273674966679568280361291)
                ·
                  refine ⟨60410512450019352420541937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40273674966679568280361291 60410512450019352420541937)
                  ·
                    refine ⟨45307884337514514315406453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60410512450019352420541937 45307884337514514315406453)
                    ·
                      refine ⟨4247614156641985717069355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45307884337514514315406453 4247614156641985717069355)
                      ·
                        rfl

theorem cell23_8272199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_8272199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272199 prefixEnd_8272199 := by exact prefixLift 8272199
  have htrace : WordTrace (prefixWord ++ tailWord_8272199) baseStart_8272199 baseEnd_8272199 := by
    simpa [prefixWord, tailWord_8272199, baseEnd_8272199] using wordTrace_append hprefix tailTrace_8272199
  have hstable : (prefixWord ++ tailWord_8272199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272199).length < 2 ^ (prefixWord ++ tailWord_8272199).sum := by decide
  have hdescent : baseEnd_8272199 < baseStart_8272199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272293 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_8272293 : Nat := 118140960795 + 8272293 * 2 ^ 59
def prefixEnd_8272293 : Nat := 4983230072969 + 3 ^ 40 * 8272293 * 2
def baseEnd_8272293 : Nat := 4247662423823508349293923

theorem tailTrace_8272293 : CollatzResearch.WordTrace tailWord_8272293 prefixEnd_8272293 4247662423823508349293923 := by
  unfold tailWord_8272293
  simp only [CollatzResearch.WordTrace]
  refine ⟨301715312619902731011141533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201143541746601820674094355 301715312619902731011141533)
  ·
    refine ⟨113143242232463524129178075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301715312619902731011141533 113143242232463524129178075)
    ·
      refine ⟨169714863348695286193767113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113143242232463524129178075 169714863348695286193767113)
      ·
        refine ⟨127286147511521464645325335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169714863348695286193767113 127286147511521464645325335)
        ·
          refine ⟨190929221267282196967988003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127286147511521464645325335 190929221267282196967988003)
          ·
            refine ⟨286393831900923295451982005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190929221267282196967988003 286393831900923295451982005)
            ·
              refine ⟨26849421740711558948623313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286393831900923295451982005 26849421740711558948623313)
              ·
                refine ⟨20137066305533669211467485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26849421740711558948623313 20137066305533669211467485)
                ·
                  refine ⟨7551399864575125954300307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20137066305533669211467485 7551399864575125954300307)
                  ·
                    refine ⟨11327099796862688931450461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7551399864575125954300307 11327099796862688931450461)
                    ·
                      refine ⟨4247662423823508349293923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327099796862688931450461 4247662423823508349293923)
                      ·
                        rfl

theorem cell23_8272293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_8272293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272293 prefixEnd_8272293 := by exact prefixLift 8272293
  have htrace : WordTrace (prefixWord ++ tailWord_8272293) baseStart_8272293 baseEnd_8272293 := by
    simpa [prefixWord, tailWord_8272293, baseEnd_8272293] using wordTrace_append hprefix tailTrace_8272293
  have hstable : (prefixWord ++ tailWord_8272293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272293).length < 2 ^ (prefixWord ++ tailWord_8272293).sum := by decide
  have hdescent : baseEnd_8272293 < baseStart_8272293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272313 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_8272313 : Nat := 118140960795 + 8272313 * 2 ^ 59
def prefixEnd_8272313 : Nat := 4983230072969 + 3 ^ 40 * 8272313 * 2
def baseEnd_8272313 : Nat := 1415890897812199423681277

theorem tailTrace_8272313 : CollatzResearch.WordTrace tailWord_8272313 prefixEnd_8272313 1415890897812199423681277 := by
  unfold tailWord_8272313
  simp only [CollatzResearch.WordTrace]
  refine ⟨301716042079830274426869593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201144028053220182951246395 301716042079830274426869593)
  ·
    refine ⟨226287031559872705820152195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301716042079830274426869593 226287031559872705820152195)
    ·
      refine ⟨339430547339809058730228293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226287031559872705820152195 339430547339809058730228293)
      ·
        refine ⟨63643227626214198511917805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339430547339809058730228293 63643227626214198511917805)
        ·
          refine ⟨23866210359830324441969177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63643227626214198511917805 23866210359830324441969177)
          ·
            refine ⟨17899657769872743331476883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23866210359830324441969177 17899657769872743331476883)
            ·
              refine ⟨26849486654809114997215325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17899657769872743331476883 26849486654809114997215325)
              ·
                refine ⟨10068557495553418123955747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26849486654809114997215325 10068557495553418123955747)
                ·
                  refine ⟨15102836243330127185933621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068557495553418123955747 15102836243330127185933621)
                  ·
                    refine ⟨1415890897812199423681277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15102836243330127185933621 1415890897812199423681277)
                    ·
                      rfl

theorem cell23_8272313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_8272313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272313 prefixEnd_8272313 := by exact prefixLift 8272313
  have htrace : WordTrace (prefixWord ++ tailWord_8272313) baseStart_8272313 baseEnd_8272313 := by
    simpa [prefixWord, tailWord_8272313, baseEnd_8272313] using wordTrace_append hprefix tailTrace_8272313
  have hstable : (prefixWord ++ tailWord_8272313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272313).length < 2 ^ (prefixWord ++ tailWord_8272313).sum := by decide
  have hdescent : baseEnd_8272313 < baseStart_8272313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272346 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_8272346 : Nat := 118140960795 + 8272346 * 2 ^ 59
def prefixEnd_8272346 : Nat := 4983230072969 + 3 ^ 40 * 8272346 * 2
def baseEnd_8272346 : Nat := 4247689638298196641931179

theorem tailTrace_8272346 : CollatzResearch.WordTrace tailWord_8272346 prefixEnd_8272346 4247689638298196641931179 := by
  unfold tailWord_8272346
  simp only [CollatzResearch.WordTrace]
  refine ⟨75429311422177680265705223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201144830459140480708547261 75429311422177680265705223)
  ·
    refine ⟨113143967133266520398557835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75429311422177680265705223 113143967133266520398557835)
    ·
      refine ⟨169715950699899780597836753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113143967133266520398557835 169715950699899780597836753)
      ·
        refine ⟨127286963024924835448377565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169715950699899780597836753 127286963024924835448377565)
        ·
          refine ⟨47732611134346813293141587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127286963024924835448377565 47732611134346813293141587)
          ·
            refine ⟨71598916701520219939712381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47732611134346813293141587 71598916701520219939712381)
            ·
              refine ⟨26849593763070082477392143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71598916701520219939712381 26849593763070082477392143)
              ·
                refine ⟨40274390644605123716088215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26849593763070082477392143 40274390644605123716088215)
                ·
                  refine ⟨60411585966907685574132323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40274390644605123716088215 60411585966907685574132323)
                  ·
                    refine ⟨90617378950361528361198485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60411585966907685574132323 90617378950361528361198485)
                    ·
                      refine ⟨4247689638298196641931179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90617378950361528361198485 4247689638298196641931179)
                      ·
                        rfl

theorem cell23_8272346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_8272346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272346 prefixEnd_8272346 := by exact prefixLift 8272346
  have htrace : WordTrace (prefixWord ++ tailWord_8272346) baseStart_8272346 baseEnd_8272346 := by
    simpa [prefixWord, tailWord_8272346, baseEnd_8272346] using wordTrace_append hprefix tailTrace_8272346
  have hstable : (prefixWord ++ tailWord_8272346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272346).length < 2 ^ (prefixWord ++ tailWord_8272346).sum := by decide
  have hdescent : baseEnd_8272346 < baseStart_8272346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272370 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_8272370 : Nat := 118140960795 + 8272370 * 2 ^ 59
def prefixEnd_8272370 : Nat := 4983230072969 + 3 ^ 40 * 8272370 * 2
def baseEnd_8272370 : Nat := 4247701961833904548031069

theorem tailTrace_8272370 : CollatzResearch.WordTrace tailWord_8272370 prefixEnd_8272370 4247701961833904548031069 := by
  unfold tailWord_8272370
  simp only [CollatzResearch.WordTrace]
  refine ⟨75429530260155943290423641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201145414027082515441129709 75429530260155943290423641)
  ·
    refine ⟨56572147695116957467817731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75429530260155943290423641 56572147695116957467817731)
    ·
      refine ⟨84858221542675436201726597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56572147695116957467817731 84858221542675436201726597)
      ·
        refine ⟨15910916539251644287823737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84858221542675436201726597 15910916539251644287823737)
        ·
          refine ⟨11933187404438733215867803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15910916539251644287823737 11933187404438733215867803)
          ·
            refine ⟨17899781106658099823801705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933187404438733215867803 17899781106658099823801705)
            ·
              refine ⟨13424835829993574867851279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17899781106658099823801705 13424835829993574867851279)
              ·
                refine ⟨20137253744990362301776919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13424835829993574867851279 20137253744990362301776919)
                ·
                  refine ⟨30205880617485543452665379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20137253744990362301776919 30205880617485543452665379)
                  ·
                    refine ⟨45308820926228315178998069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30205880617485543452665379 45308820926228315178998069)
                    ·
                      refine ⟨4247701961833904548031069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45308820926228315178998069 4247701961833904548031069)
                      ·
                        rfl

theorem cell23_8272370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_8272370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272370 prefixEnd_8272370 := by exact prefixLift 8272370
  have htrace : WordTrace (prefixWord ++ tailWord_8272370) baseStart_8272370 baseEnd_8272370 := by
    simpa [prefixWord, tailWord_8272370, baseEnd_8272370] using wordTrace_append hprefix tailTrace_8272370
  have hstable : (prefixWord ++ tailWord_8272370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272370).length < 2 ^ (prefixWord ++ tailWord_8272370).sum := by decide
  have hdescent : baseEnd_8272370 < baseStart_8272370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272383 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_8272383 : Nat := 118140960795 + 8272383 * 2 ^ 59
def prefixEnd_8272383 : Nat := 4983230072969 + 3 ^ 40 * 8272383 * 2
def baseEnd_8272383 : Nat := 4247708637082412997168509

theorem tailTrace_8272383 : CollatzResearch.WordTrace tailWord_8272383 prefixEnd_8272383 4247708637082412997168509 := by
  unfold tailWord_8272383
  simp only [CollatzResearch.WordTrace]
  refine ⟨301718595189576676381917803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201145730126384450921278535 301718595189576676381917803)
  ·
    refine ⟨452577892784365014572876705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301718595189576676381917803 452577892784365014572876705)
    ·
      refine ⟨339433419588273760929657529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452577892784365014572876705 339433419588273760929657529)
      ·
        refine ⟨254575064691205320697243147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339433419588273760929657529 254575064691205320697243147)
        ·
          refine ⟨381862597036807981045864721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254575064691205320697243147 381862597036807981045864721)
          ·
            refine ⟨286396947777605985784398541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381862597036807981045864721 286396947777605985784398541)
            ·
              refine ⟨107398855416602244669149453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286396947777605985784398541 107398855416602244669149453)
              ·
                refine ⟨40274570781225841750931045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107398855416602244669149453 40274570781225841750931045)
                ·
                  refine ⟨7551482021479845328299571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40274570781225841750931045 7551482021479845328299571)
                  ·
                    refine ⟨11327223032219767992449357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7551482021479845328299571 11327223032219767992449357)
                    ·
                      refine ⟨4247708637082412997168509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327223032219767992449357 4247708637082412997168509)
                      ·
                        rfl

theorem cell23_8272383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_8272383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272383 prefixEnd_8272383 := by exact prefixLift 8272383
  have htrace : WordTrace (prefixWord ++ tailWord_8272383) baseStart_8272383 baseEnd_8272383 := by
    simpa [prefixWord, tailWord_8272383, baseEnd_8272383] using wordTrace_append hprefix tailTrace_8272383
  have hstable : (prefixWord ++ tailWord_8272383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272383).length < 2 ^ (prefixWord ++ tailWord_8272383).sum := by decide
  have hdescent : baseEnd_8272383 < baseStart_8272383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272404 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_8272404 : Nat := 118140960795 + 8272404 * 2 ^ 59
def prefixEnd_8272404 : Nat := 4983230072969 + 3 ^ 40 * 8272404 * 2
def baseEnd_8272404 : Nat := 4247719420176157415005913

theorem tailTrace_8272404 : CollatzResearch.WordTrace tailWord_8272404 prefixEnd_8272404 4247719420176157415005913 := by
  unfold tailWord_8272404
  simp only [CollatzResearch.WordTrace]
  refine ⟨150859680561250298484216133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201146240748333731312288177 150859680561250298484216133)
  ·
    refine ⟨28286190105234430965790525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150859680561250298484216133 28286190105234430965790525)
    ·
      refine ⟨10607321289462911612171447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28286190105234430965790525 10607321289462911612171447)
      ·
        refine ⟨15910981934194367418257171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10607321289462911612171447 15910981934194367418257171)
        ·
          refine ⟨23866472901291551127385757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15910981934194367418257171 23866472901291551127385757)
          ·
            refine ⟨8949927337984331672769659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23866472901291551127385757 8949927337984331672769659)
            ·
              refine ⟨13424891006976497509154489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8949927337984331672769659 13424891006976497509154489)
              ·
                refine ⟨10068668255232373131865867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13424891006976497509154489 10068668255232373131865867)
                ·
                  refine ⟨15103002382848559697798801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068668255232373131865867 15103002382848559697798801)
                  ·
                    refine ⟨11327251787136419773349101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15103002382848559697798801 11327251787136419773349101)
                    ·
                      refine ⟨4247719420176157415005913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327251787136419773349101 4247719420176157415005913)
                      ·
                        rfl

theorem cell23_8272404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_8272404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272404 prefixEnd_8272404 := by exact prefixLift 8272404
  have htrace : WordTrace (prefixWord ++ tailWord_8272404) baseStart_8272404 baseEnd_8272404 := by
    simpa [prefixWord, tailWord_8272404, baseEnd_8272404] using wordTrace_append hprefix tailTrace_8272404
  have hstable : (prefixWord ++ tailWord_8272404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272404).length < 2 ^ (prefixWord ++ tailWord_8272404).sum := by decide
  have hdescent : baseEnd_8272404 < baseStart_8272404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272453 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_8272453 : Nat := 118140960795 + 8272453 * 2 ^ 59
def prefixEnd_8272453 : Nat := 4983230072969 + 3 ^ 40 * 8272453 * 2
def baseEnd_8272453 : Nat := 4247744580728227723293187

theorem tailTrace_8272453 : CollatzResearch.WordTrace tailWord_8272453 prefixEnd_8272453 4247744580728227723293187 := by
  unfold tailWord_8272453
  simp only [CollatzResearch.WordTrace]
  refine ⟨301721148299323078336966013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201147432199548718891310675 301721148299323078336966013)
  ·
    refine ⟨113145430612246154376362255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301721148299323078336966013 113145430612246154376362255)
    ·
      refine ⟨169718145918369231564543383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113145430612246154376362255 169718145918369231564543383)
      ·
        refine ⟨254577218877553847346815075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169718145918369231564543383 254577218877553847346815075)
        ·
          refine ⟨381865828316330771020222613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254577218877553847346815075 381865828316330771020222613)
          ·
            refine ⟨17899960702328004891572935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381865828316330771020222613 17899960702328004891572935)
            ·
              refine ⟨26849941053492007337359403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17899960702328004891572935 26849941053492007337359403)
              ·
                refine ⟨40274911580238011006039105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26849941053492007337359403 40274911580238011006039105)
                ·
                  refine ⟨30206183685178508254529329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40274911580238011006039105 30206183685178508254529329)
                  ·
                    refine ⟨22654637763883881190896997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30206183685178508254529329 22654637763883881190896997)
                    ·
                      refine ⟨4247744580728227723293187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22654637763883881190896997 4247744580728227723293187)
                      ·
                        rfl

theorem cell23_8272453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_8272453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272453 prefixEnd_8272453 := by exact prefixLift 8272453
  have htrace : WordTrace (prefixWord ++ tailWord_8272453) baseStart_8272453 baseEnd_8272453 := by
    simpa [prefixWord, tailWord_8272453, baseEnd_8272453] using wordTrace_append hprefix tailTrace_8272453
  have hstable : (prefixWord ++ tailWord_8272453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272453).length < 2 ^ (prefixWord ++ tailWord_8272453).sum := by decide
  have hdescent : baseEnd_8272453 < baseStart_8272453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272478 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_8272478 : Nat := 118140960795 + 8272478 * 2 ^ 59
def prefixEnd_8272478 : Nat := 4983230072969 + 3 ^ 40 * 8272478 * 2
def baseEnd_8272478 : Nat := 4247757417744590125480573

theorem tailTrace_8272478 : CollatzResearch.WordTrace tailWord_8272478 prefixEnd_8272478 4247757417744590125480573 := by
  unfold tailWord_8272478
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715257515529063450828261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201148040082821671737750725 37715257515529063450828261)
  ·
    refine ⟨7071610784161699397030299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37715257515529063450828261 7071610784161699397030299)
    ·
      refine ⟨10607416176242549095545449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071610784161699397030299 10607416176242549095545449)
      ·
        refine ⟨7955562132181911821659087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607416176242549095545449 7955562132181911821659087)
        ·
          refine ⟨11933343198272867732488631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955562132181911821659087 11933343198272867732488631)
          ·
            refine ⟨17900014797409301598732947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933343198272867732488631 17900014797409301598732947)
            ·
              refine ⟨26850022196113952398099421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900014797409301598732947 26850022196113952398099421)
              ·
                refine ⟨10068758323542732149287283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26850022196113952398099421 10068758323542732149287283)
                ·
                  refine ⟨15103137485314098223930925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068758323542732149287283 15103137485314098223930925)
                  ·
                    refine ⟨5663676556992786833974097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15103137485314098223930925 5663676556992786833974097)
                    ·
                      refine ⟨4247757417744590125480573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663676556992786833974097 4247757417744590125480573)
                      ·
                        rfl

theorem cell23_8272478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_8272478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272478 prefixEnd_8272478 := by exact prefixLift 8272478
  have htrace : WordTrace (prefixWord ++ tailWord_8272478) baseStart_8272478 baseEnd_8272478 := by
    simpa [prefixWord, tailWord_8272478, baseEnd_8272478] using wordTrace_append hprefix tailTrace_8272478
  have hstable : (prefixWord ++ tailWord_8272478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272478).length < 2 ^ (prefixWord ++ tailWord_8272478).sum := by decide
  have hdescent : baseEnd_8272478 < baseStart_8272478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272513 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_8272513 : Nat := 118140960795 + 8272513 * 2 ^ 59
def prefixEnd_8272513 : Nat := 4983230072969 + 3 ^ 40 * 8272513 * 2
def baseEnd_8272513 : Nat := 4247775389567497488542911

theorem tailTrace_8272513 : CollatzResearch.WordTrace tailWord_8272513 prefixEnd_8272513 4247775389567497488542911 := by
  unfold tailWord_8272513
  simp only [CollatzResearch.WordTrace]
  refine ⟨301723336679105708584150193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201148891119403805722766795 301723336679105708584150193)
  ·
    refine ⟨226292502509329281438112645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301723336679105708584150193 226292502509329281438112645)
    ·
      refine ⟨42429844220499240269646121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226292502509329281438112645 42429844220499240269646121)
      ·
        refine ⟨31822383165374430202234591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42429844220499240269646121 31822383165374430202234591)
        ·
          refine ⟨47733574748061645303351887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31822383165374430202234591 47733574748061645303351887)
          ·
            refine ⟨71600362122092467955027831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47733574748061645303351887 71600362122092467955027831)
            ·
              refine ⟨107400543183138701932541747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71600362122092467955027831 107400543183138701932541747)
              ·
                refine ⟨161100814774708052898812621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107400543183138701932541747 161100814774708052898812621)
                ·
                  refine ⟨60412805540515519837054733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161100814774708052898812621 60412805540515519837054733)
                  ·
                    refine ⟨22654802077693319938895525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60412805540515519837054733 22654802077693319938895525)
                    ·
                      refine ⟨4247775389567497488542911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22654802077693319938895525 4247775389567497488542911)
                      ·
                        rfl

theorem cell23_8272513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_8272513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272513 prefixEnd_8272513 := by exact prefixLift 8272513
  have htrace : WordTrace (prefixWord ++ tailWord_8272513) baseStart_8272513 baseEnd_8272513 := by
    simpa [prefixWord, tailWord_8272513, baseEnd_8272513] using wordTrace_append hprefix tailTrace_8272513
  have hstable : (prefixWord ++ tailWord_8272513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272513).length < 2 ^ (prefixWord ++ tailWord_8272513).sum := by decide
  have hdescent : baseEnd_8272513 < baseStart_8272513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272523 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 5, 4]
def baseStart_8272523 : Nat := 118140960795 + 8272523 * 2 ^ 59
def prefixEnd_8272523 : Nat := 4983230072969 + 3 ^ 40 * 8272523 * 2
def baseEnd_8272523 : Nat := 1415926841458014149805955

theorem tailTrace_8272523 : CollatzResearch.WordTrace tailWord_8272523 prefixEnd_8272523 1415926841458014149805955 := by
  unfold tailWord_8272523
  simp only [CollatzResearch.WordTrace]
  refine ⟨301723701409069480292014223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201149134272712986861342815 301723701409069480292014223)
  ·
    refine ⟨452585552113604220438021335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301723701409069480292014223 452585552113604220438021335)
    ·
      refine ⟨678878328170406330657032003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452585552113604220438021335 678878328170406330657032003)
      ·
        refine ⟨1018317492255609495985548005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678878328170406330657032003 1018317492255609495985548005)
        ·
          refine ⟨190934529797926780497290251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018317492255609495985548005 190934529797926780497290251)
          ·
            refine ⟨286401794696890170745935377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190934529797926780497290251 286401794696890170745935377)
            ·
              refine ⟨214801346022667628059451533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286401794696890170745935377 214801346022667628059451533)
              ·
                refine ⟨80550504758500360522294325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214801346022667628059451533 80550504758500360522294325)
                ·
                  refine ⟨7551609821109408798965093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80550504758500360522294325 7551609821109408798965093)
                  ·
                    refine ⟨1415926841458014149805955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7551609821109408798965093 1415926841458014149805955)
                    ·
                      rfl

theorem cell23_8272523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 4].length) (baseStart_8272523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272523 prefixEnd_8272523 := by exact prefixLift 8272523
  have htrace : WordTrace (prefixWord ++ tailWord_8272523) baseStart_8272523 baseEnd_8272523 := by
    simpa [prefixWord, tailWord_8272523, baseEnd_8272523] using wordTrace_append hprefix tailTrace_8272523
  have hstable : (prefixWord ++ tailWord_8272523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272523).length < 2 ^ (prefixWord ++ tailWord_8272523).sum := by decide
  have hdescent : baseEnd_8272523 < baseStart_8272523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272530 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8272530 : Nat := 118140960795 + 8272530 * 2 ^ 59
def prefixEnd_8272530 : Nat := 4983230072969 + 3 ^ 40 * 8272530 * 2
def baseEnd_8272530 : Nat := 4247784118738623922030333

theorem tailTrace_8272530 : CollatzResearch.WordTrace tailWord_8272530 prefixEnd_8272530 4247784118738623922030333 := by
  unfold tailWord_8272530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75430989180011030121879761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201149304480029413658346029 75430989180011030121879761)
  ·
    refine ⟨56573241885008272591409821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75430989180011030121879761 56573241885008272591409821)
    ·
      refine ⟨21214965706878102221778683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56573241885008272591409821 21214965706878102221778683)
      ·
        refine ⟨31822448560317153332668025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21214965706878102221778683 31822448560317153332668025)
        ·
          refine ⟨23866836420237864999501019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31822448560317153332668025 23866836420237864999501019)
          ·
            refine ⟨35800254630356797499251529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23866836420237864999501019 35800254630356797499251529)
            ·
              refine ⟨26850190972767598124438647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35800254630356797499251529 26850190972767598124438647)
              ·
                refine ⟨40275286459151397186657971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26850190972767598124438647 40275286459151397186657971)
                ·
                  refine ⟨60412929688727095779986957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40275286459151397186657971 60412929688727095779986957)
                  ·
                    refine ⟨22654848633272660917495109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60412929688727095779986957 22654848633272660917495109)
                    ·
                      refine ⟨4247784118738623922030333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22654848633272660917495109 4247784118738623922030333)
                      ·
                        rfl

theorem cell23_8272530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8272530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272530 prefixEnd_8272530 := by exact prefixLift 8272530
  have htrace : WordTrace (prefixWord ++ tailWord_8272530) baseStart_8272530 baseEnd_8272530 := by
    simpa [prefixWord, tailWord_8272530, baseEnd_8272530] using wordTrace_append hprefix tailTrace_8272530
  have hstable : (prefixWord ++ tailWord_8272530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272530).length < 2 ^ (prefixWord ++ tailWord_8272530).sum := by decide
  have hdescent : baseEnd_8272530 < baseStart_8272530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272557 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_8272557 : Nat := 118140960795 + 8272557 * 2 ^ 59
def prefixEnd_8272557 : Nat := 4983230072969 + 3 ^ 40 * 8272557 * 2
def baseEnd_8272557 : Nat := 1415932660905431772130903

theorem tailTrace_8272557 : CollatzResearch.WordTrace tailWord_8272557 prefixEnd_8272557 1415932660905431772130903 := by
  unfold tailWord_8272557
  simp only [CollatzResearch.WordTrace]
  refine ⟨301724941490946304098751925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201149960993964202732501283 301724941490946304098751925)
  ·
    refine ⟨28286713264776216009257993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301724941490946304098751925 28286713264776216009257993)
    ·
      refine ⟨21215034948582162006943495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28286713264776216009257993 21215034948582162006943495)
      ·
        refine ⟨31822552422873243010415243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21215034948582162006943495 31822552422873243010415243)
        ·
          refine ⟨47733828634309864515622865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31822552422873243010415243 47733828634309864515622865)
          ·
            refine ⟨35800371475732398386717149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47733828634309864515622865 35800371475732398386717149)
            ·
              refine ⟨13425139303399649395018931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35800371475732398386717149 13425139303399649395018931)
              ·
                refine ⟨20137708955099474092528397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425139303399649395018931 20137708955099474092528397)
                ·
                  refine ⟨7551640858162302784698149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20137708955099474092528397 7551640858162302784698149)
                  ·
                    refine ⟨1415932660905431772130903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7551640858162302784698149 1415932660905431772130903)
                    ·
                      rfl

theorem cell23_8272557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_8272557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272557 prefixEnd_8272557 := by exact prefixLift 8272557
  have htrace : WordTrace (prefixWord ++ tailWord_8272557) baseStart_8272557 baseEnd_8272557 := by
    simpa [prefixWord, tailWord_8272557, baseEnd_8272557] using wordTrace_append hprefix tailTrace_8272557
  have hstable : (prefixWord ++ tailWord_8272557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272557).length < 2 ^ (prefixWord ++ tailWord_8272557).sum := by decide
  have hdescent : baseEnd_8272557 < baseStart_8272557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272607 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 2, 3, 2]
def baseStart_8272607 : Nat := 118140960795 + 8272607 * 2 ^ 59
def prefixEnd_8272607 : Nat := 4983230072969 + 3 ^ 40 * 8272607 * 2
def baseEnd_8272607 : Nat := 4247823656749020120767479

theorem tailTrace_8272607 : CollatzResearch.WordTrace tailWord_8272607 prefixEnd_8272607 4247823656749020120767479 := by
  unfold tailWord_8272607
  simp only [CollatzResearch.WordTrace]
  refine ⟨301726765140765162638072075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201151176760510108425381383 301726765140765162638072075)
  ·
    refine ⟨452590147711147743957108113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301726765140765162638072075 452590147711147743957108113)
    ·
      refine ⟨339442610783360807967831085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452590147711147743957108113 339442610783360807967831085)
      ·
        refine ⟨127290979043760302987936657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339442610783360807967831085 127290979043760302987936657)
        ·
          refine ⟨95468234282820227240952493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127290979043760302987936657 95468234282820227240952493)
          ·
            refine ⟨35800587856057585215357185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95468234282820227240952493 35800587856057585215357185)
            ·
              refine ⟨26850440892043188911517889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35800587856057585215357185 26850440892043188911517889)
              ·
                refine ⟨20137830669032391683638417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26850440892043188911517889 20137830669032391683638417)
                ·
                  refine ⟨15103373001774293762728813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20137830669032391683638417 15103373001774293762728813)
                  ·
                    refine ⟨5663764875665360161023305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15103373001774293762728813 5663764875665360161023305)
                    ·
                      refine ⟨4247823656749020120767479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663764875665360161023305 4247823656749020120767479)
                      ·
                        rfl

theorem cell23_8272607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_8272607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272607 prefixEnd_8272607 := by exact prefixLift 8272607
  have htrace : WordTrace (prefixWord ++ tailWord_8272607) baseStart_8272607 baseEnd_8272607 := by
    simpa [prefixWord, tailWord_8272607, baseEnd_8272607] using wordTrace_append hprefix tailTrace_8272607
  have hstable : (prefixWord ++ tailWord_8272607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272607).length < 2 ^ (prefixWord ++ tailWord_8272607).sum := by decide
  have hdescent : baseEnd_8272607 < baseStart_8272607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272620 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_8272620 : Nat := 118140960795 + 8272620 * 2 ^ 59
def prefixEnd_8272620 : Nat := 4983230072969 + 3 ^ 40 * 8272620 * 2
def baseEnd_8272620 : Nat := 4247830331997528569904919

theorem tailTrace_8272620 : CollatzResearch.WordTrace tailWord_8272620 prefixEnd_8272620 4247830331997528569904919 := by
  unfold tailWord_8272620
  simp only [CollatzResearch.WordTrace]
  refine ⟨150863619644859032929147657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201151492859812043905530209 150863619644859032929147657)
  ·
    refine ⟨113147714733644274696860743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150863619644859032929147657 113147714733644274696860743)
    ·
      refine ⟨169721572100466412045291115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113147714733644274696860743 169721572100466412045291115)
      ·
        refine ⟨254582358150699618067936673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169721572100466412045291115 254582358150699618067936673)
        ·
          refine ⟨190936768613024713550952505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254582358150699618067936673 190936768613024713550952505)
          ·
            refine ⟨143202576459768535163214379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190936768613024713550952505 143202576459768535163214379)
            ·
              refine ⟨214803864689652802744821569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143202576459768535163214379 214803864689652802744821569)
              ·
                refine ⟨161102898517239602058616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214803864689652802744821569 161102898517239602058616177)
                ·
                  refine ⟨120827173887929701543962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161102898517239602058616177 120827173887929701543962133)
                  ·
                    refine ⟨5663773775996704759873225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120827173887929701543962133 5663773775996704759873225)
                    ·
                      refine ⟨4247830331997528569904919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663773775996704759873225 4247830331997528569904919)
                      ·
                        rfl

theorem cell23_8272620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_8272620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272620 prefixEnd_8272620 := by exact prefixLift 8272620
  have htrace : WordTrace (prefixWord ++ tailWord_8272620) baseStart_8272620 baseEnd_8272620 := by
    simpa [prefixWord, tailWord_8272620, baseEnd_8272620] using wordTrace_append hprefix tailTrace_8272620
  have hstable : (prefixWord ++ tailWord_8272620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272620).length < 2 ^ (prefixWord ++ tailWord_8272620).sum := by decide
  have hdescent : baseEnd_8272620 < baseStart_8272620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272633 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_8272633 : Nat := 118140960795 + 8272633 * 2 ^ 59
def prefixEnd_8272633 : Nat := 4983230072969 + 3 ^ 40 * 8272633 * 2
def baseEnd_8272633 : Nat := 4247837007246037019042359

theorem tailTrace_8272633 : CollatzResearch.WordTrace tailWord_8272633 prefixEnd_8272633 4247837007246037019042359 := by
  unfold tailWord_8272633
  simp only [CollatzResearch.WordTrace]
  refine ⟨301727713438670969078518553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201151808959113979385679035 301727713438670969078518553)
  ·
    refine ⟨226295785079003226808888915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301727713438670969078518553 226295785079003226808888915)
    ·
      refine ⟨339443677618504840213333373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226295785079003226808888915 339443677618504840213333373)
      ·
        refine ⟨127291379106939315080000015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339443677618504840213333373 127291379106939315080000015)
        ·
          refine ⟨190937068660408972620000023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127291379106939315080000015 190937068660408972620000023)
          ·
            refine ⟨286405602990613458930000035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190937068660408972620000023 286405602990613458930000035)
            ·
              refine ⟨429608404485920188395000053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286405602990613458930000035 429608404485920188395000053)
              ·
                refine ⟨40275787920555017662031255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429608404485920188395000053 40275787920555017662031255)
                ·
                  refine ⟨60413681880832526493046883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40275787920555017662031255 60413681880832526493046883)
                  ·
                    refine ⟨90620522821248789739570325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60413681880832526493046883 90620522821248789739570325)
                    ·
                      refine ⟨4247837007246037019042359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90620522821248789739570325 4247837007246037019042359)
                      ·
                        rfl

theorem cell23_8272633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_8272633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272633 prefixEnd_8272633 := by exact prefixLift 8272633
  have htrace : WordTrace (prefixWord ++ tailWord_8272633) baseStart_8272633 baseEnd_8272633 := by
    simpa [prefixWord, tailWord_8272633, baseEnd_8272633] using wordTrace_append hprefix tailTrace_8272633
  have hstable : (prefixWord ++ tailWord_8272633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272633).length < 2 ^ (prefixWord ++ tailWord_8272633).sum := by decide
  have hdescent : baseEnd_8272633 < baseStart_8272633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272650 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_8272650 : Nat := 118140960795 + 8272650 * 2 ^ 59
def prefixEnd_8272650 : Nat := 4983230072969 + 3 ^ 40 * 8272650 * 2
def baseEnd_8272650 : Nat := 4247845736417163452529781

theorem tailTrace_8272650 : CollatzResearch.WordTrace tailWord_8272650 prefixEnd_8272650 4247845736417163452529781 := by
  unfold tailWord_8272650
  simp only [CollatzResearch.WordTrace]
  refine ⟨75432083369902345245471851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201152222319739587321258269 75432083369902345245471851)
  ·
    refine ⟨113148125054853517868207777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75432083369902345245471851 113148125054853517868207777)
    ·
      refine ⟨84861093791140138401155833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113148125054853517868207777 84861093791140138401155833)
      ·
        refine ⟨63645820343355103800866875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84861093791140138401155833 63645820343355103800866875)
        ·
          refine ⟨95468730515032655701300313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63645820343355103800866875 95468730515032655701300313)
          ·
            refine ⟨71601547886274491775975235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95468730515032655701300313 71601547886274491775975235)
            ·
              refine ⟨107402321829411737663962853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71601547886274491775975235 107402321829411737663962853)
              ·
                refine ⟨20137935343014700811993035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107402321829411737663962853 20137935343014700811993035)
                ·
                  refine ⟨30206903014522051217989553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20137935343014700811993035 30206903014522051217989553)
                  ·
                    refine ⟨22655177260891538413492165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30206903014522051217989553 22655177260891538413492165)
                    ·
                      refine ⟨4247845736417163452529781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22655177260891538413492165 4247845736417163452529781)
                      ·
                        rfl

theorem cell23_8272650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_8272650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272650 prefixEnd_8272650 := by exact prefixLift 8272650
  have htrace : WordTrace (prefixWord ++ tailWord_8272650) baseStart_8272650 baseEnd_8272650 := by
    simpa [prefixWord, tailWord_8272650, baseEnd_8272650] using wordTrace_append hprefix tailTrace_8272650
  have hstable : (prefixWord ++ tailWord_8272650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272650).length < 2 ^ (prefixWord ++ tailWord_8272650).sum := by decide
  have hdescent : baseEnd_8272650 < baseStart_8272650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272671 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 1, 2, 2]
def baseStart_8272671 : Nat := 118140960795 + 8272671 * 2 ^ 59
def prefixEnd_8272671 : Nat := 4983230072969 + 3 ^ 40 * 8272671 * 2
def baseEnd_8272671 : Nat := 4247856519510907870367185

theorem tailTrace_8272671 : CollatzResearch.WordTrace tailWord_8272671 prefixEnd_8272671 4247856519510907870367185 := by
  unfold tailWord_8272671
  simp only [CollatzResearch.WordTrace]
  refine ⟨301729099412533301568401867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201152732941688867712267911 301729099412533301568401867)
  ·
    refine ⟨452593649118799952352602801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301729099412533301568401867 452593649118799952352602801)
    ·
      refine ⟨339445236839099964264452101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452593649118799952352602801 339445236839099964264452101)
      ·
        refine ⟨63645981907331243299584769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339445236839099964264452101 63645981907331243299584769)
        ·
          refine ⟨47734486430498432474688577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63645981907331243299584769 47734486430498432474688577)
          ·
            refine ⟨35800864822873824356016433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47734486430498432474688577 35800864822873824356016433)
            ·
              refine ⟨26850648617155368267012325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35800864822873824356016433 26850648617155368267012325)
              ·
                refine ⟨5034496615716631550064811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26850648617155368267012325 5034496615716631550064811)
                ·
                  refine ⟨7551744923574947325097217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034496615716631550064811 7551744923574947325097217)
                  ·
                    refine ⟨5663808692681210493822913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7551744923574947325097217 5663808692681210493822913)
                    ·
                      refine ⟨4247856519510907870367185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663808692681210493822913 4247856519510907870367185)
                      ·
                        rfl

theorem cell23_8272671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_8272671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272671 prefixEnd_8272671 := by exact prefixLift 8272671
  have htrace : WordTrace (prefixWord ++ tailWord_8272671) baseStart_8272671 baseEnd_8272671 := by
    simpa [prefixWord, tailWord_8272671, baseEnd_8272671] using wordTrace_append hprefix tailTrace_8272671
  have hstable : (prefixWord ++ tailWord_8272671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272671).length < 2 ^ (prefixWord ++ tailWord_8272671).sum := by decide
  have hdescent : baseEnd_8272671 < baseStart_8272671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272683 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_8272683 : Nat := 118140960795 + 8272683 * 2 ^ 59
def prefixEnd_8272683 : Nat := 4983230072969 + 3 ^ 40 * 8272683 * 2
def baseEnd_8272683 : Nat := 4247862681278761823417129

theorem tailTrace_8272683 : CollatzResearch.WordTrace tailWord_8272683 prefixEnd_8272683 4247862681278761823417129 := by
  unfold tailWord_8272683
  simp only [CollatzResearch.WordTrace]
  refine ⟨301729537088489827617838703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201153024725659885078559135 301729537088489827617838703)
  ·
    refine ⟨452594305632734741426758055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301729537088489827617838703 452594305632734741426758055)
    ·
      refine ⟨678891458449102112140137083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452594305632734741426758055 678891458449102112140137083)
      ·
        refine ⟨1018337187673653168210205625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678891458449102112140137083 1018337187673653168210205625)
        ·
          refine ⟨763752890755239876157654219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018337187673653168210205625 763752890755239876157654219)
          ·
            refine ⟨1145629336132859814236481329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763752890755239876157654219 1145629336132859814236481329)
            ·
              refine ⟨859222002099644860677360997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145629336132859814236481329 859222002099644860677360997)
              ·
                refine ⟨161104125393683411377005187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 859222002099644860677360997 161104125393683411377005187)
                ·
                  refine ⟨241656188090525117065507781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161104125393683411377005187 241656188090525117065507781)
                  ·
                    refine ⟨45310535266973459449782709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241656188090525117065507781 45310535266973459449782709)
                    ·
                      refine ⟨4247862681278761823417129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45310535266973459449782709 4247862681278761823417129)
                      ·
                        rfl

theorem cell23_8272683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_8272683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272683 prefixEnd_8272683 := by exact prefixLift 8272683
  have htrace : WordTrace (prefixWord ++ tailWord_8272683) baseStart_8272683 baseEnd_8272683 := by
    simpa [prefixWord, tailWord_8272683, baseEnd_8272683] using wordTrace_append hprefix tailTrace_8272683
  have hstable : (prefixWord ++ tailWord_8272683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272683).length < 2 ^ (prefixWord ++ tailWord_8272683).sum := by decide
  have hdescent : baseEnd_8272683 < baseStart_8272683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272760 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_8272760 : Nat := 118140960795 + 8272760 * 2 ^ 59
def prefixEnd_8272760 : Nat := 4983230072969 + 3 ^ 40 * 8272760 * 2
def baseEnd_8272760 : Nat := 4247902219289158022154275

theorem tailTrace_8272760 : CollatzResearch.WordTrace tailWord_8272760 prefixEnd_8272760 4247902219289158022154275 := by
  unfold tailWord_8272760
  simp only [CollatzResearch.WordTrace]
  refine ⟨150866172754605434884195867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201154897006140579845594489 150866172754605434884195867)
  ·
    refine ⟨226299259131908152326293801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150866172754605434884195867 226299259131908152326293801)
    ·
      refine ⟨169724444348931114244720351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226299259131908152326293801 169724444348931114244720351)
      ·
        refine ⟨254586666523396671367080527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169724444348931114244720351 254586666523396671367080527)
        ·
          refine ⟨381879999785095007050620791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254586666523396671367080527 381879999785095007050620791)
          ·
            refine ⟨572819999677642510575931187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381879999785095007050620791 572819999677642510575931187)
            ·
              refine ⟨859229999516463765863896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572819999677642510575931187 859229999516463765863896781)
              ·
                refine ⟨322211249818673912198961293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859229999516463765863896781 322211249818673912198961293)
                ·
                  refine ⟨120829218682002717074610485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322211249818673912198961293 120829218682002717074610485)
                  ·
                    refine ⟨11327739251437754725744733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120829218682002717074610485 11327739251437754725744733)
                    ·
                      refine ⟨4247902219289158022154275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327739251437754725744733 4247902219289158022154275)
                      ·
                        rfl

theorem cell23_8272760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_8272760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272760 prefixEnd_8272760 := by exact prefixLift 8272760
  have htrace : WordTrace (prefixWord ++ tailWord_8272760) baseStart_8272760 baseEnd_8272760 := by
    simpa [prefixWord, tailWord_8272760, baseEnd_8272760] using wordTrace_append hprefix tailTrace_8272760
  have hstable : (prefixWord ++ tailWord_8272760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272760).length < 2 ^ (prefixWord ++ tailWord_8272760).sum := by decide
  have hdescent : baseEnd_8272760 < baseStart_8272760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272778 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_8272778 : Nat := 118140960795 + 8272778 * 2 ^ 59
def prefixEnd_8272778 : Nat := 4983230072969 + 3 ^ 40 * 8272778 * 2
def baseEnd_8272778 : Nat := 4247911461940938951729193

theorem tailTrace_8272778 : CollatzResearch.WordTrace tailWord_8272778 prefixEnd_8272778 4247911461940938951729193 := by
  unfold tailWord_8272778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75433250505786414710636747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201155334682097105895031325 75433250505786414710636747)
  ·
    refine ⟨113149875758679622065955121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75433250505786414710636747 113149875758679622065955121)
    ·
      refine ⟨84862406819009716549466341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113149875758679622065955121 84862406819009716549466341)
      ·
        refine ⟨15911701278564321853024939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84862406819009716549466341 15911701278564321853024939)
        ·
          refine ⟨23867551917846482779537409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15911701278564321853024939 23867551917846482779537409)
          ·
            refine ⟨17900663938384862084653057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23867551917846482779537409 17900663938384862084653057)
            ·
              refine ⟨13425497953788646563489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17900663938384862084653057 13425497953788646563489793)
              ·
                refine ⟨10069123465341484922617345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13425497953788646563489793 10069123465341484922617345)
                ·
                  refine ⟨7551842599006113691963009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069123465341484922617345 7551842599006113691963009)
                  ·
                    refine ⟨5663881949254585268972257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7551842599006113691963009 5663881949254585268972257)
                    ·
                      refine ⟨4247911461940938951729193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5663881949254585268972257 4247911461940938951729193)
                      ·
                        rfl

theorem cell23_8272778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_8272778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272778 prefixEnd_8272778 := by exact prefixLift 8272778
  have htrace : WordTrace (prefixWord ++ tailWord_8272778) baseStart_8272778 baseEnd_8272778 := by
    simpa [prefixWord, tailWord_8272778, baseEnd_8272778] using wordTrace_append hprefix tailTrace_8272778
  have hstable : (prefixWord ++ tailWord_8272778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272778).length < 2 ^ (prefixWord ++ tailWord_8272778).sum := by decide
  have hdescent : baseEnd_8272778 < baseStart_8272778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272794 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_8272794 : Nat := 118140960795 + 8272794 * 2 ^ 59
def prefixEnd_8272794 : Nat := 4983230072969 + 3 ^ 40 * 8272794 * 2
def baseEnd_8272794 : Nat := 4247919677631410889129119

theorem tailTrace_8272794 : CollatzResearch.WordTrace tailWord_8272794 prefixEnd_8272794 4247919677631410889129119 := by
  unfold tailWord_8272794
  simp only [CollatzResearch.WordTrace]
  refine ⟨75433396397771923393782359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201155723727391795716752957 75433396397771923393782359)
  ·
    refine ⟨113150094596657885090673539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75433396397771923393782359 113150094596657885090673539)
    ·
      refine ⟨169725141894986827636010309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113150094596657885090673539 169725141894986827636010309)
      ·
        refine ⟨31823464105310030181751933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169725141894986827636010309 31823464105310030181751933)
        ·
          refine ⟨11933799039491261318156975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31823464105310030181751933 11933799039491261318156975)
          ·
            refine ⟨17900698559236891977235463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933799039491261318156975 17900698559236891977235463)
            ·
              refine ⟨26851047838855337965853195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900698559236891977235463 26851047838855337965853195)
              ·
                refine ⟨40276571758283006948779793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26851047838855337965853195 40276571758283006948779793)
                ·
                  refine ⟨30207428818712255211584845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40276571758283006948779793 30207428818712255211584845)
                  ·
                    refine ⟨11327785807017095704344317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30207428818712255211584845 11327785807017095704344317)
                    ·
                      refine ⟨4247919677631410889129119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327785807017095704344317 4247919677631410889129119)
                      ·
                        rfl

theorem cell23_8272794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_8272794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272794 prefixEnd_8272794 := by exact prefixLift 8272794
  have htrace : WordTrace (prefixWord ++ tailWord_8272794) baseStart_8272794 baseEnd_8272794 := by
    simpa [prefixWord, tailWord_8272794, baseEnd_8272794] using wordTrace_append hprefix tailTrace_8272794
  have hstable : (prefixWord ++ tailWord_8272794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272794).length < 2 ^ (prefixWord ++ tailWord_8272794).sum := by decide
  have hdescent : baseEnd_8272794 < baseStart_8272794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272844 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_8272844 : Nat := 118140960795 + 8272844 * 2 ^ 59
def prefixEnd_8272844 : Nat := 4983230072969 + 3 ^ 40 * 8272844 * 2
def baseEnd_8272844 : Nat := 1415981783888045231167963

theorem tailTrace_8272844 : CollatzResearch.WordTrace tailWord_8272844 prefixEnd_8272844 1415981783888045231167963 := by
  unfold tailWord_8272844
  simp only [CollatzResearch.WordTrace]
  refine ⟨150867704620453276057224793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201156939493937701409633057 150867704620453276057224793)
  ·
    refine ⟨113150778465339957042918595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150867704620453276057224793 113150778465339957042918595)
    ·
      refine ⟨169726167698009935564377893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113150778465339957042918595 169726167698009935564377893)
      ·
        refine ⟨31823656443376862918320855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169726167698009935564377893 31823656443376862918320855)
        ·
          refine ⟨47735484665065294377481283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31823656443376862918320855 47735484665065294377481283)
          ·
            refine ⟨71603226997597941566221925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47735484665065294377481283 71603226997597941566221925)
            ·
              refine ⟨13425605062049614043666611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71603226997597941566221925 13425605062049614043666611)
              ·
                refine ⟨20138407593074421065499917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425605062049614043666611 20138407593074421065499917)
                ·
                  refine ⟨7551902847402907899562469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20138407593074421065499917 7551902847402907899562469)
                  ·
                    refine ⟨1415981783888045231167963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7551902847402907899562469 1415981783888045231167963)
                    ·
                      rfl

theorem cell23_8272844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_8272844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272844 prefixEnd_8272844 := by exact prefixLift 8272844
  have htrace : WordTrace (prefixWord ++ tailWord_8272844) baseStart_8272844 baseEnd_8272844 := by
    simpa [prefixWord, tailWord_8272844, baseEnd_8272844] using wordTrace_append hprefix tailTrace_8272844
  have hstable : (prefixWord ++ tailWord_8272844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272844).length < 2 ^ (prefixWord ++ tailWord_8272844).sum := by decide
  have hdescent : baseEnd_8272844 < baseStart_8272844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272867 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3]
def baseStart_8272867 : Nat := 118140960795 + 8272867 * 2 ^ 59
def prefixEnd_8272867 : Nat := 4983230072969 + 3 ^ 40 * 8272867 * 2
def baseEnd_8272867 : Nat := 4247957161719189103516283

theorem tailTrace_8272867 : CollatzResearch.WordTrace tailWord_8272867 prefixEnd_8272867 4247957161719189103516283 := by
  unfold tailWord_8272867
  simp only [CollatzResearch.WordTrace]
  refine ⟨301736248119823227042536855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201157498746548818028357903 301736248119823227042536855)
  ·
    refine ⟨452604372179734840563805283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301736248119823227042536855 452604372179734840563805283)
    ·
      refine ⟨678906558269602260845707925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452604372179734840563805283 678906558269602260845707925)
      ·
        refine ⟨31823744918887605977142559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 678906558269602260845707925 31823744918887605977142559)
        ·
          refine ⟨47735617378331408965713839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31823744918887605977142559 47735617378331408965713839)
          ·
            refine ⟨71603426067497113448570759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47735617378331408965713839 71603426067497113448570759)
            ·
              refine ⟨107405139101245670172856139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71603426067497113448570759 107405139101245670172856139)
              ·
                refine ⟨161107708651868505259284209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107405139101245670172856139 161107708651868505259284209)
                ·
                  refine ⟨120830781488901378944463157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161107708651868505259284209 120830781488901378944463157)
                  ·
                    refine ⟨11327885764584504276043421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120830781488901378944463157 11327885764584504276043421)
                    ·
                      refine ⟨4247957161719189103516283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11327885764584504276043421 4247957161719189103516283)
                      ·
                        rfl

theorem cell23_8272867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_8272867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272867 prefixEnd_8272867 := by exact prefixLift 8272867
  have htrace : WordTrace (prefixWord ++ tailWord_8272867) baseStart_8272867 baseEnd_8272867 := by
    simpa [prefixWord, tailWord_8272867, baseEnd_8272867] using wordTrace_append hprefix tailTrace_8272867
  have hstable : (prefixWord ++ tailWord_8272867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272867).length < 2 ^ (prefixWord ++ tailWord_8272867).sum := by decide
  have hdescent : baseEnd_8272867 < baseStart_8272867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8272938 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_8272938 : Nat := 118140960795 + 8272938 * 2 ^ 59
def prefixEnd_8272938 : Nat := 4983230072969 + 3 ^ 40 * 8272938 * 2
def baseEnd_8272938 : Nat := 1415997872948552775242819

theorem tailTrace_8272938 : CollatzResearch.WordTrace tailWord_8272938 prefixEnd_8272938 1415997872948552775242819 := by
  unfold tailWord_8272938
  simp only [CollatzResearch.WordTrace]
  refine ⟨75434709425641501542092867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201159225135044004112247645 75434709425641501542092867)
  ·
    refine ⟨113152064138462252313139301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75434709425641501542092867 113152064138462252313139301)
    ·
      refine ⟨21216012025961672308713619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113152064138462252313139301 21216012025961672308713619)
      ·
        refine ⟨31824018038942508463070429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216012025961672308713619 31824018038942508463070429)
        ·
          refine ⟨11934006764603440673651411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31824018038942508463070429 11934006764603440673651411)
          ·
            refine ⟨17901010146905161010477117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934006764603440673651411 17901010146905161010477117)
            ·
              refine ⟨6712878805089435378928919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17901010146905161010477117 6712878805089435378928919)
              ·
                refine ⟨10069318207634153068393379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712878805089435378928919 10069318207634153068393379)
                ·
                  refine ⟨15103977311451229602590069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10069318207634153068393379 15103977311451229602590069)
                  ·
                    refine ⟨1415997872948552775242819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15103977311451229602590069 1415997872948552775242819)
                    ·
                      rfl

theorem cell23_8272938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_8272938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8272938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8272938 prefixEnd_8272938 := by exact prefixLift 8272938
  have htrace : WordTrace (prefixWord ++ tailWord_8272938) baseStart_8272938 baseEnd_8272938 := by
    simpa [prefixWord, tailWord_8272938, baseEnd_8272938] using wordTrace_append hprefix tailTrace_8272938
  have hstable : (prefixWord ++ tailWord_8272938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8272938).length < 2 ^ (prefixWord ++ tailWord_8272938).sum := by decide
  have hdescent : baseEnd_8272938 < baseStart_8272938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8272938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273007 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 6]
def baseStart_8273007 : Nat := 118140960795 + 8273007 * 2 ^ 59
def prefixEnd_8273007 : Nat := 4983230072969 + 3 ^ 40 * 8273007 * 2
def baseEnd_8273007 : Nat := 1416009683003606185255213

theorem tailTrace_8273007 : CollatzResearch.WordTrace tailWord_8273007 prefixEnd_8273007 1416009683003606185255213 := by
  unfold tailWord_8273007
  simp only [CollatzResearch.WordTrace]
  refine ⟨301741354339316030952633275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201160902892877353968422183 301741354339316030952633275)
  ·
    refine ⟨452612031508974046428949913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301741354339316030952633275 452612031508974046428949913)
    ·
      refine ⟨339459023631730534821712435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452612031508974046428949913 339459023631730534821712435)
      ·
        refine ⟨509188535447595802232568653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339459023631730534821712435 509188535447595802232568653)
        ·
          refine ⟨190945700792848425837213245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509188535447595802232568653 190945700792848425837213245)
          ·
            refine ⟨71604637797318159688954967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190945700792848425837213245 71604637797318159688954967)
            ·
              refine ⟨107406956695977239533432451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71604637797318159688954967 107406956695977239533432451)
              ·
                refine ⟨161110435043965859300148677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107406956695977239533432451 161110435043965859300148677)
                ·
                  refine ⟨30208206570743598618777877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161110435043965859300148677 30208206570743598618777877)
                  ·
                    refine ⟨1416009683003606185255213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30208206570743598618777877 1416009683003606185255213)
                    ·
                      rfl

theorem cell23_8273007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_8273007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273007 prefixEnd_8273007 := by exact prefixLift 8273007
  have htrace : WordTrace (prefixWord ++ tailWord_8273007) baseStart_8273007 baseEnd_8273007 := by
    simpa [prefixWord, tailWord_8273007, baseEnd_8273007] using wordTrace_append hprefix tailTrace_8273007
  have hstable : (prefixWord ++ tailWord_8273007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273007).length < 2 ^ (prefixWord ++ tailWord_8273007).sum := by decide
  have hdescent : baseEnd_8273007 < baseStart_8273007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273022 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_8273022 : Nat := 118140960795 + 8273022 * 2 ^ 59
def prefixEnd_8273022 : Nat := 4983230072969 + 3 ^ 40 * 8273022 * 2
def baseEnd_8273022 : Nat := 4248036751220635997078071

theorem tailTrace_8273022 : CollatzResearch.WordTrace tailWord_8273022 prefixEnd_8273022 4248036751220635997078071 := by
  unfold tailWord_8273022
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717737679282711064303665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201161267622841125676286213 37717737679282711064303665)
  ·
    refine ⟨28288303259462033298227749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37717737679282711064303665 28288303259462033298227749)
    ·
      refine ⟨5304056861149131243417703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28288303259462033298227749 5304056861149131243417703)
      ·
        refine ⟨7956085291723696865126555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304056861149131243417703 7956085291723696865126555)
        ·
          refine ⟨11934127937585545297689833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956085291723696865126555 11934127937585545297689833)
          ·
            refine ⟨8950595953189158973267375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11934127937585545297689833 8950595953189158973267375)
            ·
              refine ⟨13425893929783738459901063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950595953189158973267375 13425893929783738459901063)
              ·
                refine ⟨20138840894675607689851595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425893929783738459901063 20138840894675607689851595)
                ·
                  refine ⟨30208261342013411534777393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20138840894675607689851595 30208261342013411534777393)
                  ·
                    refine ⟨22656196006510058651083045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30208261342013411534777393 22656196006510058651083045)
                    ·
                      refine ⟨4248036751220635997078071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22656196006510058651083045 4248036751220635997078071)
                      ·
                        rfl

theorem cell23_8273022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_8273022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273022 prefixEnd_8273022 := by exact prefixLift 8273022
  have htrace : WordTrace (prefixWord ++ tailWord_8273022) baseStart_8273022 baseEnd_8273022 := by
    simpa [prefixWord, tailWord_8273022, baseEnd_8273022] using wordTrace_append hprefix tailTrace_8273022
  have hstable : (prefixWord ++ tailWord_8273022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273022).length < 2 ^ (prefixWord ++ tailWord_8273022).sum := by decide
  have hdescent : baseEnd_8273022 < baseStart_8273022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273025 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_8273025 : Nat := 118140960795 + 8273025 * 2 ^ 59
def prefixEnd_8273025 : Nat := 4983230072969 + 3 ^ 40 * 8273025 * 2
def baseEnd_8273025 : Nat := 4248038291662599485340557

theorem tailTrace_8273025 : CollatzResearch.WordTrace tailWord_8273025 prefixEnd_8273025 4248038291662599485340557 := by
  unfold tailWord_8273025
  simp only [CollatzResearch.WordTrace]
  refine ⟨301742010853250820026788529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201161340568833880017859019 301742010853250820026788529)
  ·
    refine ⟨226306508139938115020091397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301742010853250820026788529 226306508139938115020091397)
    ·
      refine ⟨42432470276238396566267137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226306508139938115020091397 42432470276238396566267137)
      ·
        refine ⟨31824352707178797424700353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42432470276238396566267137 31824352707178797424700353)
        ·
          refine ⟨23868264530384098068525265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31824352707178797424700353 23868264530384098068525265)
          ·
            refine ⟨17901198397788073551393949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23868264530384098068525265 17901198397788073551393949)
            ·
              refine ⟨6712949399170527581772731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17901198397788073551393949 6712949399170527581772731)
              ·
                refine ⟨10069424098755791372659097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712949399170527581772731 10069424098755791372659097)
                ·
                  refine ⟨7552068074066843529494323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069424098755791372659097 7552068074066843529494323)
                  ·
                    refine ⟨11328102111100265294241485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7552068074066843529494323 11328102111100265294241485)
                    ·
                      refine ⟨4248038291662599485340557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328102111100265294241485 4248038291662599485340557)
                      ·
                        rfl

theorem cell23_8273025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_8273025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273025 prefixEnd_8273025 := by exact prefixLift 8273025
  have htrace : WordTrace (prefixWord ++ tailWord_8273025) baseStart_8273025 baseEnd_8273025 := by
    simpa [prefixWord, tailWord_8273025, baseEnd_8273025] using wordTrace_append hprefix tailTrace_8273025
  have hstable : (prefixWord ++ tailWord_8273025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273025).length < 2 ^ (prefixWord ++ tailWord_8273025).sum := by decide
  have hdescent : baseEnd_8273025 < baseStart_8273025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273034 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_8273034 : Nat := 118140960795 + 8273034 * 2 ^ 59
def prefixEnd_8273034 : Nat := 4983230072969 + 3 ^ 40 * 8273034 * 2
def baseEnd_8273034 : Nat := 4248042912988489950128015

theorem tailTrace_8273034 : CollatzResearch.WordTrace tailWord_8273034 prefixEnd_8273034 4248042912988489950128015 := by
  unfold tailWord_8273034
  simp only [CollatzResearch.WordTrace]
  refine ⟨75435584777554553640966539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201161559406812143042577437 75435584777554553640966539)
  ·
    refine ⟨113153377166331830461449809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75435584777554553640966539 113153377166331830461449809)
    ·
      refine ⟨84865032874748872846087357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113153377166331830461449809 84865032874748872846087357)
      ·
        refine ⟨31824387328030827317282759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84865032874748872846087357 31824387328030827317282759)
        ·
          refine ⟨47736580992046240975924139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824387328030827317282759 47736580992046240975924139)
          ·
            refine ⟨71604871488069361463886209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47736580992046240975924139 71604871488069361463886209)
            ·
              refine ⟨53703653616052021097914657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71604871488069361463886209 53703653616052021097914657)
              ·
                refine ⟨40277740212039015823435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53703653616052021097914657 40277740212039015823435993)
                ·
                  refine ⟨30208305159029261867576995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40277740212039015823435993 30208305159029261867576995)
                  ·
                    refine ⟨45312457738543892801365493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30208305159029261867576995 45312457738543892801365493)
                    ·
                      refine ⟨4248042912988489950128015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45312457738543892801365493 4248042912988489950128015)
                      ·
                        rfl

theorem cell23_8273034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_8273034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273034 prefixEnd_8273034 := by exact prefixLift 8273034
  have htrace : WordTrace (prefixWord ++ tailWord_8273034) baseStart_8273034 baseEnd_8273034 := by
    simpa [prefixWord, tailWord_8273034, baseEnd_8273034] using wordTrace_append hprefix tailTrace_8273034
  have hstable : (prefixWord ++ tailWord_8273034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273034).length < 2 ^ (prefixWord ++ tailWord_8273034).sum := by decide
  have hdescent : baseEnd_8273034 < baseStart_8273034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273048 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_8273048 : Nat := 118140960795 + 8273048 * 2 ^ 59
def prefixEnd_8273048 : Nat := 4983230072969 + 3 ^ 40 * 8273048 * 2
def baseEnd_8273048 : Nat := 4248050101717652895352951

theorem tailTrace_8273048 : CollatzResearch.WordTrace tailWord_8273048 prefixEnd_8273048 4248050101717652895352951 := by
  unfold tailWord_8273048
  simp only [CollatzResearch.WordTrace]
  refine ⟨150871424866083747477437899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201161899821444996636583865 150871424866083747477437899)
  ·
    refine ⟨226307137299125621216156849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150871424866083747477437899 226307137299125621216156849)
    ·
      refine ⟨169730352974344215912117637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226307137299125621216156849 169730352974344215912117637)
      ·
        refine ⟨31824441182689540483522057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169730352974344215912117637 31824441182689540483522057)
        ·
          refine ⟨23868330887017155362641543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31824441182689540483522057 23868330887017155362641543)
          ·
            refine ⟨35802496330525733043962315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23868330887017155362641543 35802496330525733043962315)
            ·
              refine ⟨53703744495788599565943473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35802496330525733043962315 53703744495788599565943473)
              ·
                refine ⟨40277808371841449674457605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53703744495788599565943473 40277808371841449674457605)
                ·
                  refine ⟨7552089069720271813960801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40277808371841449674457605 7552089069720271813960801)
                  ·
                    refine ⟨5664066802290203860470601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7552089069720271813960801 5664066802290203860470601)
                    ·
                      refine ⟨4248050101717652895352951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664066802290203860470601 4248050101717652895352951)
                      ·
                        rfl

theorem cell23_8273048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_8273048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273048 prefixEnd_8273048 := by exact prefixLift 8273048
  have htrace : WordTrace (prefixWord ++ tailWord_8273048) baseStart_8273048 baseEnd_8273048 := by
    simpa [prefixWord, tailWord_8273048, baseEnd_8273048] using wordTrace_append hprefix tailTrace_8273048
  have hstable : (prefixWord ++ tailWord_8273048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273048).length < 2 ^ (prefixWord ++ tailWord_8273048).sum := by decide
  have hdescent : baseEnd_8273048 < baseStart_8273048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273121 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_8273121 : Nat := 118140960795 + 8273121 * 2 ^ 59
def prefixEnd_8273121 : Nat := 4983230072969 + 3 ^ 40 * 8273121 * 2
def baseEnd_8273121 : Nat := 4248087585805431109740115

theorem tailTrace_8273121 : CollatzResearch.WordTrace tailWord_8273121 prefixEnd_8273121 4248087585805431109740115 := by
  unfold tailWord_8273121
  simp only [CollatzResearch.WordTrace]
  refine ⟨301745512260903028422283217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201163674840602018948188811 301745512260903028422283217)
  ·
    refine ⟨226309134195677271316712413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301745512260903028422283217 226309134195677271316712413)
    ·
      refine ⟨84865925323378976743767155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226309134195677271316712413 84865925323378976743767155)
      ·
        refine ⟨127298887985068465115650733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84865925323378976743767155 127298887985068465115650733)
        ·
          refine ⟨47737082994400674418369025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127298887985068465115650733 47737082994400674418369025)
          ·
            refine ⟨35802812245800505813776769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47737082994400674418369025 35802812245800505813776769)
            ·
              refine ⟨26852109184350379360332577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35802812245800505813776769 26852109184350379360332577)
              ·
                refine ⟨20139081888262784520249433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26852109184350379360332577 20139081888262784520249433)
                ·
                  refine ⟨15104311416197088390187075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20139081888262784520249433 15104311416197088390187075)
                  ·
                    refine ⟨22656467124295632585280613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15104311416197088390187075 22656467124295632585280613)
                    ·
                      refine ⟨4248087585805431109740115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22656467124295632585280613 4248087585805431109740115)
                      ·
                        rfl

theorem cell23_8273121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_8273121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273121 prefixEnd_8273121 := by exact prefixLift 8273121
  have htrace : WordTrace (prefixWord ++ tailWord_8273121) baseStart_8273121 baseEnd_8273121 := by
    simpa [prefixWord, tailWord_8273121, baseEnd_8273121] using wordTrace_append hprefix tailTrace_8273121
  have hstable : (prefixWord ++ tailWord_8273121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273121).length < 2 ^ (prefixWord ++ tailWord_8273121).sum := by decide
  have hdescent : baseEnd_8273121 < baseStart_8273121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273148 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_8273148 : Nat := 118140960795 + 8273148 * 2 ^ 59
def prefixEnd_8273148 : Nat := 4983230072969 + 3 ^ 40 * 8273148 * 2
def baseEnd_8273148 : Nat := 1416033816594367501367497

theorem tailTrace_8273148 : CollatzResearch.WordTrace tailWord_8273148 prefixEnd_8273148 1416033816594367501367497 := by
  unfold tailWord_8273148
  simp only [CollatzResearch.WordTrace]
  refine ⟨150873248515902606016758049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201164331354536808022344065 150873248515902606016758049)
  ·
    refine ⟨113154936386926954512568537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150873248515902606016758049 113154936386926954512568537)
    ·
      refine ⟨84866202290195215884426403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113154936386926954512568537 84866202290195215884426403)
      ·
        refine ⟨127299303435292823826639605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84866202290195215884426403 127299303435292823826639605)
        ·
          refine ⟨11934309697058702233747463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127299303435292823826639605 11934309697058702233747463)
          ·
            refine ⟨17901464545588053350621195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934309697058702233747463 17901464545588053350621195)
            ·
              refine ⟨26852196818382080025931793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17901464545588053350621195 26852196818382080025931793)
              ·
                refine ⟨20139147613786560019448845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26852196818382080025931793 20139147613786560019448845)
                ·
                  refine ⟨7552180355169960007293317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20139147613786560019448845 7552180355169960007293317)
                  ·
                    refine ⟨1416033816594367501367497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7552180355169960007293317 1416033816594367501367497)
                    ·
                      rfl

theorem cell23_8273148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_8273148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273148 prefixEnd_8273148 := by exact prefixLift 8273148
  have htrace : WordTrace (prefixWord ++ tailWord_8273148) baseStart_8273148 baseEnd_8273148 := by
    simpa [prefixWord, tailWord_8273148, baseEnd_8273148] using wordTrace_append hprefix tailTrace_8273148
  have hstable : (prefixWord ++ tailWord_8273148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273148).length < 2 ^ (prefixWord ++ tailWord_8273148).sum := by decide
  have hdescent : baseEnd_8273148 < baseStart_8273148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273178 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 6]
def baseStart_8273178 : Nat := 118140960795 + 8273178 * 2 ^ 59
def prefixEnd_8273178 : Nat := 4983230072969 + 3 ^ 40 * 8273178 * 2
def baseEnd_8273178 : Nat := 472012983800304154080817

theorem tailTrace_8273178 : CollatzResearch.WordTrace tailWord_8273178 prefixEnd_8273178 472012983800304154080817 := by
  unfold tailWord_8273178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75436897805424131789277047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201165060814464351438072125 75436897805424131789277047)
  ·
    refine ⟨113155346708136197683915571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75436897805424131789277047 113155346708136197683915571)
    ·
      refine ⟨169733020062204296525873357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113155346708136197683915571 169733020062204296525873357)
      ·
        refine ⟨63649882523326611197202509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169733020062204296525873357 63649882523326611197202509)
        ·
          refine ⟨23868705946247479198950941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63649882523326611197202509 23868705946247479198950941)
          ·
            refine ⟨8950764729842804699606603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23868705946247479198950941 8950764729842804699606603)
            ·
              refine ⟨13426147094764207049409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950764729842804699606603 13426147094764207049409905)
              ·
                refine ⟨10069610321073155287057429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13426147094764207049409905 10069610321073155287057429)
                ·
                  refine ⟨472012983800304154080817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10069610321073155287057429 472012983800304154080817)
                  ·
                    rfl

theorem cell23_8273178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_8273178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273178 prefixEnd_8273178 := by exact prefixLift 8273178
  have htrace : WordTrace (prefixWord ++ tailWord_8273178) baseStart_8273178 baseEnd_8273178 := by
    simpa [prefixWord, tailWord_8273178, baseEnd_8273178] using wordTrace_append hprefix tailTrace_8273178
  have hstable : (prefixWord ++ tailWord_8273178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273178).length < 2 ^ (prefixWord ++ tailWord_8273178).sum := by decide
  have hdescent : baseEnd_8273178 < baseStart_8273178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273181 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_8273181 : Nat := 118140960795 + 8273181 * 2 ^ 59
def prefixEnd_8273181 : Nat := 4983230072969 + 3 ^ 40 * 8273181 * 2
def baseEnd_8273181 : Nat := 4248118394644700874989839

theorem tailTrace_8273181 : CollatzResearch.WordTrace tailWord_8273181 prefixEnd_8273181 4248118394644700874989839 := by
  unfold tailWord_8273181
  simp only [CollatzResearch.WordTrace]
  refine ⟨301747700640685658669467397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201165133760457105779644931 301747700640685658669467397)
  ·
    refine ⟨56577693870128561000525137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301747700640685658669467397 56577693870128561000525137)
    ·
      refine ⟨42433270402596420750393853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56577693870128561000525137 42433270402596420750393853)
      ·
        refine ⟨15912476400973657781397695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42433270402596420750393853 15912476400973657781397695)
        ·
          refine ⟨23868714601460486672096543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912476400973657781397695 23868714601460486672096543)
          ·
            refine ⟨35803071902190730008144815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23868714601460486672096543 35803071902190730008144815)
            ·
              refine ⟨53704607853286095012217223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35803071902190730008144815 53704607853286095012217223)
              ·
                refine ⟨80556911779929142518325835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53704607853286095012217223 80556911779929142518325835)
                ·
                  refine ⟨120835367669893713777488753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80556911779929142518325835 120835367669893713777488753)
                  ·
                    refine ⟨90626525752420285333116565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120835367669893713777488753 90626525752420285333116565)
                    ·
                      refine ⟨4248118394644700874989839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90626525752420285333116565 4248118394644700874989839)
                      ·
                        rfl

theorem cell23_8273181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_8273181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273181 prefixEnd_8273181 := by exact prefixLift 8273181
  have htrace : WordTrace (prefixWord ++ tailWord_8273181) baseStart_8273181 baseEnd_8273181 := by
    simpa [prefixWord, tailWord_8273181, baseEnd_8273181] using wordTrace_append hprefix tailTrace_8273181
  have hstable : (prefixWord ++ tailWord_8273181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273181).length < 2 ^ (prefixWord ++ tailWord_8273181).sum := by decide
  have hdescent : baseEnd_8273181 < baseStart_8273181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273182 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_8273182 : Nat := 118140960795 + 8273182 * 2 ^ 59
def prefixEnd_8273182 : Nat := 4983230072969 + 3 ^ 40 * 8273182 * 2
def baseEnd_8273182 : Nat := 1416039636041785123692445

theorem tailTrace_8273182 : CollatzResearch.WordTrace tailWord_8273182 prefixEnd_8273182 1416039636041785123692445 := by
  unfold tailWord_8273182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718467139210254480031725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201165158075788023893502533 37718467139210254480031725)
  ·
    refine ⟨14144425177203845430011897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37718467139210254480031725 14144425177203845430011897)
    ·
      refine ⟨10608318882902884072508923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144425177203845430011897 10608318882902884072508923)
      ·
        refine ⟨15912478324354326108763385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608318882902884072508923 15912478324354326108763385)
        ·
          refine ⟨11934358743265744581572539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15912478324354326108763385 11934358743265744581572539)
          ·
            refine ⟨17901538114898616872358809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934358743265744581572539 17901538114898616872358809)
            ·
              refine ⟨13426153586173962654269107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17901538114898616872358809 13426153586173962654269107)
              ·
                refine ⟨20139230379260943981403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426153586173962654269107 20139230379260943981403661)
                ·
                  refine ⟨7552211392222853993026373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20139230379260943981403661 7552211392222853993026373)
                  ·
                    refine ⟨1416039636041785123692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7552211392222853993026373 1416039636041785123692445)
                    ·
                      rfl

theorem cell23_8273182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_8273182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273182 prefixEnd_8273182 := by exact prefixLift 8273182
  have htrace : WordTrace (prefixWord ++ tailWord_8273182) baseStart_8273182 baseEnd_8273182 := by
    simpa [prefixWord, tailWord_8273182, baseEnd_8273182] using wordTrace_append hprefix tailTrace_8273182
  have hstable : (prefixWord ++ tailWord_8273182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273182).length < 2 ^ (prefixWord ++ tailWord_8273182).sum := by decide
  have hdescent : baseEnd_8273182 < baseStart_8273182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273228 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_8273228 : Nat := 118140960795 + 8273228 * 2 ^ 59
def prefixEnd_8273228 : Nat := 4983230072969 + 3 ^ 40 * 8273228 * 2
def baseEnd_8273228 : Nat := 4248142528235462191102123

theorem tailTrace_8273228 : CollatzResearch.WordTrace tailWord_8273228 prefixEnd_8273228 4248142528235462191102123 := by
  unfold tailWord_8273228
  simp only [CollatzResearch.WordTrace]
  refine ⟨150874707435757692848214169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201166276581010257130952225 150874707435757692848214169)
  ·
    refine ⟨113156030576818269636160627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150874707435757692848214169 113156030576818269636160627)
    ·
      refine ⟨169734045865227404454240941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113156030576818269636160627 169734045865227404454240941)
      ·
        refine ⟨63650267199460276670340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169734045865227404454240941 63650267199460276670340353)
        ·
          refine ⟨47737700399595207502755265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63650267199460276670340353 47737700399595207502755265)
          ·
            refine ⟨35803275299696405627066449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47737700399595207502755265 35803275299696405627066449)
            ·
              refine ⟨26852456474772304220299837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35803275299696405627066449 26852456474772304220299837)
              ·
                refine ⟨10069671178039614082612439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26852456474772304220299837 10069671178039614082612439)
                ·
                  refine ⟨15104506767059421123918659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10069671178039614082612439 15104506767059421123918659)
                  ·
                    refine ⟨22656760150589131685877989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15104506767059421123918659 22656760150589131685877989)
                    ·
                      refine ⟨4248142528235462191102123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22656760150589131685877989 4248142528235462191102123)
                      ·
                        rfl

theorem cell23_8273228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_8273228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273228 prefixEnd_8273228 := by exact prefixLift 8273228
  have htrace : WordTrace (prefixWord ++ tailWord_8273228) baseStart_8273228 baseEnd_8273228 := by
    simpa [prefixWord, tailWord_8273228, baseEnd_8273228] using wordTrace_append hprefix tailTrace_8273228
  have hstable : (prefixWord ++ tailWord_8273228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273228).length < 2 ^ (prefixWord ++ tailWord_8273228).sum := by decide
  have hdescent : baseEnd_8273228 < baseStart_8273228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273251 : List Nat := [1, 1, 1, 5, 2, 3, 2, 8]
def baseStart_8273251 : Nat := 118140960795 + 8273251 * 2 ^ 59
def prefixEnd_8273251 : Nat := 4983230072969 + 3 ^ 40 * 8273251 * 2
def baseEnd_8273251 : Nat := 157339049566315392633871

theorem tailTrace_8273251 : CollatzResearch.WordTrace tailWord_8273251 prefixEnd_8273251 157339049566315392633871 := by
  unfold tailWord_8273251
  simp only [CollatzResearch.WordTrace]
  refine ⟨301750253750432060624515607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201166835833621373749677071 301750253750432060624515607)
  ·
    refine ⟨452625380625648090936773411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301750253750432060624515607 452625380625648090936773411)
    ·
      refine ⟨678938070938472136405160117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452625380625648090936773411 678938070938472136405160117)
      ·
        refine ⟨63650444150481762787983761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 678938070938472136405160117 63650444150481762787983761)
        ·
          refine ⟨47737833112861322090987821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63650444150481762787983761 47737833112861322090987821)
          ·
            refine ⟨17901687417322995784120433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47737833112861322090987821 17901687417322995784120433)
            ·
              refine ⟨13426265562992246838090325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17901687417322995784120433 13426265562992246838090325)
              ·
                refine ⟨157339049566315392633871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13426265562992246838090325 157339049566315392633871)
                ·
                  rfl

theorem cell23_8273251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 8].length) (baseStart_8273251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273251 prefixEnd_8273251 := by exact prefixLift 8273251
  have htrace : WordTrace (prefixWord ++ tailWord_8273251) baseStart_8273251 baseEnd_8273251 := by
    simpa [prefixWord, tailWord_8273251, baseEnd_8273251] using wordTrace_append hprefix tailTrace_8273251
  have hstable : (prefixWord ++ tailWord_8273251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273251).length < 2 ^ (prefixWord ++ tailWord_8273251).sum := by decide
  have hdescent : baseEnd_8273251 < baseStart_8273251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273255 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 2, 4]
def baseStart_8273255 : Nat := 118140960795 + 8273255 * 2 ^ 59
def prefixEnd_8273255 : Nat := 4983230072969 + 3 ^ 40 * 8273255 * 2
def baseEnd_8273255 : Nat := 1416052130737711195154833

theorem tailTrace_8273255 : CollatzResearch.WordTrace tailWord_8273255 prefixEnd_8273255 1416052130737711195154833 := by
  unfold tailWord_8273255
  simp only [CollatzResearch.WordTrace]
  refine ⟨301750399642417569307661219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201166933094945046205107479 301750399642417569307661219)
  ·
    refine ⟨452625599463626353961491829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301750399642417569307661219 452625599463626353961491829)
    ·
      refine ⟨42433649949714970683889859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452625599463626353961491829 42433649949714970683889859)
      ·
        refine ⟨63650474924572456025834789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42433649949714970683889859 63650474924572456025834789)
        ·
          refine ⟨11934464048357335504844023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63650474924572456025834789 11934464048357335504844023)
          ·
            refine ⟨17901696072536003257266035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934464048357335504844023 17901696072536003257266035)
            ·
              refine ⟨26852544108804004885899053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17901696072536003257266035 26852544108804004885899053)
              ·
                refine ⟨10069704040801501832212145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26852544108804004885899053 10069704040801501832212145)
                ·
                  refine ⟨7552278030601126374159109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069704040801501832212145 7552278030601126374159109)
                  ·
                    refine ⟨1416052130737711195154833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7552278030601126374159109 1416052130737711195154833)
                    ·
                      rfl

theorem cell23_8273255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_8273255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273255 prefixEnd_8273255 := by exact prefixLift 8273255
  have htrace : WordTrace (prefixWord ++ tailWord_8273255) baseStart_8273255 baseEnd_8273255 := by
    simpa [prefixWord, tailWord_8273255, baseEnd_8273255] using wordTrace_append hprefix tailTrace_8273255
  have hstable : (prefixWord ++ tailWord_8273255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273255).length < 2 ^ (prefixWord ++ tailWord_8273255).sum := by decide
  have hdescent : baseEnd_8273255 < baseStart_8273255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273282 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_8273282 : Nat := 118140960795 + 8273282 * 2 ^ 59
def prefixEnd_8273282 : Nat := 4983230072969 + 3 ^ 40 * 8273282 * 2
def baseEnd_8273282 : Nat := 4248170256190804979826875

theorem tailTrace_8273282 : CollatzResearch.WordTrace tailWord_8273282 prefixEnd_8273282 4248170256190804979826875 := by
  unfold tailWord_8273282
  simp only [CollatzResearch.WordTrace]
  refine ⟨75437846103329938229723525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201167589608879835279262733 75437846103329938229723525)
  ·
    refine ⟨14144596144374363418073161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75437846103329938229723525 14144596144374363418073161)
    ·
      refine ⟨10608447108280772563554871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144596144374363418073161 10608447108280772563554871)
      ·
        refine ⟨15912670662421158845332307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608447108280772563554871 15912670662421158845332307)
        ·
          refine ⟨23869005993631738267998461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912670662421158845332307 23869005993631738267998461)
          ·
            refine ⟨8950877247611901850499423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23869005993631738267998461 8950877247611901850499423)
            ·
              refine ⟨13426315871417852775749135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950877247611901850499423 13426315871417852775749135)
              ·
                refine ⟨20139473807126779163623703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426315871417852775749135 20139473807126779163623703)
                ·
                  refine ⟨30209210710690168745435555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20139473807126779163623703 30209210710690168745435555)
                  ·
                    refine ⟨45313816066035253118153333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30209210710690168745435555 45313816066035253118153333)
                    ·
                      refine ⟨4248170256190804979826875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45313816066035253118153333 4248170256190804979826875)
                      ·
                        rfl

theorem cell23_8273282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_8273282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273282 prefixEnd_8273282 := by exact prefixLift 8273282
  have htrace : WordTrace (prefixWord ++ tailWord_8273282) baseStart_8273282 baseEnd_8273282 := by
    simpa [prefixWord, tailWord_8273282, baseEnd_8273282] using wordTrace_append hprefix tailTrace_8273282
  have hstable : (prefixWord ++ tailWord_8273282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273282).length < 2 ^ (prefixWord ++ tailWord_8273282).sum := by decide
  have hdescent : baseEnd_8273282 < baseStart_8273282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273301 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_8273301 : Nat := 118140960795 + 8273301 * 2 ^ 59
def prefixEnd_8273301 : Nat := 4983230072969 + 3 ^ 40 * 8273301 * 2
def baseEnd_8273301 : Nat := 4248180012323240405489287

theorem tailTrace_8273301 : CollatzResearch.WordTrace tailWord_8273301 prefixEnd_8273301 4248180012323240405489287 := by
  unfold tailWord_8273301
  simp only [CollatzResearch.WordTrace]
  refine ⟨301752077400250919163835757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201168051600167279442557171 301752077400250919163835757)
  ·
    refine ⟨113157029025094094686438409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301752077400250919163835757 113157029025094094686438409)
    ·
      refine ⟨84867771768820571014828807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113157029025094094686438409 84867771768820571014828807)
      ·
        refine ⟨127301657653230856522243211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84867771768820571014828807 127301657653230856522243211)
        ·
          refine ⟨190952486479846284783364817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127301657653230856522243211 190952486479846284783364817)
          ·
            refine ⟨143214364859884713587523613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190952486479846284783364817 143214364859884713587523613)
            ·
              refine ⟨53705386822456767595321355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143214364859884713587523613 53705386822456767595321355)
              ·
                refine ⟨80558080233685151392982033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53705386822456767595321355 80558080233685151392982033)
                ·
                  refine ⟨60418560175263863544736525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80558080233685151392982033 60418560175263863544736525)
                  ·
                    refine ⟨22656960065723948829276197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60418560175263863544736525 22656960065723948829276197)
                    ·
                      refine ⟨4248180012323240405489287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22656960065723948829276197 4248180012323240405489287)
                      ·
                        rfl

theorem cell23_8273301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_8273301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273301 prefixEnd_8273301 := by exact prefixLift 8273301
  have htrace : WordTrace (prefixWord ++ tailWord_8273301) baseStart_8273301 baseEnd_8273301 := by
    simpa [prefixWord, tailWord_8273301, baseEnd_8273301] using wordTrace_append hprefix tailTrace_8273301
  have hstable : (prefixWord ++ tailWord_8273301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273301).length < 2 ^ (prefixWord ++ tailWord_8273301).sum := by decide
  have hdescent : baseEnd_8273301 < baseStart_8273301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273311 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 8]
def baseStart_8273311 : Nat := 118140960795 + 8273311 * 2 ^ 59
def prefixEnd_8273311 : Nat := 4983230072969 + 3 ^ 40 * 8273311 * 2
def baseEnd_8273311 : Nat := 1416061715709928455454747

theorem tailTrace_8273311 : CollatzResearch.WordTrace tailWord_8273311 prefixEnd_8273311 1416061715709928455454747 := by
  unfold tailWord_8273311
  simp only [CollatzResearch.WordTrace]
  refine ⟨301752442130214690871699787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201168294753476460581133191 301752442130214690871699787)
  ·
    refine ⟨452628663195322036307549681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301752442130214690871699787 452628663195322036307549681)
    ·
      refine ⟨339471497396491527230662261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452628663195322036307549681 339471497396491527230662261)
      ·
        refine ⟨31825452880921080677874587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339471497396491527230662261 31825452880921080677874587)
        ·
          refine ⟨47738179321381621016811881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31825452880921080677874587 47738179321381621016811881)
          ·
            refine ⟨35803634491036215762608911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47738179321381621016811881 35803634491036215762608911)
            ·
              refine ⟨53705451736554323643913367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35803634491036215762608911 53705451736554323643913367)
              ·
                refine ⟨80558177604831485465870051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53705451736554323643913367 80558177604831485465870051)
                ·
                  refine ⟨120837266407247228198805077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80558177604831485465870051 120837266407247228198805077)
                  ·
                    refine ⟨1416061715709928455454747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120837266407247228198805077 1416061715709928455454747)
                    ·
                      rfl

theorem cell23_8273311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_8273311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273311 prefixEnd_8273311 := by exact prefixLift 8273311
  have htrace : WordTrace (prefixWord ++ tailWord_8273311) baseStart_8273311 baseEnd_8273311 := by
    simpa [prefixWord, tailWord_8273311, baseEnd_8273311] using wordTrace_append hprefix tailTrace_8273311
  have hstable : (prefixWord ++ tailWord_8273311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273311).length < 2 ^ (prefixWord ++ tailWord_8273311).sum := by decide
  have hdescent : baseEnd_8273311 < baseStart_8273311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273335 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_8273335 : Nat := 118140960795 + 8273335 * 2 ^ 59
def prefixEnd_8273335 : Nat := 4983230072969 + 3 ^ 40 * 8273335 * 2
def baseEnd_8273335 : Nat := 4248197470665493272464131

theorem tailTrace_8273335 : CollatzResearch.WordTrace tailWord_8273335 prefixEnd_8273335 4248197470665493272464131 := by
  unfold tailWord_8273335
  simp only [CollatzResearch.WordTrace]
  refine ⟨301753317482127742970573459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201168878321418495313715639 301753317482127742970573459)
  ·
    refine ⟨452629976223191614455860189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301753317482127742970573459 452629976223191614455860189)
    ·
      refine ⟨169736241083696855420947571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452629976223191614455860189 169736241083696855420947571)
      ·
        refine ⟨254604361625545283131421357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169736241083696855420947571 254604361625545283131421357)
        ·
          refine ⟨95476635609579481174283009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254604361625545283131421357 95476635609579481174283009)
          ·
            refine ⟨71607476707184610880712257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95476635609579481174283009 71607476707184610880712257)
            ·
              refine ⟨53705607530388458160534193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71607476707184610880712257 53705607530388458160534193)
              ·
                refine ⟨40279205647791343620400645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53705607530388458160534193 40279205647791343620400645)
                ·
                  refine ⟨7552351058960876928825121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40279205647791343620400645 7552351058960876928825121)
                  ·
                    refine ⟨5664263294220657696618841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7552351058960876928825121 5664263294220657696618841)
                    ·
                      refine ⟨4248197470665493272464131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664263294220657696618841 4248197470665493272464131)
                      ·
                        rfl

theorem cell23_8273335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_8273335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273335 prefixEnd_8273335 := by exact prefixLift 8273335
  have htrace : WordTrace (prefixWord ++ tailWord_8273335) baseStart_8273335 baseEnd_8273335 := by
    simpa [prefixWord, tailWord_8273335, baseEnd_8273335] using wordTrace_append hprefix tailTrace_8273335
  have hstable : (prefixWord ++ tailWord_8273335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273335).length < 2 ^ (prefixWord ++ tailWord_8273335).sum := by decide
  have hdescent : baseEnd_8273335 < baseStart_8273335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273341 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 9]
def baseStart_8273341 : Nat := 118140960795 + 8273341 * 2 ^ 59
def prefixEnd_8273341 : Nat := 4983230072969 + 3 ^ 40 * 8273341 * 2
def baseEnd_8273341 : Nat := 472022283505491138776567

theorem tailTrace_8273341 : CollatzResearch.WordTrace tailWord_8273341 prefixEnd_8273341 472022283505491138776567 := by
  unfold tailWord_8273341
  simp only [CollatzResearch.WordTrace]
  refine ⟨301753536320106005995291877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201169024213404003996861251 301753536320106005995291877)
  ·
    refine ⟨56578788060019876124117227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301753536320106005995291877 56578788060019876124117227)
    ·
      refine ⟨84868182090029814186175841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56578788060019876124117227 84868182090029814186175841)
      ·
        refine ⟨63651136567522360639631881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84868182090029814186175841 63651136567522360639631881)
        ·
          refine ⟨47738352425641770479723911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63651136567522360639631881 47738352425641770479723911)
          ·
            refine ⟨71607528638462655719585867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47738352425641770479723911 71607528638462655719585867)
            ·
              refine ⟨107411292957693983579378801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71607528638462655719585867 107411292957693983579378801)
              ·
                refine ⟨80558469718270487684534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107411292957693983579378801 80558469718270487684534101)
                ·
                  refine ⟨472022283505491138776567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80558469718270487684534101 472022283505491138776567)
                  ·
                    rfl

theorem cell23_8273341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_8273341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273341 prefixEnd_8273341 := by exact prefixLift 8273341
  have htrace : WordTrace (prefixWord ++ tailWord_8273341) baseStart_8273341 baseEnd_8273341 := by
    simpa [prefixWord, tailWord_8273341, baseEnd_8273341] using wordTrace_append hprefix tailTrace_8273341
  have hstable : (prefixWord ++ tailWord_8273341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273341).length < 2 ^ (prefixWord ++ tailWord_8273341).sum := by decide
  have hdescent : baseEnd_8273341 < baseStart_8273341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273368 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_8273368 : Nat := 118140960795 + 8273368 * 2 ^ 59
def prefixEnd_8273368 : Nat := 4983230072969 + 3 ^ 40 * 8273368 * 2
def baseEnd_8273368 : Nat := 4248214415527091643351479

theorem tailTrace_8273368 : CollatzResearch.WordTrace tailWord_8273368 prefixEnd_8273368 4248214415527091643351479 := by
  unfold tailWord_8273368
  simp only [CollatzResearch.WordTrace]
  refine ⟨150877260545504094803262379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201169680727338793071016505 150877260545504094803262379)
  ·
    refine ⟨226315890818256142204893569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150877260545504094803262379 226315890818256142204893569)
    ·
      refine ⟨169736918113692106653670177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226315890818256142204893569 169736918113692106653670177)
      ·
        refine ⟨127302688585269079990252633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169736918113692106653670177 127302688585269079990252633)
        ·
          refine ⟨95477016438951809992689475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127302688585269079990252633 95477016438951809992689475)
          ·
            refine ⟨143215524658427714989034213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95477016438951809992689475 143215524658427714989034213)
            ·
              refine ⟨26852910873455196560443915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143215524658427714989034213 26852910873455196560443915)
              ·
                refine ⟨40279366310182794840665873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26852910873455196560443915 40279366310182794840665873)
                ·
                  refine ⟨30209524732637096130499405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40279366310182794840665873 30209524732637096130499405)
                  ·
                    refine ⟨11328571774738911048937277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30209524732637096130499405 11328571774738911048937277)
                    ·
                      refine ⟨4248214415527091643351479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328571774738911048937277 4248214415527091643351479)
                      ·
                        rfl

theorem cell23_8273368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_8273368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273368 prefixEnd_8273368 := by exact prefixLift 8273368
  have htrace : WordTrace (prefixWord ++ tailWord_8273368) baseStart_8273368 baseEnd_8273368 := by
    simpa [prefixWord, tailWord_8273368, baseEnd_8273368] using wordTrace_append hprefix tailTrace_8273368
  have hstable : (prefixWord ++ tailWord_8273368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273368).length < 2 ^ (prefixWord ++ tailWord_8273368).sum := by decide
  have hdescent : baseEnd_8273368 < baseStart_8273368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273369 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 2, 2, 2]
def baseStart_8273369 : Nat := 118140960795 + 8273369 * 2 ^ 59
def prefixEnd_8273369 : Nat := 4983230072969 + 3 ^ 40 * 8273369 * 2
def baseEnd_8273369 : Nat := 4248214929007746139438975

theorem tailTrace_8273369 : CollatzResearch.WordTrace tailWord_8273369 prefixEnd_8273369 4248214929007746139438975 := by
  unfold tailWord_8273369
  simp only [CollatzResearch.WordTrace]
  refine ⟨301754557564004566777311161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201169705042669711184874107 301754557564004566777311161)
  ·
    refine ⟨226315918173003425082983371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301754557564004566777311161 226315918173003425082983371)
    ·
      refine ⟨339473877259505137624475057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226315918173003425082983371 339473877259505137624475057)
      ·
        refine ⟨254605407944628853218356293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339473877259505137624475057 254605407944628853218356293)
        ·
          refine ⟨47738513989617909978441805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254605407944628853218356293 47738513989617909978441805)
          ·
            refine ⟨17901942746106716241915677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47738513989617909978441805 17901942746106716241915677)
            ·
              refine ⟨6713228529790018590718379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17901942746106716241915677 6713228529790018590718379)
              ·
                refine ⟨10069842794685027886077569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713228529790018590718379 10069842794685027886077569)
                ·
                  refine ⟨7552382096013770914558177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10069842794685027886077569 7552382096013770914558177)
                  ·
                    refine ⟨5664286572010328185918633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7552382096013770914558177 5664286572010328185918633)
                    ·
                      refine ⟨4248214929007746139438975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664286572010328185918633 4248214929007746139438975)
                      ·
                        rfl

theorem cell23_8273369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_8273369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273369 prefixEnd_8273369 := by exact prefixLift 8273369
  have htrace : WordTrace (prefixWord ++ tailWord_8273369) baseStart_8273369 baseEnd_8273369 := by
    simpa [prefixWord, tailWord_8273369, baseEnd_8273369] using wordTrace_append hprefix tailTrace_8273369
  have hstable : (prefixWord ++ tailWord_8273369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273369).length < 2 ^ (prefixWord ++ tailWord_8273369).sum := by decide
  have hdescent : baseEnd_8273369 < baseStart_8273369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273411 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_8273411 : Nat := 118140960795 + 8273411 * 2 ^ 59
def prefixEnd_8273411 : Nat := 4983230072969 + 3 ^ 40 * 8273411 * 2
def baseEnd_8273411 : Nat := 4248236495195234975113781

theorem tailTrace_8273411 : CollatzResearch.WordTrace tailWord_8273411 prefixEnd_8273411 4248236495195234975113781 := by
  unfold tailWord_8273411
  simp only [CollatzResearch.WordTrace]
  refine ⟨301756089429852407950340087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201170726286568271966893391 301756089429852407950340087)
  ·
    refine ⟨452634134144778611925510131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301756089429852407950340087 452634134144778611925510131)
    ·
      refine ⟨678951201217167917888265197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452634134144778611925510131 678951201217167917888265197)
      ·
        refine ⟨254606700456437969208099449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678951201217167917888265197 254606700456437969208099449)
        ·
          refine ⟨190955025342328476906074587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254606700456437969208099449 190955025342328476906074587)
          ·
            refine ⟨286432538013492715359111881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190955025342328476906074587 286432538013492715359111881)
            ·
              refine ⟨214824403510119536519333911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286432538013492715359111881 214824403510119536519333911)
              ·
                refine ⟨322236605265179304779000867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214824403510119536519333911 322236605265179304779000867)
                ·
                  refine ⟨483354907897768957168501301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322236605265179304779000867 483354907897768957168501301)
                  ·
                    refine ⟨45314522615415839734546997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 483354907897768957168501301 45314522615415839734546997)
                    ·
                      refine ⟨4248236495195234975113781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45314522615415839734546997 4248236495195234975113781)
                      ·
                        rfl

theorem cell23_8273411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_8273411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273411 prefixEnd_8273411 := by exact prefixLift 8273411
  have htrace : WordTrace (prefixWord ++ tailWord_8273411) baseStart_8273411 baseEnd_8273411 := by
    simpa [prefixWord, tailWord_8273411, baseEnd_8273411] using wordTrace_append hprefix tailTrace_8273411
  have hstable : (prefixWord ++ tailWord_8273411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273411).length < 2 ^ (prefixWord ++ tailWord_8273411).sum := by decide
  have hdescent : baseEnd_8273411 < baseStart_8273411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_8273451 : Nat := 118140960795 + 8273451 * 2 ^ 59
def prefixEnd_8273451 : Nat := 4983230072969 + 3 ^ 40 * 8273451 * 2
def baseEnd_8273451 : Nat := 4248257034421414818613597

theorem tailTrace_8273451 : CollatzResearch.WordTrace tailWord_8273451 prefixEnd_8273451 4248257034421414818613597 := by
  unfold tailWord_8273451
  simp only [CollatzResearch.WordTrace]
  refine ⟨301757548349707494781796207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201171698899804996521197471 301757548349707494781796207)
  ·
    refine ⟨452636322524561242172694311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301757548349707494781796207 452636322524561242172694311)
    ·
      refine ⟨678954483786841863259041467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452636322524561242172694311 678954483786841863259041467)
      ·
        refine ⟨1018431725680262794888562201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678954483786841863259041467 1018431725680262794888562201)
        ·
          refine ⟨763823794260197096166421651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018431725680262794888562201 763823794260197096166421651)
          ·
            refine ⟨1145735691390295644249632477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763823794260197096166421651 1145735691390295644249632477)
            ·
              refine ⟨429650884271360866593612179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145735691390295644249632477 429650884271360866593612179)
              ·
                refine ⟨644476326407041299890418269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429650884271360866593612179 644476326407041299890418269)
                ·
                  refine ⟨241678622402640487458906851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644476326407041299890418269 241678622402640487458906851)
                  ·
                    refine ⟨362517933603960731188360277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241678622402640487458906851 362517933603960731188360277)
                    ·
                      refine ⟨4248257034421414818613597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362517933603960731188360277 4248257034421414818613597)
                      ·
                        rfl

theorem cell23_8273451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_8273451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273451 prefixEnd_8273451 := by exact prefixLift 8273451
  have htrace : WordTrace (prefixWord ++ tailWord_8273451) baseStart_8273451 baseEnd_8273451 := by
    simpa [prefixWord, tailWord_8273451, baseEnd_8273451] using wordTrace_append hprefix tailTrace_8273451
  have hstable : (prefixWord ++ tailWord_8273451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273451).length < 2 ^ (prefixWord ++ tailWord_8273451).sum := by decide
  have hdescent : baseEnd_8273451 < baseStart_8273451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273465 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 6]
def baseStart_8273465 : Nat := 118140960795 + 8273465 * 2 ^ 59
def prefixEnd_8273465 : Nat := 4983230072969 + 3 ^ 40 * 8273465 * 2
def baseEnd_8273465 : Nat := 472029358127841973759837

theorem tailTrace_8273465 : CollatzResearch.WordTrace tailWord_8273465 prefixEnd_8273465 472029358127841973759837 := by
  unfold tailWord_8273465
  simp only [CollatzResearch.WordTrace]
  refine ⟨301758058971656775172805849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201172039314437850115203899 301758058971656775172805849)
  ·
    refine ⟨226318544228742581379604387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301758058971656775172805849 226318544228742581379604387)
    ·
      refine ⟨339477816343113872069406581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226318544228742581379604387 339477816343113872069406581)
      ·
        refine ⟨31826045282166925506506867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339477816343113872069406581 31826045282166925506506867)
        ·
          refine ⟨47739067923250388259760301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31826045282166925506506867 47739067923250388259760301)
          ·
            refine ⟨17902150471218895597410113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47739067923250388259760301 17902150471218895597410113)
            ·
              refine ⟨13426612853414171698057585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17902150471218895597410113 13426612853414171698057585)
              ·
                refine ⟨10069959640060628773543189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13426612853414171698057585 10069959640060628773543189)
                ·
                  refine ⟨472029358127841973759837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10069959640060628773543189 472029358127841973759837)
                  ·
                    rfl

theorem cell23_8273465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_8273465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273465 prefixEnd_8273465 := by exact prefixLift 8273465
  have htrace : WordTrace (prefixWord ++ tailWord_8273465) baseStart_8273465 baseEnd_8273465 := by
    simpa [prefixWord, tailWord_8273465, baseEnd_8273465] using wordTrace_append hprefix tailTrace_8273465
  have hstable : (prefixWord ++ tailWord_8273465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273465).length < 2 ^ (prefixWord ++ tailWord_8273465).sum := by decide
  have hdescent : baseEnd_8273465 < baseStart_8273465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273469 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_8273469 : Nat := 118140960795 + 8273469 * 2 ^ 59
def prefixEnd_8273469 : Nat := 4983230072969 + 3 ^ 40 * 8273469 * 2
def baseEnd_8273469 : Nat := 1416088759024398582729505

theorem tailTrace_8273469 : CollatzResearch.WordTrace tailWord_8273469 prefixEnd_8273469 1416088759024398582729505 := by
  unfold tailWord_8273469
  simp only [CollatzResearch.WordTrace]
  refine ⟨301758204863642283855951461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201172136575761522570634307 301758204863642283855951461)
  ·
    refine ⟨56579663411932928222990899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301758204863642283855951461 56579663411932928222990899)
    ·
      refine ⟨84869495117899392334486349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56579663411932928222990899 84869495117899392334486349)
      ·
        refine ⟨31826060669212272125432381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84869495117899392334486349 31826060669212272125432381)
        ·
          refine ⟨11934772750954602047037143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31826060669212272125432381 11934772750954602047037143)
          ·
            refine ⟨17902159126431903070555715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934772750954602047037143 17902159126431903070555715)
            ·
              refine ⟨26853238689647854605833573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902159126431903070555715 26853238689647854605833573)
              ·
                refine ⟨5034982254308972738593795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26853238689647854605833573 5034982254308972738593795)
                ·
                  refine ⟨7552473381463459107890693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034982254308972738593795 7552473381463459107890693)
                  ·
                    refine ⟨1416088759024398582729505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7552473381463459107890693 1416088759024398582729505)
                    ·
                      rfl

theorem cell23_8273469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_8273469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273469 prefixEnd_8273469 := by exact prefixLift 8273469
  have htrace : WordTrace (prefixWord ++ tailWord_8273469) baseStart_8273469 baseEnd_8273469 := by
    simpa [prefixWord, tailWord_8273469, baseEnd_8273469] using wordTrace_append hprefix tailTrace_8273469
  have hstable : (prefixWord ++ tailWord_8273469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273469).length < 2 ^ (prefixWord ++ tailWord_8273469).sum := by decide
  have hdescent : baseEnd_8273469 < baseStart_8273469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273492 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_8273492 : Nat := 118140960795 + 8273492 * 2 ^ 59
def prefixEnd_8273492 : Nat := 4983230072969 + 3 ^ 40 * 8273492 * 2
def baseEnd_8273492 : Nat := 4248278087128249158200909

theorem tailTrace_8273492 : CollatzResearch.WordTrace tailWord_8273492 prefixEnd_8273492 4248278087128249158200909 := by
  unfold tailWord_8273492
  simp only [CollatzResearch.WordTrace]
  refine ⟨150879521871279479392019365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201172695828372639189359153 150879521871279479392019365)
  ·
    refine ⟨28289910350864902386003631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150879521871279479392019365 28289910350864902386003631)
    ·
      refine ⟨42434865526297353579005447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28289910350864902386003631 42434865526297353579005447)
      ·
        refine ⟨63652298289446030368508171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42434865526297353579005447 63652298289446030368508171)
        ·
          refine ⟨95478447434169045552762257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63652298289446030368508171 95478447434169045552762257)
          ·
            refine ⟨71608835575626784164571693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95478447434169045552762257 71608835575626784164571693)
            ·
              refine ⟨26853313340860044061714385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71608835575626784164571693 26853313340860044061714385)
              ·
                refine ⟨20139985005645033046285789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26853313340860044061714385 20139985005645033046285789)
                ·
                  refine ⟨7552494377116887392357171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20139985005645033046285789 7552494377116887392357171)
                  ·
                    refine ⟨11328741565675331088535757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7552494377116887392357171 11328741565675331088535757)
                    ·
                      refine ⟨4248278087128249158200909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328741565675331088535757 4248278087128249158200909)
                      ·
                        rfl

theorem cell23_8273492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_8273492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273492 prefixEnd_8273492 := by exact prefixLift 8273492
  have htrace : WordTrace (prefixWord ++ tailWord_8273492) baseStart_8273492 baseEnd_8273492 := by
    simpa [prefixWord, tailWord_8273492, baseEnd_8273492] using wordTrace_append hprefix tailTrace_8273492
  have hstable : (prefixWord ++ tailWord_8273492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273492).length < 2 ^ (prefixWord ++ tailWord_8273492).sum := by decide
  have hdescent : baseEnd_8273492 < baseStart_8273492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273509 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_8273509 : Nat := 118140960795 + 8273509 * 2 ^ 59
def prefixEnd_8273509 : Nat := 4983230072969 + 3 ^ 40 * 8273509 * 2
def baseEnd_8273509 : Nat := 4248286816299375591688331

theorem tailTrace_8273509 : CollatzResearch.WordTrace tailWord_8273509 prefixEnd_8273509 4248286816299375591688331 := by
  unfold tailWord_8273509
  simp only [CollatzResearch.WordTrace]
  refine ⟨301759663783497370687407581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201173109188998247124938387 301759663783497370687407581)
  ·
    refine ⟨113159873918811514007777843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301759663783497370687407581 113159873918811514007777843)
    ·
      refine ⟨169739810878217271011666765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113159873918811514007777843 169739810878217271011666765)
      ·
        refine ⟨63652429079331476629375037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169739810878217271011666765 63652429079331476629375037)
        ·
          refine ⟨23869660904749303736015639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63652429079331476629375037 23869660904749303736015639)
          ·
            refine ⟨35804491357123955604023459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23869660904749303736015639 35804491357123955604023459)
            ·
              refine ⟨53706737035685933406035189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35804491357123955604023459 53706737035685933406035189)
              ·
                refine ⟨5035006597095556256815799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53706737035685933406035189 5035006597095556256815799)
                ·
                  refine ⟨7552509895643334385223699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035006597095556256815799 7552509895643334385223699)
                  ·
                    refine ⟨11328764843465001577835549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7552509895643334385223699 11328764843465001577835549)
                    ·
                      refine ⟨4248286816299375591688331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328764843465001577835549 4248286816299375591688331)
                      ·
                        rfl

theorem cell23_8273509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_8273509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273509 prefixEnd_8273509 := by exact prefixLift 8273509
  have htrace : WordTrace (prefixWord ++ tailWord_8273509) baseStart_8273509 baseEnd_8273509 := by
    simpa [prefixWord, tailWord_8273509, baseEnd_8273509] using wordTrace_append hprefix tailTrace_8273509
  have hstable : (prefixWord ++ tailWord_8273509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273509).length < 2 ^ (prefixWord ++ tailWord_8273509).sum := by decide
  have hdescent : baseEnd_8273509 < baseStart_8273509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273512 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_8273512 : Nat := 118140960795 + 8273512 * 2 ^ 59
def prefixEnd_8273512 : Nat := 4983230072969 + 3 ^ 40 * 8273512 * 2
def baseEnd_8273512 : Nat := 1416096118913779693316939

theorem tailTrace_8273512 : CollatzResearch.WordTrace tailWord_8273512 prefixEnd_8273512 1416096118913779693316939 := by
  unfold tailWord_8273512
  simp only [CollatzResearch.WordTrace]
  refine ⟨150879886601243251099883395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201173182134991001466511193 150879886601243251099883395)
  ·
    refine ⟨226319829901864876649825093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150879886601243251099883395 226319829901864876649825093)
    ·
      refine ⟨42434968106599664371842205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226319829901864876649825093 42434968106599664371842205)
      ·
        refine ⟨15913113039974874139440827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42434968106599664371842205 15913113039974874139440827)
        ·
          refine ⟨23869669559962311209161241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15913113039974874139440827 23869669559962311209161241)
          ·
            refine ⟨17902252169971733406870931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23869669559962311209161241 17902252169971733406870931)
            ·
              refine ⟨26853378254957600110306397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902252169971733406870931 26853378254957600110306397)
              ·
                refine ⟨10070016845609100041364899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26853378254957600110306397 10070016845609100041364899)
                ·
                  refine ⟨15105025268413650062047349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070016845609100041364899 15105025268413650062047349)
                  ·
                    refine ⟨1416096118913779693316939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15105025268413650062047349 1416096118913779693316939)
                    ·
                      rfl

theorem cell23_8273512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_8273512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273512 prefixEnd_8273512 := by exact prefixLift 8273512
  have htrace : WordTrace (prefixWord ++ tailWord_8273512) baseStart_8273512 baseEnd_8273512 := by
    simpa [prefixWord, tailWord_8273512, baseEnd_8273512] using wordTrace_append hprefix tailTrace_8273512
  have hstable : (prefixWord ++ tailWord_8273512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273512).length < 2 ^ (prefixWord ++ tailWord_8273512).sum := by decide
  have hdescent : baseEnd_8273512 < baseStart_8273512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273526 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_8273526 : Nat := 118140960795 + 8273526 * 2 ^ 59
def prefixEnd_8273526 : Nat := 4983230072969 + 3 ^ 40 * 8273526 * 2
def baseEnd_8273526 : Nat := 4248295545470502025175753

theorem tailTrace_8273526 : CollatzResearch.WordTrace tailWord_8273526 prefixEnd_8273526 4248295545470502025175753 := by
  unfold tailWord_8273526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860017739027236411923527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201173522549623855060517621 18860017739027236411923527)
  ·
    refine ⟨28290026608540854617885291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860017739027236411923527 28290026608540854617885291)
    ·
      refine ⟨42435039912811281926827937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28290026608540854617885291 42435039912811281926827937)
      ·
        refine ⟨31826279934608461445120953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42435039912811281926827937 31826279934608461445120953)
        ·
          refine ⟨23869709950956346083840715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31826279934608461445120953 23869709950956346083840715)
          ·
            refine ⟨35804564926434519125761073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23869709950956346083840715 35804564926434519125761073)
            ·
              refine ⟨26853423694825889344320805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35804564926434519125761073 26853423694825889344320805)
              ·
                refine ⟨5035016942779854252060151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26853423694825889344320805 5035016942779854252060151)
                ·
                  refine ⟨7552525414169781378090227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035016942779854252060151 7552525414169781378090227)
                  ·
                    refine ⟨11328788121254672067135341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7552525414169781378090227 11328788121254672067135341)
                    ·
                      refine ⟨4248295545470502025175753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328788121254672067135341 4248295545470502025175753)
                      ·
                        rfl

theorem cell23_8273526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_8273526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273526 prefixEnd_8273526 := by exact prefixLift 8273526
  have htrace : WordTrace (prefixWord ++ tailWord_8273526) baseStart_8273526 baseEnd_8273526 := by
    simpa [prefixWord, tailWord_8273526, baseEnd_8273526] using wordTrace_append hprefix tailTrace_8273526
  have hstable : (prefixWord ++ tailWord_8273526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273526).length < 2 ^ (prefixWord ++ tailWord_8273526).sum := by decide
  have hdescent : baseEnd_8273526 < baseStart_8273526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273545 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_8273545 : Nat := 118140960795 + 8273545 * 2 ^ 59
def prefixEnd_8273545 : Nat := 4983230072969 + 3 ^ 40 * 8273545 * 2
def baseEnd_8273545 : Nat := 4248305301602937450838165

theorem tailTrace_8273545 : CollatzResearch.WordTrace tailWord_8273545 prefixEnd_8273545 4248305301602937450838165 := by
  unfold tailWord_8273545
  simp only [CollatzResearch.WordTrace]
  refine ⟨301760976811366948835718089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201173984540911299223812059 301760976811366948835718089)
  ·
    refine ⟨226320732608525211626788567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301760976811366948835718089 226320732608525211626788567)
    ·
      refine ⟨339481098912787817440182851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226320732608525211626788567 339481098912787817440182851)
      ·
        refine ⟨509221648369181726160274277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339481098912787817440182851 509221648369181726160274277)
        ·
          refine ⟨95479059069221573655051427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509221648369181726160274277 95479059069221573655051427)
          ·
            refine ⟨143218588603832360482577141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95479059069221573655051427 143218588603832360482577141)
            ·
              refine ⟨13426742681609283795241607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143218588603832360482577141 13426742681609283795241607)
              ·
                refine ⟨20140114022413925692862411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426742681609283795241607 20140114022413925692862411)
                ·
                  refine ⟨30210171033620888539293617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20140114022413925692862411 30210171033620888539293617)
                  ·
                    refine ⟨22657628275215666404470213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30210171033620888539293617 22657628275215666404470213)
                    ·
                      refine ⟨4248305301602937450838165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22657628275215666404470213 4248305301602937450838165)
                      ·
                        rfl

theorem cell23_8273545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_8273545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273545 prefixEnd_8273545 := by exact prefixLift 8273545
  have htrace : WordTrace (prefixWord ++ tailWord_8273545) baseStart_8273545 baseEnd_8273545 := by
    simpa [prefixWord, tailWord_8273545, baseEnd_8273545] using wordTrace_append hprefix tailTrace_8273545
  have hstable : (prefixWord ++ tailWord_8273545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273545).length < 2 ^ (prefixWord ++ tailWord_8273545).sum := by decide
  have hdescent : baseEnd_8273545 < baseStart_8273545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273565 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_8273565 : Nat := 118140960795 + 8273565 * 2 ^ 59
def prefixEnd_8273565 : Nat := 4983230072969 + 3 ^ 40 * 8273565 * 2
def baseEnd_8273565 : Nat := 4248315571216027372588073

theorem tailTrace_8273565 : CollatzResearch.WordTrace tailWord_8273565 prefixEnd_8273565 4248315571216027372588073 := by
  unfold tailWord_8273565
  simp only [CollatzResearch.WordTrace]
  refine ⟨301761706271294492251446149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201174470847529661500964099 301761706271294492251446149)
  ·
    refine ⟨56580319925867717297146153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301761706271294492251446149 56580319925867717297146153)
    ·
      refine ⟨42435239944400787972859615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56580319925867717297146153 42435239944400787972859615)
      ·
        refine ⟨63652859916601181959289423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42435239944400787972859615 63652859916601181959289423)
        ·
          refine ⟨95479289874901772938934135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63652859916601181959289423 95479289874901772938934135)
          ·
            refine ⟨143218934812352659408401203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95479289874901772938934135 143218934812352659408401203)
            ·
              refine ⟨214828402218528989112601805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143218934812352659408401203 214828402218528989112601805)
              ·
                refine ⟨80560650831948370917225677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214828402218528989112601805 80560650831948370917225677)
                ·
                  refine ⟨30210244061980639093959629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80560650831948370917225677 30210244061980639093959629)
                  ·
                    refine ⟨11328841523242739660234861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30210244061980639093959629 11328841523242739660234861)
                    ·
                      refine ⟨4248315571216027372588073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328841523242739660234861 4248315571216027372588073)
                      ·
                        rfl

theorem cell23_8273565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_8273565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273565 prefixEnd_8273565 := by exact prefixLift 8273565
  have htrace : WordTrace (prefixWord ++ tailWord_8273565) baseStart_8273565 baseEnd_8273565 := by
    simpa [prefixWord, tailWord_8273565, baseEnd_8273565] using wordTrace_append hprefix tailTrace_8273565
  have hstable : (prefixWord ++ tailWord_8273565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273565).length < 2 ^ (prefixWord ++ tailWord_8273565).sum := by decide
  have hdescent : baseEnd_8273565 < baseStart_8273565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273625 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_8273625 : Nat := 118140960795 + 8273625 * 2 ^ 59
def prefixEnd_8273625 : Nat := 4983230072969 + 3 ^ 40 * 8273625 * 2
def baseEnd_8273625 : Nat := 4248346380055297137837797

theorem tailTrace_8273625 : CollatzResearch.WordTrace tailWord_8273625 prefixEnd_8273625 4248346380055297137837797 := by
  unfold tailWord_8273625
  simp only [CollatzResearch.WordTrace]
  refine ⟨301763894651077122498630329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201175929767384748332420219 301763894651077122498630329)
  ·
    refine ⟨226322920988307841873972747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301763894651077122498630329 226322920988307841873972747)
    ·
      refine ⟨339484381482461762810959121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226322920988307841873972747 339484381482461762810959121)
      ·
        refine ⟨254613286111846322108219341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339484381482461762810959121 254613286111846322108219341)
        ·
          refine ⟨95479982291942370790582253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254613286111846322108219341 95479982291942370790582253)
          ·
            refine ⟨35804993359478389046468345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95479982291942370790582253 35804993359478389046468345)
            ·
              refine ⟨26853745019608791784851259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35804993359478389046468345 26853745019608791784851259)
              ·
                refine ⟨40280617529413187677276889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26853745019608791784851259 40280617529413187677276889)
                ·
                  refine ⟨30210463147059890757957667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40280617529413187677276889 30210463147059890757957667)
                  ·
                    refine ⟨45315694720589836136936501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30210463147059890757957667 45315694720589836136936501)
                    ·
                      refine ⟨4248346380055297137837797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45315694720589836136936501 4248346380055297137837797)
                      ·
                        rfl

theorem cell23_8273625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_8273625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273625 prefixEnd_8273625 := by exact prefixLift 8273625
  have htrace : WordTrace (prefixWord ++ tailWord_8273625) baseStart_8273625 baseEnd_8273625 := by
    simpa [prefixWord, tailWord_8273625, baseEnd_8273625] using wordTrace_append hprefix tailTrace_8273625
  have hstable : (prefixWord ++ tailWord_8273625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273625).length < 2 ^ (prefixWord ++ tailWord_8273625).sum := by decide
  have hdescent : baseEnd_8273625 < baseStart_8273625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273626 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_8273626 : Nat := 118140960795 + 8273626 * 2 ^ 59
def prefixEnd_8273626 : Nat := 4983230072969 + 3 ^ 40 * 8273626 * 2
def baseEnd_8273626 : Nat := 4248346893535951633925293

theorem tailTrace_8273626 : CollatzResearch.WordTrace tailWord_8273626 prefixEnd_8273626 4248346893535951633925293 := by
  unfold tailWord_8273626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75440982781018374917354183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201175954082715666446277821 75440982781018374917354183)
  ·
    refine ⟨113161474171527562376031275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75440982781018374917354183 113161474171527562376031275)
    ·
      refine ⟨169742211257291343564046913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113161474171527562376031275 169742211257291343564046913)
      ·
        refine ⟨127306658442968507673035185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169742211257291343564046913 127306658442968507673035185)
        ·
          refine ⟨95479993832226380754776389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127306658442968507673035185 95479993832226380754776389)
          ·
            refine ⟨17902498843542446391520573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95479993832226380754776389 17902498843542446391520573)
            ·
              refine ⟨6713437066328417396820215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17902498843542446391520573 6713437066328417396820215)
              ·
                refine ⟨10070155599492626095230323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713437066328417396820215 10070155599492626095230323)
                ·
                  refine ⟨15105233399238939142845485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070155599492626095230323 15105233399238939142845485)
                  ·
                    refine ⟨5664462524714602178567057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15105233399238939142845485 5664462524714602178567057)
                    ·
                      refine ⟨4248346893535951633925293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664462524714602178567057 4248346893535951633925293)
                      ·
                        rfl

theorem cell23_8273626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_8273626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273626 prefixEnd_8273626 := by exact prefixLift 8273626
  have htrace : WordTrace (prefixWord ++ tailWord_8273626) baseStart_8273626 baseEnd_8273626 := by
    simpa [prefixWord, tailWord_8273626, baseEnd_8273626] using wordTrace_append hprefix tailTrace_8273626
  have hstable : (prefixWord ++ tailWord_8273626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273626).length < 2 ^ (prefixWord ++ tailWord_8273626).sum := by decide
  have hdescent : baseEnd_8273626 < baseStart_8273626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273655 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_8273655 : Nat := 118140960795 + 8273655 * 2 ^ 59
def prefixEnd_8273655 : Nat := 4983230072969 + 3 ^ 40 * 8273655 * 2
def baseEnd_8273655 : Nat := 4248361784474932020462659

theorem tailTrace_8273655 : CollatzResearch.WordTrace tailWord_8273655 prefixEnd_8273655 4248361784474932020462659 := by
  unfold tailWord_8273655
  simp only [CollatzResearch.WordTrace]
  refine ⟨301764988840968437622222419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201176659227312291748148279 301764988840968437622222419)
  ·
    refine ⟨452647483261452656433333629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301764988840968437622222419 452647483261452656433333629)
    ·
      refine ⟨169742806223044746162500111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452647483261452656433333629 169742806223044746162500111)
      ·
        refine ⟨254614209334567119243750167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169742806223044746162500111 254614209334567119243750167)
        ·
          refine ⟨381921314001850678865625251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254614209334567119243750167 381921314001850678865625251)
          ·
            refine ⟨572881971002776018298437877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381921314001850678865625251 572881971002776018298437877)
            ·
              refine ⟨53707684781510251715478551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 572881971002776018298437877 53707684781510251715478551)
              ·
                refine ⟨80561527172265377573217827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53707684781510251715478551 80561527172265377573217827)
                ·
                  refine ⟨120842290758398066359826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80561527172265377573217827 120842290758398066359826741)
                  ·
                    refine ⟨11328964758599818721233757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120842290758398066359826741 11328964758599818721233757)
                    ·
                      refine ⟨4248361784474932020462659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11328964758599818721233757 4248361784474932020462659)
                      ·
                        rfl

theorem cell23_8273655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_8273655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273655 prefixEnd_8273655 := by exact prefixLift 8273655
  have htrace : WordTrace (prefixWord ++ tailWord_8273655) baseStart_8273655 baseEnd_8273655 := by
    simpa [prefixWord, tailWord_8273655, baseEnd_8273655] using wordTrace_append hprefix tailTrace_8273655
  have hstable : (prefixWord ++ tailWord_8273655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273655).length < 2 ^ (prefixWord ++ tailWord_8273655).sum := by decide
  have hdescent : baseEnd_8273655 < baseStart_8273655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273677 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_8273677 : Nat := 118140960795 + 8273677 * 2 ^ 59
def prefixEnd_8273677 : Nat := 4983230072969 + 3 ^ 40 * 8273677 * 2
def baseEnd_8273677 : Nat := 4248373081049330934387559

theorem tailTrace_8273677 : CollatzResearch.WordTrace tailWord_8273677 prefixEnd_8273677 4248373081049330934387559 := by
  unfold tailWord_8273677
  simp only [CollatzResearch.WordTrace]
  refine ⟨301765791246888735379523285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201177194164592490253015523 301765791246888735379523285)
  ·
    refine ⟨7072635732348954735457577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 301765791246888735379523285 7072635732348954735457577)
    ·
      refine ⟨5304476799261716051593183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7072635732348954735457577 5304476799261716051593183)
      ·
        refine ⟨7956715198892574077389775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304476799261716051593183 7956715198892574077389775)
        ·
          refine ⟨11935072798338861116084663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956715198892574077389775 11935072798338861116084663)
          ·
            refine ⟨17902609197508291674126995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935072798338861116084663 17902609197508291674126995)
            ·
              refine ⟨26853913796262437511190493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902609197508291674126995 26853913796262437511190493)
              ·
                refine ⟨10070217673598414066696435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26853913796262437511190493 10070217673598414066696435)
                ·
                  refine ⟨15105326510397621100044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070217673598414066696435 15105326510397621100044653)
                  ·
                    refine ⟨5664497441399107912516745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15105326510397621100044653 5664497441399107912516745)
                    ·
                      refine ⟨4248373081049330934387559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664497441399107912516745 4248373081049330934387559)
                      ·
                        rfl

theorem cell23_8273677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_8273677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273677 prefixEnd_8273677 := by exact prefixLift 8273677
  have htrace : WordTrace (prefixWord ++ tailWord_8273677) baseStart_8273677 baseEnd_8273677 := by
    simpa [prefixWord, tailWord_8273677, baseEnd_8273677] using wordTrace_append hprefix tailTrace_8273677
  have hstable : (prefixWord ++ tailWord_8273677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273677).length < 2 ^ (prefixWord ++ tailWord_8273677).sum := by decide
  have hdescent : baseEnd_8273677 < baseStart_8273677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273735 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 8]
def baseStart_8273735 : Nat := 118140960795 + 8273735 * 2 ^ 59
def prefixEnd_8273735 : Nat := 4983230072969 + 3 ^ 40 * 8273735 * 2
def baseEnd_8273735 : Nat := 472044762547476856384699

theorem tailTrace_8273735 : CollatzResearch.WordTrace tailWord_8273735 prefixEnd_8273735 472044762547476856384699 := by
  unfold tailWord_8273735
  simp only [CollatzResearch.WordTrace]
  refine ⟨301767906680678611285134659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201178604453785740856756439 301767906680678611285134659)
  ·
    refine ⟨452651860021017916927701989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301767906680678611285134659 452651860021017916927701989)
    ·
      refine ⟨84872223753940859423944123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452651860021017916927701989 84872223753940859423944123)
      ·
        refine ⟨127308335630911289135916185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84872223753940859423944123 127308335630911289135916185)
        ·
          refine ⟨95481251723183466851937139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127308335630911289135916185 95481251723183466851937139)
          ·
            refine ⟨143221877584775200277905709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95481251723183466851937139 143221877584775200277905709)
            ·
              refine ⟨53708204094290700104214641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143221877584775200277905709 53708204094290700104214641)
              ·
                refine ⟨40281153070718025078160981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53708204094290700104214641 40281153070718025078160981)
                ·
                  refine ⟨472044762547476856384699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40281153070718025078160981 472044762547476856384699)
                  ·
                    rfl

theorem cell23_8273735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 8].length) (baseStart_8273735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273735 prefixEnd_8273735 := by exact prefixLift 8273735
  have htrace : WordTrace (prefixWord ++ tailWord_8273735) baseStart_8273735 baseEnd_8273735 := by
    simpa [prefixWord, tailWord_8273735, baseEnd_8273735] using wordTrace_append hprefix tailTrace_8273735
  have hstable : (prefixWord ++ tailWord_8273735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273735).length < 2 ^ (prefixWord ++ tailWord_8273735).sum := by decide
  have hdescent : baseEnd_8273735 < baseStart_8273735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273749 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_8273749 : Nat := 118140960795 + 8273749 * 2 ^ 59
def prefixEnd_8273749 : Nat := 4983230072969 + 3 ^ 40 * 8273749 * 2
def baseEnd_8273749 : Nat := 4248410051656454652687227

theorem tailTrace_8273749 : CollatzResearch.WordTrace tailWord_8273749 prefixEnd_8273749 4248410051656454652687227 := by
  unfold tailWord_8273749
  simp only [CollatzResearch.WordTrace]
  refine ⟨301768417302627891676144301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201178944868418594450762867 301768417302627891676144301)
  ·
    refine ⟨113163156488485459378554113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301768417302627891676144301 113163156488485459378554113)
    ·
      refine ⟨84872367366364094533915585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113163156488485459378554113 84872367366364094533915585)
      ·
        refine ⟨63654275524773070900436689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84872367366364094533915585 63654275524773070900436689)
        ·
          refine ⟨47740706643579803175327517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63654275524773070900436689 47740706643579803175327517)
          ·
            refine ⟨17902764991342426190747819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47740706643579803175327517 17902764991342426190747819)
            ·
              refine ⟨26854147487013639286121729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902764991342426190747819 26854147487013639286121729)
              ·
                refine ⟨20140610615260229464591297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26854147487013639286121729 20140610615260229464591297)
                ·
                  refine ⟨15105457961445172098443473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20140610615260229464591297 15105457961445172098443473)
                  ·
                    refine ⟨11329093471083879073832605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15105457961445172098443473 11329093471083879073832605)
                    ·
                      refine ⟨4248410051656454652687227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329093471083879073832605 4248410051656454652687227)
                      ·
                        rfl

theorem cell23_8273749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_8273749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273749 prefixEnd_8273749 := by exact prefixLift 8273749
  have htrace : WordTrace (prefixWord ++ tailWord_8273749) baseStart_8273749 baseEnd_8273749 := by
    simpa [prefixWord, tailWord_8273749, baseEnd_8273749] using wordTrace_append hprefix tailTrace_8273749
  have hstable : (prefixWord ++ tailWord_8273749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273749).length < 2 ^ (prefixWord ++ tailWord_8273749).sum := by decide
  have hdescent : baseEnd_8273749 < baseStart_8273749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273765 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_8273765 : Nat := 118140960795 + 8273765 * 2 ^ 59
def prefixEnd_8273765 : Nat := 4983230072969 + 3 ^ 40 * 8273765 * 2
def baseEnd_8273765 : Nat := 1416139422448975530029051

theorem tailTrace_8273765 : CollatzResearch.WordTrace tailWord_8273765 prefixEnd_8273765 1416139422448975530029051 := by
  unfold tailWord_8273765
  simp only [CollatzResearch.WordTrace]
  refine ⟨301769000870569926408726749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201179333913713284272484499 301769000870569926408726749)
  ·
    refine ⟨113163375326463722403272531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301769000870569926408726749 113163375326463722403272531)
    ·
      refine ⟨169745062989695583604908797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113163375326463722403272531 169745062989695583604908797)
      ·
        refine ⟨63654398621135843851840799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169745062989695583604908797 63654398621135843851840799)
        ·
          refine ⟨95481597931703765777761199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63654398621135843851840799 95481597931703765777761199)
          ·
            refine ⟨143222396897555648666641799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95481597931703765777761199 143222396897555648666641799)
            ·
              refine ⟨214833595346333472999962699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143222396897555648666641799 214833595346333472999962699)
              ·
                refine ⟨322250393019500209499944049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214833595346333472999962699 322250393019500209499944049)
                ·
                  refine ⟨241687794764625157124958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322250393019500209499944049 241687794764625157124958037)
                  ·
                    refine ⟨1416139422448975530029051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 241687794764625157124958037 1416139422448975530029051)
                    ·
                      rfl

theorem cell23_8273765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_8273765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273765 prefixEnd_8273765 := by exact prefixLift 8273765
  have htrace : WordTrace (prefixWord ++ tailWord_8273765) baseStart_8273765 baseEnd_8273765 := by
    simpa [prefixWord, tailWord_8273765, baseEnd_8273765] using wordTrace_append hprefix tailTrace_8273765
  have hstable : (prefixWord ++ tailWord_8273765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273765).length < 2 ^ (prefixWord ++ tailWord_8273765).sum := by decide
  have hdescent : baseEnd_8273765 < baseStart_8273765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273839 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_8273839 : Nat := 118140960795 + 8273839 * 2 ^ 59
def prefixEnd_8273839 : Nat := 4983230072969 + 3 ^ 40 * 8273839 * 2
def baseEnd_8273839 : Nat := 4248456264915359300561813

theorem tailTrace_8273839 : CollatzResearch.WordTrace tailWord_8273839 prefixEnd_8273839 4248456264915359300561813 := by
  unfold tailWord_8273839
  simp only [CollatzResearch.WordTrace]
  refine ⟨301771699872301837046920571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201181133248201224697947047 301771699872301837046920571)
  ·
    refine ⟨452657549808452755570380857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301771699872301837046920571 452657549808452755570380857)
    ·
      refine ⟨339493162356339566677785643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452657549808452755570380857 339493162356339566677785643)
      ·
        refine ⟨509239743534509350016678465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339493162356339566677785643 509239743534509350016678465)
        ·
          refine ⟨381929807650882012512508849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509239743534509350016678465 381929807650882012512508849)
          ·
            refine ⟨286447355738161509384381637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381929807650882012512508849 286447355738161509384381637)
            ·
              refine ⟨53708879200905283009571557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286447355738161509384381637 53708879200905283009571557)
              ·
                refine ⟨10070414850169740564294667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53708879200905283009571557 10070414850169740564294667)
                ·
                  refine ⟨15105622275254610846442001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070414850169740564294667 15105622275254610846442001)
                  ·
                    refine ⟨11329216706440958134831501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15105622275254610846442001 11329216706440958134831501)
                    ·
                      refine ⟨4248456264915359300561813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329216706440958134831501 4248456264915359300561813)
                      ·
                        rfl

theorem cell23_8273839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_8273839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273839 prefixEnd_8273839 := by exact prefixLift 8273839
  have htrace : WordTrace (prefixWord ++ tailWord_8273839) baseStart_8273839 baseEnd_8273839 := by
    simpa [prefixWord, tailWord_8273839, baseEnd_8273839] using wordTrace_append hprefix tailTrace_8273839
  have hstable : (prefixWord ++ tailWord_8273839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273839).length < 2 ^ (prefixWord ++ tailWord_8273839).sum := by decide
  have hdescent : baseEnd_8273839 < baseStart_8273839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273853 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_8273853 : Nat := 118140960795 + 8273853 * 2 ^ 59
def prefixEnd_8273853 : Nat := 4983230072969 + 3 ^ 40 * 8273853 * 2
def baseEnd_8273853 : Nat := 4248463453644522245786749

theorem tailTrace_8273853 : CollatzResearch.WordTrace tailWord_8273853 prefixEnd_8273853 4248463453644522245786749 := by
  unfold tailWord_8273853
  simp only [CollatzResearch.WordTrace]
  refine ⟨301772210494251117437930213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201181473662834078291953475 301772210494251117437930213)
  ·
    refine ⟨56582289467672084519611915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301772210494251117437930213 56582289467672084519611915)
    ·
      refine ⟨84873434201508126779417873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56582289467672084519611915 84873434201508126779417873)
      ·
        refine ⟨63655075651131095084563405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84873434201508126779417873 63655075651131095084563405)
        ·
          refine ⟨23870653369174160656711277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63655075651131095084563405 23870653369174160656711277)
          ·
            refine ⟨8951495013440310246266729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23870653369174160656711277 8951495013440310246266729)
            ·
              refine ⟨6713621260080232684700047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8951495013440310246266729 6713621260080232684700047)
              ·
                refine ⟨10070431890120349027050071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713621260080232684700047 10070431890120349027050071)
                ·
                  refine ⟨15105647835180523540575107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070431890120349027050071 15105647835180523540575107)
                  ·
                    refine ⟨22658471752770785310862661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15105647835180523540575107 22658471752770785310862661)
                    ·
                      refine ⟨4248463453644522245786749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22658471752770785310862661 4248463453644522245786749)
                      ·
                        rfl

theorem cell23_8273853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_8273853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273853 prefixEnd_8273853 := by exact prefixLift 8273853
  have htrace : WordTrace (prefixWord ++ tailWord_8273853) baseStart_8273853 baseEnd_8273853 := by
    simpa [prefixWord, tailWord_8273853, baseEnd_8273853] using wordTrace_append hprefix tailTrace_8273853
  have hstable : (prefixWord ++ tailWord_8273853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273853).length < 2 ^ (prefixWord ++ tailWord_8273853).sum := by decide
  have hdescent : baseEnd_8273853 < baseStart_8273853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273890 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_8273890 : Nat := 118140960795 + 8273890 * 2 ^ 59
def prefixEnd_8273890 : Nat := 4983230072969 + 3 ^ 40 * 8273890 * 2
def baseEnd_8273890 : Nat := 4248482452428738601024079

theorem tailTrace_8273890 : CollatzResearch.WordTrace tailWord_8273890 prefixEnd_8273890 4248482452428738601024079 := by
  unfold tailWord_8273890
  simp only [CollatzResearch.WordTrace]
  refine ⟨75443389998779268189256781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201182373330078048504684749 75443389998779268189256781)
  ·
    refine ⟨28291271249542225570971293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75443389998779268189256781 28291271249542225570971293)
    ·
      refine ⟨10609226718578334589114235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28291271249542225570971293 10609226718578334589114235)
      ·
        refine ⟨15913840077867501883671353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609226718578334589114235 15913840077867501883671353)
        ·
          refine ⟨11935380058400626412753515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15913840077867501883671353 11935380058400626412753515)
          ·
            refine ⟨17903070087600939619130273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935380058400626412753515 17903070087600939619130273)
            ·
              refine ⟨13427302565700704714347705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17903070087600939619130273 13427302565700704714347705)
              ·
                refine ⟨10070476924275528535760779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13427302565700704714347705 10070476924275528535760779)
                ·
                  refine ⟨15105715386413292803641169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070476924275528535760779 15105715386413292803641169)
                  ·
                    refine ⟨11329286539809969602730877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15105715386413292803641169 11329286539809969602730877)
                    ·
                      refine ⟨4248482452428738601024079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329286539809969602730877 4248482452428738601024079)
                      ·
                        rfl

theorem cell23_8273890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_8273890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273890 prefixEnd_8273890 := by exact prefixLift 8273890
  have htrace : WordTrace (prefixWord ++ tailWord_8273890) baseStart_8273890 baseEnd_8273890 := by
    simpa [prefixWord, tailWord_8273890, baseEnd_8273890] using wordTrace_append hprefix tailTrace_8273890
  have hstable : (prefixWord ++ tailWord_8273890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273890).length < 2 ^ (prefixWord ++ tailWord_8273890).sum := by decide
  have hdescent : baseEnd_8273890 < baseStart_8273890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273912 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_8273912 : Nat := 118140960795 + 8273912 * 2 ^ 59
def prefixEnd_8273912 : Nat := 4983230072969 + 3 ^ 40 * 8273912 * 2
def baseEnd_8273912 : Nat := 4248493749003137514948977

theorem tailTrace_8273912 : CollatzResearch.WordTrace tailWord_8273912 prefixEnd_8273912 4248493749003137514948977 := by
  unfold tailWord_8273912
  simp only [CollatzResearch.WordTrace]
  refine ⟨150887181200518685257163995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201182908267358247009551993 150887181200518685257163995)
  ·
    refine ⟨226330771800778027885745993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150887181200518685257163995 226330771800778027885745993)
    ·
      refine ⟨169748078850583520914309495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226330771800778027885745993 169748078850583520914309495)
      ·
        refine ⟨254622118275875281371464243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169748078850583520914309495 254622118275875281371464243)
        ·
          refine ⟨381933177413812922057196365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254622118275875281371464243 381933177413812922057196365)
          ·
            refine ⟨143224941530179845771448637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381933177413812922057196365 143224941530179845771448637)
            ·
              refine ⟨53709353073817442164293239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143224941530179845771448637 53709353073817442164293239)
              ·
                refine ⟨80564029610726163246439859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53709353073817442164293239 80564029610726163246439859)
                ·
                  refine ⟨120846044416089244869659789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80564029610726163246439859 120846044416089244869659789)
                  ·
                    refine ⟨45317266656033466826122421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120846044416089244869659789 45317266656033466826122421)
                    ·
                      refine ⟨4248493749003137514948977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45317266656033466826122421 4248493749003137514948977)
                      ·
                        rfl

theorem cell23_8273912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_8273912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273912 prefixEnd_8273912 := by exact prefixLift 8273912
  have htrace : WordTrace (prefixWord ++ tailWord_8273912) baseStart_8273912 baseEnd_8273912 := by
    simpa [prefixWord, tailWord_8273912, baseEnd_8273912] using wordTrace_append hprefix tailTrace_8273912
  have hstable : (prefixWord ++ tailWord_8273912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273912).length < 2 ^ (prefixWord ++ tailWord_8273912).sum := by decide
  have hdescent : baseEnd_8273912 < baseStart_8273912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8273960 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8273960 : Nat := 118140960795 + 8273960 * 2 ^ 59
def prefixEnd_8273960 : Nat := 4983230072969 + 3 ^ 40 * 8273960 * 2
def baseEnd_8273960 : Nat := 4248518396074553327148757

theorem tailTrace_8273960 : CollatzResearch.WordTrace tailWord_8273960 prefixEnd_8273960 4248518396074553327148757 := by
  unfold tailWord_8273960
  simp only [CollatzResearch.WordTrace]
  refine ⟨150888056552431737356037667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201184075403242316474716889 150888056552431737356037667)
  ·
    refine ⟨226332084828647606034056501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150888056552431737356037667 226332084828647606034056501)
    ·
      refine ⟨21218632952685713065692797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226332084828647606034056501 21218632952685713065692797)
      ·
        refine ⟨7956987357257142399634799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21218632952685713065692797 7956987357257142399634799)
        ·
          refine ⟨11935481035885713599452199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956987357257142399634799 11935481035885713599452199)
          ·
            refine ⟨17903221553828570399178299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935481035885713599452199 17903221553828570399178299)
            ·
              refine ⟨26854832330742855598767449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903221553828570399178299 26854832330742855598767449)
              ·
                refine ⟨20141124248057141699075587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26854832330742855598767449 20141124248057141699075587)
                ·
                  refine ⟨30211686372085712548613381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20141124248057141699075587 30211686372085712548613381)
                  ·
                    refine ⟨5664691194766071102865009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30211686372085712548613381 5664691194766071102865009)
                    ·
                      refine ⟨4248518396074553327148757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664691194766071102865009 4248518396074553327148757)
                      ·
                        rfl

theorem cell23_8273960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8273960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8273960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8273960 prefixEnd_8273960 := by exact prefixLift 8273960
  have htrace : WordTrace (prefixWord ++ tailWord_8273960) baseStart_8273960 baseEnd_8273960 := by
    simpa [prefixWord, tailWord_8273960, baseEnd_8273960] using wordTrace_append hprefix tailTrace_8273960
  have hstable : (prefixWord ++ tailWord_8273960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8273960).length < 2 ^ (prefixWord ++ tailWord_8273960).sum := by decide
  have hdescent : baseEnd_8273960 < baseStart_8273960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8273960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274013 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8274013 : Nat := 118140960795 + 8274013 * 2 ^ 59
def prefixEnd_8274013 : Nat := 4983230072969 + 3 ^ 40 * 8274013 * 2
def baseEnd_8274013 : Nat := 1416181870183080539928671

theorem tailTrace_8274013 : CollatzResearch.WordTrace tailWord_8274013 prefixEnd_8274013 1416181870183080539928671 := by
  unfold tailWord_8274013
  simp only [CollatzResearch.WordTrace]
  refine ⟨301778046173671464763754693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201185364115780976509169795 301778046173671464763754693)
  ·
    refine ⟨56583383657563399643204005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301778046173671464763754693 56583383657563399643204005)
    ·
      refine ⟨10609384435793137433100751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56583383657563399643204005 10609384435793137433100751)
      ·
        refine ⟨15914076653689706149651127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609384435793137433100751 15914076653689706149651127)
        ·
          refine ⟨23871114980534559224476691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15914076653689706149651127 23871114980534559224476691)
          ·
            refine ⟨35806672470801838836715037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23871114980534559224476691 35806672470801838836715037)
            ·
              refine ⟨13427502176550689563768139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35806672470801838836715037 13427502176550689563768139)
              ·
                refine ⟨20141253264826034345652209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427502176550689563768139 20141253264826034345652209)
                ·
                  refine ⟨15105939948619525759239157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20141253264826034345652209 15105939948619525759239157)
                  ·
                    refine ⟨1416181870183080539928671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15105939948619525759239157 1416181870183080539928671)
                    ·
                      rfl

theorem cell23_8274013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8274013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274013 prefixEnd_8274013 := by exact prefixLift 8274013
  have htrace : WordTrace (prefixWord ++ tailWord_8274013) baseStart_8274013 baseEnd_8274013 := by
    simpa [prefixWord, tailWord_8274013, baseEnd_8274013] using wordTrace_append hprefix tailTrace_8274013
  have hstable : (prefixWord ++ tailWord_8274013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274013).length < 2 ^ (prefixWord ++ tailWord_8274013).sum := by decide
  have hdescent : baseEnd_8274013 < baseStart_8274013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274016 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_8274016 : Nat := 118140960795 + 8274016 * 2 ^ 59
def prefixEnd_8274016 : Nat := 4983230072969 + 3 ^ 40 * 8274016 * 2
def baseEnd_8274016 : Nat := 4248547150991205108048499

theorem tailTrace_8274016 : CollatzResearch.WordTrace tailWord_8274016 prefixEnd_8274016 4248547150991205108048499 := by
  unfold tailWord_8274016
  simp only [CollatzResearch.WordTrace]
  refine ⟨150889077796330298138056951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201185437061773730850742601 150889077796330298138056951)
  ·
    refine ⟨226333616694495447207085427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150889077796330298138056951 226333616694495447207085427)
    ·
      refine ⟨339500425041743170810628141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226333616694495447207085427 339500425041743170810628141)
      ·
        refine ⟨127312659390653689053985553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339500425041743170810628141 127312659390653689053985553)
        ·
          refine ⟨95484494542990266790489165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127312659390653689053985553 95484494542990266790489165)
          ·
            refine ⟨35806685453621350046433437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95484494542990266790489165 35806685453621350046433437)
            ·
              refine ⟨13427507045108006267412539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35806685453621350046433437 13427507045108006267412539)
              ·
                refine ⟨20141260567662009401118809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427507045108006267412539 20141260567662009401118809)
                ·
                  refine ⟨15105945425746507050839107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20141260567662009401118809 15105945425746507050839107)
                  ·
                    refine ⟨22658918138619760576258661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15105945425746507050839107 22658918138619760576258661)
                    ·
                      refine ⟨4248547150991205108048499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22658918138619760576258661 4248547150991205108048499)
                      ·
                        rfl

theorem cell23_8274016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_8274016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274016 prefixEnd_8274016 := by exact prefixLift 8274016
  have htrace : WordTrace (prefixWord ++ tailWord_8274016) baseStart_8274016 baseEnd_8274016 := by
    simpa [prefixWord, tailWord_8274016, baseEnd_8274016] using wordTrace_append hprefix tailTrace_8274016
  have hstable : (prefixWord ++ tailWord_8274016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274016).length < 2 ^ (prefixWord ++ tailWord_8274016).sum := by decide
  have hdescent : baseEnd_8274016 < baseStart_8274016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274029 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_8274029 : Nat := 118140960795 + 8274029 * 2 ^ 59
def prefixEnd_8274029 : Nat := 4983230072969 + 3 ^ 40 * 8274029 * 2
def baseEnd_8274029 : Nat := 4248553826239713557185939

theorem tailTrace_8274029 : CollatzResearch.WordTrace tailWord_8274029 prefixEnd_8274029 4248553826239713557185939 := by
  unfold tailWord_8274029
  simp only [CollatzResearch.WordTrace]
  refine ⟨301778629741613499496337141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201185753161075666330891427 301778629741613499496337141)
  ·
    refine ⟨28291746538276265577781607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 301778629741613499496337141 28291746538276265577781607)
    ·
      refine ⟨42437619807414398366672411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28291746538276265577781607 42437619807414398366672411)
      ·
        refine ⟨63656429711121597550008617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42437619807414398366672411 63656429711121597550008617)
        ·
          refine ⟨47742322283341198162506463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63656429711121597550008617 47742322283341198162506463)
          ·
            refine ⟨71613483425011797243759695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47742322283341198162506463 71613483425011797243759695)
            ·
              refine ⟨107420225137517695865639543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71613483425011797243759695 107420225137517695865639543)
              ·
                refine ⟨161130337706276543798459315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107420225137517695865639543 161130337706276543798459315)
                ·
                  refine ⟨241695506559414815697688973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161130337706276543798459315 241695506559414815697688973)
                  ·
                    refine ⟨90635814959780555886633365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241695506559414815697688973 90635814959780555886633365)
                    ·
                      refine ⟨4248553826239713557185939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90635814959780555886633365 4248553826239713557185939)
                      ·
                        rfl

theorem cell23_8274029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_8274029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274029 prefixEnd_8274029 := by exact prefixLift 8274029
  have htrace : WordTrace (prefixWord ++ tailWord_8274029) baseStart_8274029 baseEnd_8274029 := by
    simpa [prefixWord, tailWord_8274029, baseEnd_8274029] using wordTrace_append hprefix tailTrace_8274029
  have hstable : (prefixWord ++ tailWord_8274029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274029).length < 2 ^ (prefixWord ++ tailWord_8274029).sum := by decide
  have hdescent : baseEnd_8274029 < baseStart_8274029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274039 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 8]
def baseStart_8274039 : Nat := 118140960795 + 8274039 * 2 ^ 59
def prefixEnd_8274039 : Nat := 4983230072969 + 3 ^ 40 * 8274039 * 2
def baseEnd_8274039 : Nat := 472062106782917613117877

theorem tailTrace_8274039 : CollatzResearch.WordTrace tailWord_8274039 prefixEnd_8274039 472062106782917613117877 := by
  unfold tailWord_8274039
  simp only [CollatzResearch.WordTrace]
  refine ⟨301778994471577271204201171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201185996314384847469467447 301778994471577271204201171)
  ·
    refine ⟨452668491707365906806301757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301778994471577271204201171 452668491707365906806301757)
    ·
      refine ⟨169750684390262215052363159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452668491707365906806301757 169750684390262215052363159)
      ·
        refine ⟨254626026585393322578544739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169750684390262215052363159 254626026585393322578544739)
        ·
          refine ⟨381939039878089983867817109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254626026585393322578544739 381939039878089983867817109)
          ·
            refine ⟨17903392494285467993803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381939039878089983867817109 17903392494285467993803927)
            ·
              refine ⟨26855088741428201990705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903392494285467993803927 26855088741428201990705891)
              ·
                refine ⟨40282633112142302986058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26855088741428201990705891 40282633112142302986058837)
                ·
                  refine ⟨472062106782917613117877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40282633112142302986058837 472062106782917613117877)
                  ·
                    rfl

theorem cell23_8274039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 8].length) (baseStart_8274039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274039 prefixEnd_8274039 := by exact prefixLift 8274039
  have htrace : WordTrace (prefixWord ++ tailWord_8274039) baseStart_8274039 baseEnd_8274039 := by
    simpa [prefixWord, tailWord_8274039, baseEnd_8274039] using wordTrace_append hprefix tailTrace_8274039
  have hstable : (prefixWord ++ tailWord_8274039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274039).length < 2 ^ (prefixWord ++ tailWord_8274039).sum := by decide
  have hdescent : baseEnd_8274039 < baseStart_8274039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274066 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_8274066 : Nat := 118140960795 + 8274066 * 2 ^ 59
def prefixEnd_8274066 : Nat := 4983230072969 + 3 ^ 40 * 8274066 * 2
def baseEnd_8274066 : Nat := 4248572825023929912423269

theorem tailTrace_8274066 : CollatzResearch.WordTrace tailWord_8274066 prefixEnd_8274066 4248572825023929912423269 := by
  unfold tailWord_8274066
  simp only [CollatzResearch.WordTrace]
  refine ⟨75444994810619863703858513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201186652828319636543622701 75444994810619863703858513)
  ·
    refine ⟨56583746107964897777893885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75444994810619863703858513 56583746107964897777893885)
    ·
      refine ⟨21218904790486836666710207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56583746107964897777893885 21218904790486836666710207)
      ·
        refine ⟨31828357185730255000065311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218904790486836666710207 31828357185730255000065311)
        ·
          refine ⟨47742535778595382500097967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31828357185730255000065311 47742535778595382500097967)
          ·
            refine ⟨71613803667893073750146951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47742535778595382500097967 71613803667893073750146951)
            ·
              refine ⟨107420705501839610625220427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71613803667893073750146951 107420705501839610625220427)
              ·
                refine ⟨161131058252759415937830641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107420705501839610625220427 161131058252759415937830641)
                ·
                  refine ⟨120848293689569561953372981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161131058252759415937830641 120848293689569561953372981)
                  ·
                    refine ⟨11329527533397146433128717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120848293689569561953372981 11329527533397146433128717)
                    ·
                      refine ⟨4248572825023929912423269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329527533397146433128717 4248572825023929912423269)
                      ·
                        rfl

theorem cell23_8274066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_8274066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274066 prefixEnd_8274066 := by exact prefixLift 8274066
  have htrace : WordTrace (prefixWord ++ tailWord_8274066) baseStart_8274066 baseEnd_8274066 := by
    simpa [prefixWord, tailWord_8274066, baseEnd_8274066] using wordTrace_append hprefix tailTrace_8274066
  have hstable : (prefixWord ++ tailWord_8274066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274066).length < 2 ^ (prefixWord ++ tailWord_8274066).sum := by decide
  have hdescent : baseEnd_8274066 < baseStart_8274066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274094 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_8274094 : Nat := 118140960795 + 8274094 * 2 ^ 59
def prefixEnd_8274094 : Nat := 4983230072969 + 3 ^ 40 * 8274094 * 2
def baseEnd_8274094 : Nat := 1416195734160751934291047

theorem tailTrace_8274094 : CollatzResearch.WordTrace tailWord_8274094 prefixEnd_8274094 1416195734160751934291047 := by
  unfold tailWord_8274094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722625060797251949681667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201187333657585343731635557 37722625060797251949681667)
  ·
    refine ⟨56583937591195877924522501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37722625060797251949681667 56583937591195877924522501)
    ·
      refine ⟨10609488298349227110847969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56583937591195877924522501 10609488298349227110847969)
      ·
        refine ⟨7957116223761920333135977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10609488298349227110847969 7957116223761920333135977)
        ·
          refine ⟨5967837167821440249851983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7957116223761920333135977 5967837167821440249851983)
          ·
            refine ⟨8951755751732160374777975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967837167821440249851983 8951755751732160374777975)
            ·
              refine ⟨13427633627598240562166963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951755751732160374777975 13427633627598240562166963)
              ·
                refine ⟨20141450441397360843250445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427633627598240562166963 20141450441397360843250445)
                ·
                  refine ⟨7553043915524010316218917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20141450441397360843250445 7553043915524010316218917)
                  ·
                    refine ⟨1416195734160751934291047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553043915524010316218917 1416195734160751934291047)
                    ·
                      rfl

theorem cell23_8274094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_8274094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274094 prefixEnd_8274094 := by exact prefixLift 8274094
  have htrace : WordTrace (prefixWord ++ tailWord_8274094) baseStart_8274094 baseEnd_8274094 := by
    simpa [prefixWord, tailWord_8274094, baseEnd_8274094] using wordTrace_append hprefix tailTrace_8274094
  have hstable : (prefixWord ++ tailWord_8274094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274094).length < 2 ^ (prefixWord ++ tailWord_8274094).sum := by decide
  have hdescent : baseEnd_8274094 < baseStart_8274094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274123 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 5, 2, 2]
def baseStart_8274123 : Nat := 118140960795 + 8274123 * 2 ^ 59
def prefixEnd_8274123 : Nat := 4983230072969 + 3 ^ 40 * 8274123 * 2
def baseEnd_8274123 : Nat := 4248602093421236189410507

theorem tailTrace_8274123 : CollatzResearch.WordTrace tailWord_8274123 prefixEnd_8274123 4248602093421236189410507 := by
  unfold tailWord_8274123
  simp only [CollatzResearch.WordTrace]
  refine ⟨301782058203272953550259023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201188038802181969033506015 301782058203272953550259023)
  ·
    refine ⟨452673087304909430325388535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301782058203272953550259023 452673087304909430325388535)
    ·
      refine ⟨679009630957364145488082803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452673087304909430325388535 679009630957364145488082803)
      ·
        refine ⟨1018514446436046218232124205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679009630957364145488082803 1018514446436046218232124205)
        ·
          refine ⟨381942917413517331837046577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1018514446436046218232124205 381942917413517331837046577)
          ·
            refine ⟨286457188060137998877784933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381942917413517331837046577 286457188060137998877784933)
            ·
              refine ⟨53710722761275874789584675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286457188060137998877784933 53710722761275874789584675)
              ·
                refine ⟨80566084141913812184377013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53710722761275874789584675 80566084141913812184377013)
                ·
                  refine ⟨7553070388304419892285345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80566084141913812184377013 7553070388304419892285345)
                  ·
                    refine ⟨5664802791228314919214009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7553070388304419892285345 5664802791228314919214009)
                    ·
                      refine ⟨4248602093421236189410507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664802791228314919214009 4248602093421236189410507)
                      ·
                        rfl

theorem cell23_8274123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2, 2].length) (baseStart_8274123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274123 prefixEnd_8274123 := by exact prefixLift 8274123
  have htrace : WordTrace (prefixWord ++ tailWord_8274123) baseStart_8274123 baseEnd_8274123 := by
    simpa [prefixWord, tailWord_8274123, baseEnd_8274123] using wordTrace_append hprefix tailTrace_8274123
  have hstable : (prefixWord ++ tailWord_8274123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274123).length < 2 ^ (prefixWord ++ tailWord_8274123).sum := by decide
  have hdescent : baseEnd_8274123 < baseStart_8274123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274129 : List Nat := [1, 2, 2, 1, 2, 2, 4, 9]
def baseStart_8274129 : Nat := 118140960795 + 8274129 * 2 ^ 59
def prefixEnd_8274129 : Nat := 4983230072969 + 3 ^ 40 * 8274129 * 2
def baseEnd_8274129 : Nat := 157355747196487524664277

theorem tailTrace_8274129 : CollatzResearch.WordTrace tailWord_8274129 prefixEnd_8274129 157355747196487524664277 := by
  unfold tailWord_8274129
  simp only [CollatzResearch.WordTrace]
  refine ⟨301782277041251216574977441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201188184694167477716651627 301782277041251216574977441)
  ·
    refine ⟨226336707780938412431233081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301782277041251216574977441 226336707780938412431233081)
    ·
      refine ⟨169752530835703809323424811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226336707780938412431233081 169752530835703809323424811)
      ·
        refine ⟨254628796253555713985137217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169752530835703809323424811 254628796253555713985137217)
        ·
          refine ⟨190971597190166785488852913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254628796253555713985137217 190971597190166785488852913)
          ·
            refine ⟨143228697892625089116639685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190971597190166785488852913 143228697892625089116639685)
            ·
              refine ⟨26855380854867204209369941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143228697892625089116639685 26855380854867204209369941)
              ·
                refine ⟨157355747196487524664277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26855380854867204209369941 157355747196487524664277)
                ·
                  rfl

theorem cell23_8274129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 9].length) (baseStart_8274129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274129 prefixEnd_8274129 := by exact prefixLift 8274129
  have htrace : WordTrace (prefixWord ++ tailWord_8274129) baseStart_8274129 baseEnd_8274129 := by
    simpa [prefixWord, tailWord_8274129, baseEnd_8274129] using wordTrace_append hprefix tailTrace_8274129
  have hstable : (prefixWord ++ tailWord_8274129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274129).length < 2 ^ (prefixWord ++ tailWord_8274129).sum := by decide
  have hdescent : baseEnd_8274129 < baseStart_8274129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274133 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_8274133 : Nat := 118140960795 + 8274133 * 2 ^ 59
def prefixEnd_8274133 : Nat := 4983230072969 + 3 ^ 40 * 8274133 * 2
def baseEnd_8274133 : Nat := 1416202409409260383428487

theorem tailTrace_8274133 : CollatzResearch.WordTrace tailWord_8274133 prefixEnd_8274133 1416202409409260383428487 := by
  unfold tailWord_8274133
  simp only [CollatzResearch.WordTrace]
  refine ⟨301782422933236725258123053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201188281955491150172082035 301782422933236725258123053)
  ·
    refine ⟨113168408599963771971796145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301782422933236725258123053 113168408599963771971796145)
    ·
      refine ⟨84876306449972828978847109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113168408599963771971796145 84876306449972828978847109)
      ·
        refine ⟨15914307459369905433533833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84876306449972828978847109 15914307459369905433533833)
        ·
          refine ⟨11935730594527429075150375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15914307459369905433533833 11935730594527429075150375)
          ·
            refine ⟨17903595891791143612725563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935730594527429075150375 17903595891791143612725563)
            ·
              refine ⟨26855393837686715419088345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903595891791143612725563 26855393837686715419088345)
              ·
                refine ⟨20141545378265036564316259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26855393837686715419088345 20141545378265036564316259)
                ·
                  refine ⟨30212318067397554846474389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20141545378265036564316259 30212318067397554846474389)
                  ·
                    refine ⟨1416202409409260383428487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30212318067397554846474389 1416202409409260383428487)
                    ·
                      rfl

theorem cell23_8274133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_8274133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274133 prefixEnd_8274133 := by exact prefixLift 8274133
  have htrace : WordTrace (prefixWord ++ tailWord_8274133) baseStart_8274133 baseEnd_8274133 := by
    simpa [prefixWord, tailWord_8274133, baseEnd_8274133] using wordTrace_append hprefix tailTrace_8274133
  have hstable : (prefixWord ++ tailWord_8274133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274133).length < 2 ^ (prefixWord ++ tailWord_8274133).sum := by decide
  have hdescent : baseEnd_8274133 < baseStart_8274133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274136 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_8274136 : Nat := 118140960795 + 8274136 * 2 ^ 59
def prefixEnd_8274136 : Nat := 4983230072969 + 3 ^ 40 * 8274136 * 2
def baseEnd_8274136 : Nat := 4248608768669744638547947

theorem tailTrace_8274136 : CollatzResearch.WordTrace tailWord_8274136 prefixEnd_8274136 4248608768669744638547947 := by
  unfold tailWord_8274136
  simp only [CollatzResearch.WordTrace]
  refine ⟨150891266176112928385241131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201188354901483904513654841 150891266176112928385241131)
  ·
    refine ⟨226336899264169392577861697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150891266176112928385241131 226336899264169392577861697)
    ·
      refine ⟨169752674448127044433396273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226336899264169392577861697 169752674448127044433396273)
      ·
        refine ⟨127314505836095283325047205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169752674448127044433396273 127314505836095283325047205)
        ·
          refine ⟨23871469844267865623446351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127314505836095283325047205 23871469844267865623446351)
          ·
            refine ⟨35807204766401798435169527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23871469844267865623446351 35807204766401798435169527)
            ·
              refine ⟨53710807149602697652754291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35807204766401798435169527 53710807149602697652754291)
              ·
                refine ⟨80566210724404046479131437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53710807149602697652754291 80566210724404046479131437)
                ·
                  refine ⟨30212329021651517429674289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80566210724404046479131437 30212329021651517429674289)
                  ·
                    refine ⟨22659246766238638072255717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30212329021651517429674289 22659246766238638072255717)
                    ·
                      refine ⟨4248608768669744638547947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22659246766238638072255717 4248608768669744638547947)
                      ·
                        rfl

theorem cell23_8274136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_8274136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274136 prefixEnd_8274136 := by exact prefixLift 8274136
  have htrace : WordTrace (prefixWord ++ tailWord_8274136) baseStart_8274136 baseEnd_8274136 := by
    simpa [prefixWord, tailWord_8274136, baseEnd_8274136] using wordTrace_append hprefix tailTrace_8274136
  have hstable : (prefixWord ++ tailWord_8274136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274136).length < 2 ^ (prefixWord ++ tailWord_8274136).sum := by decide
  have hdescent : baseEnd_8274136 < baseStart_8274136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274156 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_8274156 : Nat := 118140960795 + 8274156 * 2 ^ 59
def prefixEnd_8274156 : Nat := 4983230072969 + 3 ^ 40 * 8274156 * 2
def baseEnd_8274156 : Nat := 4248619038282834560297855

theorem tailTrace_8274156 : CollatzResearch.WordTrace tailWord_8274156 prefixEnd_8274156 4248619038282834560297855 := by
  unfold tailWord_8274156
  simp only [CollatzResearch.WordTrace]
  refine ⟨150891630906076700093105161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201188841208102266790806881 150891630906076700093105161)
  ·
    refine ⟨113168723179557525069828871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150891630906076700093105161 113168723179557525069828871)
    ·
      refine ⟨169753084769336287604743307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113168723179557525069828871 169753084769336287604743307)
      ·
        refine ⟨254629627154004431407114961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169753084769336287604743307 254629627154004431407114961)
        ·
          refine ⟨190972220365503323555336221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254629627154004431407114961 190972220365503323555336221)
          ·
            refine ⟨71614582637063746333251083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190972220365503323555336221 71614582637063746333251083)
            ·
              refine ⟨107421873955595619499876625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71614582637063746333251083 107421873955595619499876625)
              ·
                refine ⟨80566405466696714624907469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107421873955595619499876625 80566405466696714624907469)
                ·
                  refine ⟨30212402050011267984340301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80566405466696714624907469 30212402050011267984340301)
                  ·
                    refine ⟨11329650768754225494127613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30212402050011267984340301 11329650768754225494127613)
                    ·
                      refine ⟨4248619038282834560297855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329650768754225494127613 4248619038282834560297855)
                      ·
                        rfl

theorem cell23_8274156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_8274156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274156 prefixEnd_8274156 := by exact prefixLift 8274156
  have htrace : WordTrace (prefixWord ++ tailWord_8274156) baseStart_8274156 baseEnd_8274156 := by
    simpa [prefixWord, tailWord_8274156, baseEnd_8274156] using wordTrace_append hprefix tailTrace_8274156
  have hstable : (prefixWord ++ tailWord_8274156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274156).length < 2 ^ (prefixWord ++ tailWord_8274156).sum := by decide
  have hdescent : baseEnd_8274156 < baseStart_8274156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274166 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_8274166 : Nat := 118140960795 + 8274166 * 2 ^ 59
def prefixEnd_8274166 : Nat := 4983230072969 + 3 ^ 40 * 8274166 * 2
def baseEnd_8274166 : Nat := 4248624173089379521172809

theorem tailTrace_8274166 : CollatzResearch.WordTrace tailWord_8274166 prefixEnd_8274166 4248624173089379521172809 := by
  unfold tailWord_8274166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18861476658882323243379647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201189084361411447929382901 18861476658882323243379647)
  ·
    refine ⟨28292214988323484865069471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18861476658882323243379647 28292214988323484865069471)
    ·
      refine ⟨42438322482485227297604207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28292214988323484865069471 42438322482485227297604207)
      ·
        refine ⟨63657483723727840946406311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42438322482485227297604207 63657483723727840946406311)
        ·
          refine ⟨95486225585591761419609467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63657483723727840946406311 95486225585591761419609467)
          ·
            refine ⟨143229338378387642129414201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95486225585591761419609467 143229338378387642129414201)
            ·
              refine ⟨107422003783790731597060651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143229338378387642129414201 107422003783790731597060651)
              ·
                refine ⟨161133005675686097395590977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107422003783790731597060651 161133005675686097395590977)
                ·
                  refine ⟨120849754256764573046693233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161133005675686097395590977 120849754256764573046693233)
                  ·
                    refine ⟨90637315692573429785019925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120849754256764573046693233 90637315692573429785019925)
                    ·
                      refine ⟨4248624173089379521172809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90637315692573429785019925 4248624173089379521172809)
                      ·
                        rfl

theorem cell23_8274166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_8274166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274166 prefixEnd_8274166 := by exact prefixLift 8274166
  have htrace : WordTrace (prefixWord ++ tailWord_8274166) baseStart_8274166 baseEnd_8274166 := by
    simpa [prefixWord, tailWord_8274166, baseEnd_8274166] using wordTrace_append hprefix tailTrace_8274166
  have hstable : (prefixWord ++ tailWord_8274166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274166).length < 2 ^ (prefixWord ++ tailWord_8274166).sum := by decide
  have hdescent : baseEnd_8274166 < baseStart_8274166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274200 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_8274200 : Nat := 118140960795 + 8274200 * 2 ^ 59
def prefixEnd_8274200 : Nat := 4983230072969 + 3 ^ 40 * 8274200 * 2
def baseEnd_8274200 : Nat := 4248641631431632388147653

theorem tailTrace_8274200 : CollatzResearch.WordTrace tailWord_8274200 prefixEnd_8274200 4248641631431632388147653 := by
  unfold tailWord_8274200
  simp only [CollatzResearch.WordTrace]
  refine ⟨150892433311996997850406027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201189911082662663800541369 150892433311996997850406027)
  ·
    refine ⟨226338649967995496775609041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150892433311996997850406027 226338649967995496775609041)
    ·
      refine ⟨169753987475996622581706781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226338649967995496775609041 169753987475996622581706781)
      ·
        refine ⟨63657745303498733468140043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169753987475996622581706781 63657745303498733468140043)
        ·
          refine ⟨95486617955248100202210065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63657745303498733468140043 95486617955248100202210065)
          ·
            refine ⟨71614963466436075151657549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95486617955248100202210065 71614963466436075151657549)
            ·
              refine ⟨26855611299913528181871581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71614963466436075151657549 26855611299913528181871581)
              ·
                refine ⟨10070854237467573068201843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26855611299913528181871581 10070854237467573068201843)
                ·
                  refine ⟨15106281356201359602302765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10070854237467573068201843 15106281356201359602302765)
                  ·
                    refine ⟨5664855508575509850863537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15106281356201359602302765 5664855508575509850863537)
                    ·
                      refine ⟨4248641631431632388147653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664855508575509850863537 4248641631431632388147653)
                      ·
                        rfl

theorem cell23_8274200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_8274200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274200 prefixEnd_8274200 := by exact prefixLift 8274200
  have htrace : WordTrace (prefixWord ++ tailWord_8274200) baseStart_8274200 baseEnd_8274200 := by
    simpa [prefixWord, tailWord_8274200, baseEnd_8274200] using wordTrace_append hprefix tailTrace_8274200
  have hstable : (prefixWord ++ tailWord_8274200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274200).length < 2 ^ (prefixWord ++ tailWord_8274200).sum := by decide
  have hdescent : baseEnd_8274200 < baseStart_8274200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274207 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_8274207 : Nat := 118140960795 + 8274207 * 2 ^ 59
def prefixEnd_8274207 : Nat := 4983230072969 + 3 ^ 40 * 8274207 * 2
def baseEnd_8274207 : Nat := 4248645225796213860760121

theorem tailTrace_8274207 : CollatzResearch.WordTrace tailWord_8274207 prefixEnd_8274207 4248645225796213860760121 := by
  unfold tailWord_8274207
  simp only [CollatzResearch.WordTrace]
  refine ⟨301785121934968635896316875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201190081289979090597544583 301785121934968635896316875)
  ·
    refine ⟨452677682902452953844475313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301785121934968635896316875 452677682902452953844475313)
    ·
      refine ⟨339508262176839715383356485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452677682902452953844475313 339508262176839715383356485)
      ·
        refine ⟨63657799158157446634379341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339508262176839715383356485 63657799158157446634379341)
        ·
          refine ⟨23871674684309042487892253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63657799158157446634379341 23871674684309042487892253)
          ·
            refine ⟨8951878006615890932959595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23871674684309042487892253 8951878006615890932959595)
            ·
              refine ⟨13427817009923836399439393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951878006615890932959595 13427817009923836399439393)
              ·
                refine ⟨10070862757442877299579545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13427817009923836399439393 10070862757442877299579545)
                ·
                  refine ⟨7553147068082157974684659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10070862757442877299579545 7553147068082157974684659)
                  ·
                    refine ⟨11329720602123236962026989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553147068082157974684659 11329720602123236962026989)
                    ·
                      refine ⟨4248645225796213860760121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11329720602123236962026989 4248645225796213860760121)
                      ·
                        rfl

theorem cell23_8274207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_8274207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274207 prefixEnd_8274207 := by exact prefixLift 8274207
  have htrace : WordTrace (prefixWord ++ tailWord_8274207) baseStart_8274207 baseEnd_8274207 := by
    simpa [prefixWord, tailWord_8274207, baseEnd_8274207] using wordTrace_append hprefix tailTrace_8274207
  have hstable : (prefixWord ++ tailWord_8274207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274207).length < 2 ^ (prefixWord ++ tailWord_8274207).sum := by decide
  have hdescent : baseEnd_8274207 < baseStart_8274207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274236 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 7]
def baseStart_8274236 : Nat := 118140960795 + 8274236 * 2 ^ 59
def prefixEnd_8274236 : Nat := 4983230072969 + 3 ^ 40 * 8274236 * 2
def baseEnd_8274236 : Nat := 472073346303910471921943

theorem tailTrace_8274236 : CollatzResearch.WordTrace tailWord_8274236 prefixEnd_8274236 472073346303910471921943 := by
  unfold tailWord_8274236
  simp only [CollatzResearch.WordTrace]
  refine ⟨150893089825931786924561281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201190786434575715899415041 150893089825931786924561281)
  ·
    refine ⟨113169817369448840193420961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150893089825931786924561281 113169817369448840193420961)
    ·
      refine ⟨84877363027086630145065721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113169817369448840193420961 84877363027086630145065721)
      ·
        refine ⟨63658022270314972608799291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84877363027086630145065721 63658022270314972608799291)
        ·
          refine ⟨95487033405472458913198937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63658022270314972608799291 95487033405472458913198937)
          ·
            refine ⟨71615275054104344184899203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95487033405472458913198937 71615275054104344184899203)
            ·
              refine ⟨107422912581156516277348805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71615275054104344184899203 107422912581156516277348805)
              ·
                refine ⟨20141796108966846802002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107422912581156516277348805 20141796108966846802002901)
                ·
                  refine ⟨472073346303910471921943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20141796108966846802002901 472073346303910471921943)
                  ·
                    rfl

theorem cell23_8274236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_8274236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274236 prefixEnd_8274236 := by exact prefixLift 8274236
  have htrace : WordTrace (prefixWord ++ tailWord_8274236) baseStart_8274236 baseEnd_8274236 := by
    simpa [prefixWord, tailWord_8274236, baseEnd_8274236] using wordTrace_append hprefix tailTrace_8274236
  have hstable : (prefixWord ++ tailWord_8274236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274236).length < 2 ^ (prefixWord ++ tailWord_8274236).sum := by decide
  have hdescent : baseEnd_8274236 < baseStart_8274236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274303 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 6, 2]
def baseStart_8274303 : Nat := 118140960795 + 8274303 * 2 ^ 59
def prefixEnd_8274303 : Nat := 4983230072969 + 3 ^ 40 * 8274303 * 2
def baseEnd_8274303 : Nat := 4248694519939045485159679

theorem tailTrace_8274303 : CollatzResearch.WordTrace tailWord_8274303 prefixEnd_8274303 4248694519939045485159679 := by
  unfold tailWord_8274303
  simp only [CollatzResearch.WordTrace]
  refine ⟨301788623342620844291811563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201192415561747229527874375 301788623342620844291811563)
  ·
    refine ⟨452682935013931266437717345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301788623342620844291811563 452682935013931266437717345)
    ·
      refine ⟨339512201260448449828288009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452682935013931266437717345 339512201260448449828288009)
      ·
        refine ⟨254634150945336337371216007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339512201260448449828288009 254634150945336337371216007)
        ·
          refine ⟨381951226418004506056824011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254634150945336337371216007 381951226418004506056824011)
          ·
            refine ⟨572926839627006759085236017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381951226418004506056824011 572926839627006759085236017)
            ·
              refine ⟨429695129720255069313927013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572926839627006759085236017 429695129720255069313927013)
              ·
                refine ⟨80567836822547825496361315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429695129720255069313927013 80567836822547825496361315)
                ·
                  refine ⟨120851755233821738244541973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80567836822547825496361315 120851755233821738244541973)
                  ·
                    refine ⟨5664926026585393980212905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120851755233821738244541973 5664926026585393980212905)
                    ·
                      refine ⟨4248694519939045485159679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5664926026585393980212905 4248694519939045485159679)
                      ·
                        rfl

theorem cell23_8274303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_8274303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274303 prefixEnd_8274303 := by exact prefixLift 8274303
  have htrace : WordTrace (prefixWord ++ tailWord_8274303) baseStart_8274303 baseEnd_8274303 := by
    simpa [prefixWord, tailWord_8274303, baseEnd_8274303] using wordTrace_append hprefix tailTrace_8274303
  have hstable : (prefixWord ++ tailWord_8274303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274303).length < 2 ^ (prefixWord ++ tailWord_8274303).sum := by decide
  have hdescent : baseEnd_8274303 < baseStart_8274303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274364 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_8274364 : Nat := 118140960795 + 8274364 * 2 ^ 59
def prefixEnd_8274364 : Nat := 4983230072969 + 3 ^ 40 * 8274364 * 2
def baseEnd_8274364 : Nat := 1416241947419656582165633

theorem tailTrace_8274364 : CollatzResearch.WordTrace tailWord_8274364 prefixEnd_8274364 1416241947419656582165633 := by
  unfold tailWord_8274364
  simp only [CollatzResearch.WordTrace]
  refine ⟨150895424097699925854891073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201193898796933234473188097 150895424097699925854891073)
  ·
    refine ⟨113171568073274944391168305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150895424097699925854891073 113171568073274944391168305)
    ·
      refine ⟨84878676054956208293376229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113171568073274944391168305 84878676054956208293376229)
      ·
        refine ⟨15914751760304289055008043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84878676054956208293376229 15914751760304289055008043)
        ·
          refine ⟨23872127640456433582512065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15914751760304289055008043 23872127640456433582512065)
          ·
            refine ⟨17904095730342325186884049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23872127640456433582512065 17904095730342325186884049)
            ·
              refine ⟨13428071797756743890163037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17904095730342325186884049 13428071797756743890163037)
              ·
                refine ⟨5035526924158778958811139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13428071797756743890163037 5035526924158778958811139)
                ·
                  refine ⟨7553290386238168438216709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035526924158778958811139 7553290386238168438216709)
                  ·
                    refine ⟨1416241947419656582165633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553290386238168438216709 1416241947419656582165633)
                    ·
                      rfl

theorem cell23_8274364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_8274364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274364 prefixEnd_8274364 := by exact prefixLift 8274364
  have htrace : WordTrace (prefixWord ++ tailWord_8274364) baseStart_8274364 baseEnd_8274364 := by
    simpa [prefixWord, tailWord_8274364, baseEnd_8274364] using wordTrace_append hprefix tailTrace_8274364
  have hstable : (prefixWord ++ tailWord_8274364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274364).length < 2 ^ (prefixWord ++ tailWord_8274364).sum := by decide
  have hdescent : baseEnd_8274364 < baseStart_8274364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274433 : List Nat := [1, 2, 4, 1, 3, 1, 11]
def baseStart_8274433 : Nat := 118140960795 + 8274433 * 2 ^ 59
def prefixEnd_8274433 : Nat := 4983230072969 + 3 ^ 40 * 8274433 * 2
def baseEnd_8274433 : Nat := 52453842869433703414001

theorem tailTrace_8274433 : CollatzResearch.WordTrace tailWord_8274433 prefixEnd_8274433 52453842869433703414001 := by
  unfold tailWord_8274433
  simp only [CollatzResearch.WordTrace]
  refine ⟨301793364832149876494043953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201195576554766584329362635 301793364832149876494043953)
  ·
    refine ⟨226345023624112407370532965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 301793364832149876494043953 226345023624112407370532965)
    ·
      refine ⟨42439691929521076381974931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226345023624112407370532965 42439691929521076381974931)
      ·
        refine ⟨63659537894281614572962397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42439691929521076381974931 63659537894281614572962397)
        ·
          refine ⟨23872326710355605464860899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63659537894281614572962397 23872326710355605464860899)
          ·
            refine ⟨35808490065533408197291349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23872326710355605464860899 35808490065533408197291349)
            ·
              refine ⟨52453842869433703414001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35808490065533408197291349 52453842869433703414001)
              ·
                rfl

theorem cell23_8274433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 11].length) (baseStart_8274433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274433 prefixEnd_8274433 := by exact prefixLift 8274433
  have htrace : WordTrace (prefixWord ++ tailWord_8274433) baseStart_8274433 baseEnd_8274433 := by
    simpa [prefixWord, tailWord_8274433, baseEnd_8274433] using wordTrace_append hprefix tailTrace_8274433
  have hstable : (prefixWord ++ tailWord_8274433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274433).length < 2 ^ (prefixWord ++ tailWord_8274433).sum := by decide
  have hdescent : baseEnd_8274433 < baseStart_8274433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274438 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_8274438 : Nat := 118140960795 + 8274438 * 2 ^ 59
def prefixEnd_8274438 : Nat := 4983230072969 + 3 ^ 40 * 8274438 * 2
def baseEnd_8274438 : Nat := 4248763839827402456971559

theorem tailTrace_8274438 : CollatzResearch.WordTrace tailWord_8274438 prefixEnd_8274438 4248763839827402456971559 := by
  unfold tailWord_8274438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431048349910367573374249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201195698131421174898650645 9431048349910367573374249)
  ·
    refine ⟨7073286262432775680030687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9431048349910367573374249 7073286262432775680030687)
    ·
      refine ⟨10609929393649163520046031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073286262432775680030687 10609929393649163520046031)
      ·
        refine ⟨15914894090473745280069047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609929393649163520046031 15914894090473745280069047)
        ·
          refine ⟨23872341135710617920103571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15914894090473745280069047 23872341135710617920103571)
          ·
            refine ⟨35808511703565926880155357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23872341135710617920103571 35808511703565926880155357)
            ·
              refine ⟨13428191888837222580058259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35808511703565926880155357 13428191888837222580058259)
              ·
                refine ⟨20142287833255833870087389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428191888837222580058259 20142287833255833870087389)
                ·
                  refine ⟨7553357937470937701282771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20142287833255833870087389 7553357937470937701282771)
                  ·
                    refine ⟨11330036906206406551924157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553357937470937701282771 11330036906206406551924157)
                    ·
                      refine ⟨4248763839827402456971559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11330036906206406551924157 4248763839827402456971559)
                      ·
                        rfl

theorem cell23_8274438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_8274438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274438 prefixEnd_8274438 := by exact prefixLift 8274438
  have htrace : WordTrace (prefixWord ++ tailWord_8274438) baseStart_8274438 baseEnd_8274438 := by
    simpa [prefixWord, tailWord_8274438, baseEnd_8274438] using wordTrace_append hprefix tailTrace_8274438
  have hstable : (prefixWord ++ tailWord_8274438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274438).length < 2 ^ (prefixWord ++ tailWord_8274438).sum := by decide
  have hdescent : baseEnd_8274438 < baseStart_8274438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274444 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_8274444 : Nat := 118140960795 + 8274444 * 2 ^ 59
def prefixEnd_8274444 : Nat := 4983230072969 + 3 ^ 40 * 8274444 * 2
def baseEnd_8274444 : Nat := 4248766920711329433496531

theorem tailTrace_8274444 : CollatzResearch.WordTrace tailWord_8274444 prefixEnd_8274444 4248766920711329433496531 := by
  unfold tailWord_8274444
  simp only [CollatzResearch.WordTrace]
  refine ⟨150896883017555012686347193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201195844023406683581796257 150896883017555012686347193)
  ·
    refine ⟨113172662263166259514760395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150896883017555012686347193 113172662263166259514760395)
    ·
      refine ⟨169758993394749389272140593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113172662263166259514760395 169758993394749389272140593)
      ·
        refine ⟨127319245046062041954105445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169758993394749389272140593 127319245046062041954105445)
        ·
          refine ⟨23872358446136632866394771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127319245046062041954105445 23872358446136632866394771)
          ·
            refine ⟨35808537669204949299592157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23872358446136632866394771 35808537669204949299592157)
            ·
              refine ⟨13428201625951855987347059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35808537669204949299592157 13428201625951855987347059)
              ·
                refine ⟨20142302438927783981020589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428201625951855987347059 20142302438927783981020589)
                ·
                  refine ⟨7553363414597918992882721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20142302438927783981020589 7553363414597918992882721)
                  ·
                    refine ⟨5665022560948439244662041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7553363414597918992882721 5665022560948439244662041)
                    ·
                      refine ⟨4248766920711329433496531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665022560948439244662041 4248766920711329433496531)
                      ·
                        rfl

theorem cell23_8274444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_8274444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274444 prefixEnd_8274444 := by exact prefixLift 8274444
  have htrace : WordTrace (prefixWord ++ tailWord_8274444) baseStart_8274444 baseEnd_8274444 := by
    simpa [prefixWord, tailWord_8274444, baseEnd_8274444] using wordTrace_append hprefix tailTrace_8274444
  have hstable : (prefixWord ++ tailWord_8274444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274444).length < 2 ^ (prefixWord ++ tailWord_8274444).sum := by decide
  have hdescent : baseEnd_8274444 < baseStart_8274444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274453 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_8274453 : Nat := 118140960795 + 8274453 * 2 ^ 59
def prefixEnd_8274453 : Nat := 4983230072969 + 3 ^ 40 * 8274453 * 2
def baseEnd_8274453 : Nat := 4248771542037219898283989

theorem tailTrace_8274453 : CollatzResearch.WordTrace tailWord_8274453 prefixEnd_8274453 4248771542037219898283989 := by
  unfold tailWord_8274453
  simp only [CollatzResearch.WordTrace]
  refine ⟨301794094292077419909772013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201196062861384946606514675 301794094292077419909772013)
  ·
    refine ⟨113172785359529032466164505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301794094292077419909772013 113172785359529032466164505)
    ·
      refine ⟨84879589019646774349623379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113172785359529032466164505 84879589019646774349623379)
      ·
        refine ⟨127319383529470161524435069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84879589019646774349623379 127319383529470161524435069)
        ·
          refine ⟨47744768823551310571663151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127319383529470161524435069 47744768823551310571663151)
          ·
            refine ⟨71617153235326965857494727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47744768823551310571663151 71617153235326965857494727)
            ·
              refine ⟨107425729852990448786242091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71617153235326965857494727 107425729852990448786242091)
              ·
                refine ⟨161138594779485673179363137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107425729852990448786242091 161138594779485673179363137)
                ·
                  refine ⟨120853946084614254884522353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161138594779485673179363137 120853946084614254884522353)
                  ·
                    refine ⟨90640459563460691163391765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120853946084614254884522353 90640459563460691163391765)
                    ·
                      refine ⟨4248771542037219898283989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90640459563460691163391765 4248771542037219898283989)
                      ·
                        rfl

theorem cell23_8274453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_8274453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274453 prefixEnd_8274453 := by exact prefixLift 8274453
  have htrace : WordTrace (prefixWord ++ tailWord_8274453) baseStart_8274453 baseEnd_8274453 := by
    simpa [prefixWord, tailWord_8274453, baseEnd_8274453] using wordTrace_append hprefix tailTrace_8274453
  have hstable : (prefixWord ++ tailWord_8274453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274453).length < 2 ^ (prefixWord ++ tailWord_8274453).sum := by decide
  have hdescent : baseEnd_8274453 < baseStart_8274453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274517 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_8274517 : Nat := 118140960795 + 8274517 * 2 ^ 59
def prefixEnd_8274517 : Nat := 4983230072969 + 3 ^ 40 * 8274517 * 2
def baseEnd_8274517 : Nat := 4248804404799107647883695

theorem tailTrace_8274517 : CollatzResearch.WordTrace tailWord_8274517 prefixEnd_8274517 4248804404799107647883695 := by
  unfold tailWord_8274517
  simp only [CollatzResearch.WordTrace]
  refine ⟨301796428563845558840101805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201197619042563705893401203 301796428563845558840101805)
  ·
    refine ⟨113173660711442084565038177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301796428563845558840101805 113173660711442084565038177)
    ·
      refine ⟨84880245533581563423778633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113173660711442084565038177 84880245533581563423778633)
      ·
        refine ⟨63660184150186172567833975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84880245533581563423778633 63660184150186172567833975)
        ·
          refine ⟨95490276225279258851750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63660184150186172567833975 95490276225279258851750963)
          ·
            refine ⟨143235414337918888277626445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95490276225279258851750963 143235414337918888277626445)
            ·
              refine ⟨53713280376719583104109917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143235414337918888277626445 53713280376719583104109917)
              ·
                refine ⟨20142480141269843664041219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53713280376719583104109917 20142480141269843664041219)
                ·
                  refine ⟨30213720211904765496061829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20142480141269843664041219 30213720211904765496061829)
                  ·
                    refine ⟨5665072539732143530511593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30213720211904765496061829 5665072539732143530511593)
                    ·
                      refine ⟨4248804404799107647883695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5665072539732143530511593 4248804404799107647883695)
                      ·
                        rfl

theorem cell23_8274517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_8274517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274517 prefixEnd_8274517 := by exact prefixLift 8274517
  have htrace : WordTrace (prefixWord ++ tailWord_8274517) baseStart_8274517 baseEnd_8274517 := by
    simpa [prefixWord, tailWord_8274517, baseEnd_8274517] using wordTrace_append hprefix tailTrace_8274517
  have hstable : (prefixWord ++ tailWord_8274517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274517).length < 2 ^ (prefixWord ++ tailWord_8274517).sum := by decide
  have hdescent : baseEnd_8274517 < baseStart_8274517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274557 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 7]
def baseStart_8274557 : Nat := 118140960795 + 8274557 * 2 ^ 59
def prefixEnd_8274557 : Nat := 4983230072969 + 3 ^ 40 * 8274557 * 2
def baseEnd_8274557 : Nat := 472091660447254165709279

theorem tailTrace_8274557 : CollatzResearch.WordTrace tailWord_8274557 prefixEnd_8274557 472091660447254165709279 := by
  unfold tailWord_8274557
  simp only [CollatzResearch.WordTrace]
  refine ⟨301797887483700645671557925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201198591655800430447705283 301797887483700645671557925)
  ·
    refine ⟨56587103903193871063417111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 301797887483700645671557925 56587103903193871063417111)
    ·
      refine ⟨84880655854790806595125667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56587103903193871063417111 84880655854790806595125667)
      ·
        refine ⟨127320983782186209892688501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84880655854790806595125667 127320983782186209892688501)
        ·
          refine ⟨11936342229579957177439547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127320983782186209892688501 11936342229579957177439547)
          ·
            refine ⟨17904513344369935766159321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936342229579957177439547 17904513344369935766159321)
            ·
              refine ⟨13428385008277451824619491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17904513344369935766159321 13428385008277451824619491)
              ·
                refine ⟨20142577512416177736929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428385008277451824619491 20142577512416177736929237)
                ·
                  refine ⟨472091660447254165709279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20142577512416177736929237 472091660447254165709279)
                  ·
                    rfl

theorem cell23_8274557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_8274557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274557 prefixEnd_8274557 := by exact prefixLift 8274557
  have htrace : WordTrace (prefixWord ++ tailWord_8274557) baseStart_8274557 baseEnd_8274557 := by
    simpa [prefixWord, tailWord_8274557, baseEnd_8274557] using wordTrace_append hprefix tailTrace_8274557
  have hstable : (prefixWord ++ tailWord_8274557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274557).length < 2 ^ (prefixWord ++ tailWord_8274557).sum := by decide
  have hdescent : baseEnd_8274557 < baseStart_8274557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274562 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8274562 : Nat := 118140960795 + 8274562 * 2 ^ 59
def prefixEnd_8274562 : Nat := 4983230072969 + 3 ^ 40 * 8274562 * 2
def baseEnd_8274562 : Nat := 4248827511428559971820989

theorem tailTrace_8274562 : CollatzResearch.WordTrace tailWord_8274562 prefixEnd_8274562 4248827511428559971820989 := by
  unfold tailWord_8274562
  simp only [CollatzResearch.WordTrace]
  refine ⟨75449517462170632881372485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201198713232455021016993293 75449517462170632881372485)
  ·
    refine ⟨14146784524156993665257341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75449517462170632881372485 14146784524156993665257341)
    ·
      refine ⟨5305044196558872624471503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14146784524156993665257341 5305044196558872624471503)
      ·
        refine ⟨7957566294838308936707255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305044196558872624471503 7957566294838308936707255)
        ·
          refine ⟨11936349442257463405060883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957566294838308936707255 11936349442257463405060883)
          ·
            refine ⟨17904524163386195107591325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936349442257463405060883 17904524163386195107591325)
            ·
              refine ⟨6714196561269823165346747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17904524163386195107591325 6714196561269823165346747)
              ·
                refine ⟨10071294841904734748020121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714196561269823165346747 10071294841904734748020121)
                ·
                  refine ⟨7553471131428551061015091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10071294841904734748020121 7553471131428551061015091)
                  ·
                    refine ⟨11330206697142826591522637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7553471131428551061015091 11330206697142826591522637)
                    ·
                      refine ⟨4248827511428559971820989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11330206697142826591522637 4248827511428559971820989)
                      ·
                        rfl

theorem cell23_8274562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8274562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274562 prefixEnd_8274562 := by exact prefixLift 8274562
  have htrace : WordTrace (prefixWord ++ tailWord_8274562) baseStart_8274562 baseEnd_8274562 := by
    simpa [prefixWord, tailWord_8274562, baseEnd_8274562] using wordTrace_append hprefix tailTrace_8274562
  have hstable : (prefixWord ++ tailWord_8274562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274562).length < 2 ^ (prefixWord ++ tailWord_8274562).sum := by decide
  have hdescent : baseEnd_8274562 < baseStart_8274562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274607 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_8274607 : Nat := 118140960795 + 8274607 * 2 ^ 59
def prefixEnd_8274607 : Nat := 4983230072969 + 3 ^ 40 * 8274607 * 2
def baseEnd_8274607 : Nat := 4248850618058012295758281

theorem tailTrace_8274607 : CollatzResearch.WordTrace tailWord_8274607 prefixEnd_8274607 4248850618058012295758281 := by
  unfold tailWord_8274607
  simp only [CollatzResearch.WordTrace]
  refine ⟨301799711133519504210878075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201199807422346336140585383 301799711133519504210878075)
  ·
    refine ⟨452699566700279256316317113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301799711133519504210878075 452699566700279256316317113)
    ·
      refine ⟨339524675025209442237237835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452699566700279256316317113 339524675025209442237237835)
      ·
        refine ⟨509287012537814163355856753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339524675025209442237237835 509287012537814163355856753)
        ·
          refine ⟨381965259403360622516892565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509287012537814163355856753 381965259403360622516892565)
          ·
            refine ⟨17904621534532529180479339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381965259403360622516892565 17904621534532529180479339)
            ·
              refine ⟨26856932301798793770719009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17904621534532529180479339 26856932301798793770719009)
              ·
                refine ⟨20142699226349095328039257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26856932301798793770719009 20142699226349095328039257)
                ·
                  refine ⟨15107024419761821496029443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20142699226349095328039257 15107024419761821496029443)
                  ·
                    refine ⟨22660536629642732244044165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15107024419761821496029443 22660536629642732244044165)
                    ·
                      refine ⟨4248850618058012295758281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22660536629642732244044165 4248850618058012295758281)
                      ·
                        rfl

theorem cell23_8274607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_8274607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274607 prefixEnd_8274607 := by exact prefixLift 8274607
  have htrace : WordTrace (prefixWord ++ tailWord_8274607) baseStart_8274607 baseEnd_8274607 := by
    simpa [prefixWord, tailWord_8274607, baseEnd_8274607] using wordTrace_append hprefix tailTrace_8274607
  have hstable : (prefixWord ++ tailWord_8274607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274607).length < 2 ^ (prefixWord ++ tailWord_8274607).sum := by decide
  have hdescent : baseEnd_8274607 < baseStart_8274607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8274664 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 6]
def baseStart_8274664 : Nat := 118140960795 + 8274664 * 2 ^ 59
def prefixEnd_8274664 : Nat := 4983230072969 + 3 ^ 40 * 8274664 * 2
def baseEnd_8274664 : Nat := 472097765161702063638391

theorem tailTrace_8274664 : CollatzResearch.WordTrace tailWord_8274664 prefixEnd_8274664 472097765161702063638391 := by
  unfold tailWord_8274664
  simp only [CollatzResearch.WordTrace]
  refine ⟨150900895047156501472851523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201201193396208668630468697 150900895047156501472851523)
  ·
    refine ⟨226351342570734752209277285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150900895047156501472851523 226351342570734752209277285)
    ·
      refine ⟨42440876732012766039239491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226351342570734752209277285 42440876732012766039239491)
      ·
        refine ⟨63661315098019149058859237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42440876732012766039239491 63661315098019149058859237)
        ·
          refine ⟨11936496580878590448536107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63661315098019149058859237 11936496580878590448536107)
          ·
            refine ⟨17904744871317885672804161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936496580878590448536107 17904744871317885672804161)
            ·
              refine ⟨13428558653488414254603121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17904744871317885672804161 13428558653488414254603121)
              ·
                refine ⟨10071418990116310690952341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13428558653488414254603121 10071418990116310690952341)
                ·
                  refine ⟨472097765161702063638391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10071418990116310690952341 472097765161702063638391)
                  ·
                    rfl

theorem cell23_8274664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_8274664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8274664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8274664 prefixEnd_8274664 := by exact prefixLift 8274664
  have htrace : WordTrace (prefixWord ++ tailWord_8274664) baseStart_8274664 baseEnd_8274664 := by
    simpa [prefixWord, tailWord_8274664, baseEnd_8274664] using wordTrace_append hprefix tailTrace_8274664
  have hstable : (prefixWord ++ tailWord_8274664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8274664).length < 2 ^ (prefixWord ++ tailWord_8274664).sum := by decide
  have hdescent : baseEnd_8274664 < baseStart_8274664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8274664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
