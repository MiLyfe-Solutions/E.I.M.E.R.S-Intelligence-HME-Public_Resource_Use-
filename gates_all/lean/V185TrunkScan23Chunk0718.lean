import V185TrunkScan23Chunk0717

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4245294 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4245294 : Nat := 118140960795 + 4245294 * 2 ^ 59
def prefixEnd_4245294 : Nat := 4983230072969 + 3 ^ 40 * 4245294 * 2
def baseEnd_4245294 : Nat := 726625447216139500467085

theorem tailTrace_4245294 : CollatzResearch.WordTrace tailWord_4245294 prefixEnd_4245294 726625447216139500467085 := by
  unfold tailWord_4245294
  simp only [CollatzResearch.WordTrace]
  refine ⟨19354824085254043917130867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103225728454688234224697957 19354824085254043917130867)
  ·
    refine ⟨29032236127881065875696301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19354824085254043917130867 29032236127881065875696301)
    ·
      refine ⟨10887088547955399703386113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29032236127881065875696301 10887088547955399703386113)
      ·
        refine ⟨8165316410966549777539585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10887088547955399703386113 8165316410966549777539585)
        ·
          refine ⟨6123987308224912333154689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8165316410966549777539585 6123987308224912333154689)
          ·
            refine ⟨4592990481168684249866017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6123987308224912333154689 4592990481168684249866017)
            ·
              refine ⟨3444742860876513187399513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592990481168684249866017 3444742860876513187399513)
              ·
                refine ⟨2583557145657384890549635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444742860876513187399513 2583557145657384890549635)
                ·
                  refine ⟨3875335718486077335824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583557145657384890549635 3875335718486077335824453)
                  ·
                    refine ⟨726625447216139500467085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875335718486077335824453 726625447216139500467085)
                    ·
                      rfl

theorem cell23_4245294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4245294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245294 prefixEnd_4245294 := by exact prefixLift 4245294
  have htrace : WordTrace (prefixWord ++ tailWord_4245294) baseStart_4245294 baseEnd_4245294 := by
    simpa [prefixWord, tailWord_4245294, baseEnd_4245294] using wordTrace_append hprefix tailTrace_4245294
  have hstable : (prefixWord ++ tailWord_4245294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245294).length < 2 ^ (prefixWord ++ tailWord_4245294).sum := by decide
  have hdescent : baseEnd_4245294 < baseStart_4245294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245306 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_4245306 : Nat := 118140960795 + 4245306 * 2 ^ 59
def prefixEnd_4245306 : Nat := 4983230072969 + 3 ^ 40 * 4245306 * 2
def baseEnd_4245306 : Nat := 2179882503416272454451199

theorem tailTrace_4245306 : CollatzResearch.WordTrace tailWord_4245306 prefixEnd_4245306 2179882503416272454451199 := by
  unfold tailWord_4245306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38709757589497219346620943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103226020238659251590989181 38709757589497219346620943)
  ·
    refine ⟨58064636384245829019931415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38709757589497219346620943 58064636384245829019931415)
    ·
      refine ⟨87096954576368743529897123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58064636384245829019931415 87096954576368743529897123)
      ·
        refine ⟨130645431864553115294845685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87096954576368743529897123 130645431864553115294845685)
        ·
          refine ⟨12248009237301854558891783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130645431864553115294845685 12248009237301854558891783)
          ·
            refine ⟨18372013855952781838337675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12248009237301854558891783 18372013855952781838337675)
            ·
              refine ⟨27558020783929172757506513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18372013855952781838337675 27558020783929172757506513)
              ·
                refine ⟨20668515587946879568129885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27558020783929172757506513 20668515587946879568129885)
                ·
                  refine ⟨7750693345480079838048707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20668515587946879568129885 7750693345480079838048707)
                  ·
                    refine ⟨11626040018220119757073061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7750693345480079838048707 11626040018220119757073061)
                    ·
                      refine ⟨2179882503416272454451199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11626040018220119757073061 2179882503416272454451199)
                      ·
                        rfl

theorem cell23_4245306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_4245306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245306 prefixEnd_4245306 := by exact prefixLift 4245306
  have htrace : WordTrace (prefixWord ++ tailWord_4245306) baseStart_4245306 baseEnd_4245306 := by
    simpa [prefixWord, tailWord_4245306, baseEnd_4245306] using wordTrace_append hprefix tailTrace_4245306
  have hstable : (prefixWord ++ tailWord_4245306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245306).length < 2 ^ (prefixWord ++ tailWord_4245306).sum := by decide
  have hdescent : baseEnd_4245306 < baseStart_4245306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245319 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_4245319 : Nat := 118140960795 + 4245319 * 2 ^ 59
def prefixEnd_4245319 : Nat := 4983230072969 + 3 ^ 40 * 4245319 * 2
def baseEnd_4245319 : Nat := 2179889178664780903588639

theorem tailTrace_4245319 : CollatzResearch.WordTrace tailWord_4245319 prefixEnd_4245319 2179889178664780903588639 := by
  unfold tailWord_4245319
  simp only [CollatzResearch.WordTrace]
  refine ⟨154839504506941780606707011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103226336337961187071138007 154839504506941780606707011)
  ·
    refine ⟨232259256760412670910060517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154839504506941780606707011 232259256760412670910060517)
    ·
      refine ⟨43548610642577375795636347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232259256760412670910060517 43548610642577375795636347)
      ·
        refine ⟨65322915963866063693454521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43548610642577375795636347 65322915963866063693454521)
        ·
          refine ⟨48992186972899547770090891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65322915963866063693454521 48992186972899547770090891)
          ·
            refine ⟨73488280459349321655136337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48992186972899547770090891 73488280459349321655136337)
            ·
              refine ⟨55116210344511991241352253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73488280459349321655136337 55116210344511991241352253)
              ·
                refine ⟨20668578879191996715507095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55116210344511991241352253 20668578879191996715507095)
                ·
                  refine ⟨31002868318787995073260643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20668578879191996715507095 31002868318787995073260643)
                  ·
                    refine ⟨46504302478181992609890965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31002868318787995073260643 46504302478181992609890965)
                    ·
                      refine ⟨2179889178664780903588639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46504302478181992609890965 2179889178664780903588639)
                      ·
                        rfl

theorem cell23_4245319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_4245319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245319 prefixEnd_4245319 := by exact prefixLift 4245319
  have htrace : WordTrace (prefixWord ++ tailWord_4245319) baseStart_4245319 baseEnd_4245319 := by
    simpa [prefixWord, tailWord_4245319, baseEnd_4245319] using wordTrace_append hprefix tailTrace_4245319
  have hstable : (prefixWord ++ tailWord_4245319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245319).length < 2 ^ (prefixWord ++ tailWord_4245319).sum := by decide
  have hdescent : baseEnd_4245319 < baseStart_4245319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245340 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4245340 : Nat := 118140960795 + 4245340 * 2 ^ 59
def prefixEnd_4245340 : Nat := 4983230072969 + 3 ^ 40 * 4245340 * 2
def baseEnd_4245340 : Nat := 2179899961758525321426043

theorem tailTrace_4245340 : CollatzResearch.WordTrace tailWord_4245340 prefixEnd_4245340 2179899961758525321426043 := by
  unfold tailWord_4245340
  simp only [CollatzResearch.WordTrace]
  refine ⟨77420135219932850596610737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103226846959910467462147649 77420135219932850596610737)
  ·
    refine ⟨58065101414949637947458053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77420135219932850596610737 58065101414949637947458053)
    ·
      refine ⟨10887206515303057115148385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58065101414949637947458053 10887206515303057115148385)
      ·
        refine ⟨8165404886477292836361289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10887206515303057115148385 8165404886477292836361289)
        ·
          refine ⟨6124053664857969627270967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8165404886477292836361289 6124053664857969627270967)
          ·
            refine ⟨9186080497286954440906451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124053664857969627270967 9186080497286954440906451)
            ·
              refine ⟨13779120745930431661359677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186080497286954440906451 13779120745930431661359677)
              ·
                refine ⟨5167170279723911873009879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13779120745930431661359677 5167170279723911873009879)
                ·
                  refine ⟨7750755419585867809514819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167170279723911873009879 7750755419585867809514819)
                  ·
                    refine ⟨11626133129378801714272229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7750755419585867809514819 11626133129378801714272229)
                    ·
                      refine ⟨2179899961758525321426043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11626133129378801714272229 2179899961758525321426043)
                      ·
                        rfl

theorem cell23_4245340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4245340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245340 prefixEnd_4245340 := by exact prefixLift 4245340
  have htrace : WordTrace (prefixWord ++ tailWord_4245340) baseStart_4245340 baseEnd_4245340 := by
    simpa [prefixWord, tailWord_4245340, baseEnd_4245340] using wordTrace_append hprefix tailTrace_4245340
  have hstable : (prefixWord ++ tailWord_4245340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245340).length < 2 ^ (prefixWord ++ tailWord_4245340).sum := by decide
  have hdescent : baseEnd_4245340 < baseStart_4245340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245343 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_4245343 : Nat := 118140960795 + 4245343 * 2 ^ 59
def prefixEnd_4245343 : Nat := 4983230072969 + 3 ^ 40 * 4245343 * 2
def baseEnd_4245343 : Nat := 2179901502200488809688529

theorem tailTrace_4245343 : CollatzResearch.WordTrace tailWord_4245343 prefixEnd_4245343 2179901502200488809688529 := by
  unfold tailWord_4245343
  simp only [CollatzResearch.WordTrace]
  refine ⟨154840379858854832705580683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103226919905903221803720455 154840379858854832705580683)
  ·
    refine ⟨232260569788282249058371025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154840379858854832705580683 232260569788282249058371025)
    ·
      refine ⟨174195427341211686793778269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232260569788282249058371025 174195427341211686793778269)
      ·
        refine ⟨65323285252954382547666851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174195427341211686793778269 65323285252954382547666851)
        ·
          refine ⟨97984927879431573821500277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65323285252954382547666851 97984927879431573821500277)
          ·
            refine ⟨9186086988696710045765651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97984927879431573821500277 9186086988696710045765651)
            ·
              refine ⟨13779130483045065068648477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186086988696710045765651 13779130483045065068648477)
              ·
                refine ⟨5167173931141899400743179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13779130483045065068648477 5167173931141899400743179)
                ·
                  refine ⟨7750760896712849101114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167173931141899400743179 7750760896712849101114769)
                  ·
                    refine ⟨5813070672534636825836077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7750760896712849101114769 5813070672534636825836077)
                    ·
                      refine ⟨2179901502200488809688529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813070672534636825836077 2179901502200488809688529)
                      ·
                        rfl

theorem cell23_4245343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_4245343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245343 prefixEnd_4245343 := by exact prefixLift 4245343
  have htrace : WordTrace (prefixWord ++ tailWord_4245343) baseStart_4245343 baseEnd_4245343 := by
    simpa [prefixWord, tailWord_4245343, baseEnd_4245343] using wordTrace_append hprefix tailTrace_4245343
  have hstable : (prefixWord ++ tailWord_4245343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245343).length < 2 ^ (prefixWord ++ tailWord_4245343).sum := by decide
  have hdescent : baseEnd_4245343 < baseStart_4245343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245346 : List Nat := [3, 3, 2, 1, 2, 2, 10]
def baseStart_4245346 : Nat := 118140960795 + 4245346 * 2 ^ 59
def prefixEnd_4245346 : Nat := 4983230072969 + 3 ^ 40 * 4245346 * 2
def baseEnd_4245346 : Nat := 26912383242499411085815

theorem tailTrace_4245346 : CollatzResearch.WordTrace tailWord_4245346 prefixEnd_4245346 26912383242499411085815 := by
  unfold tailWord_4245346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38710122319460991054484973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103226992851895976145293261 38710122319460991054484973)
  ·
    refine ⟨14516295869797871645431865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38710122319460991054484973 14516295869797871645431865)
    ·
      refine ⟨10887221902348403734073899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14516295869797871645431865 10887221902348403734073899)
      ·
        refine ⟨16330832853522605601110849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10887221902348403734073899 16330832853522605601110849)
        ·
          refine ⟨12248124640141954200833137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16330832853522605601110849 12248124640141954200833137)
          ·
            refine ⟨9186093480106465650624853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12248124640141954200833137 9186093480106465650624853)
            ·
              refine ⟨26912383242499411085815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9186093480106465650624853 26912383242499411085815)
              ·
                rfl

theorem cell23_4245346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 10].length) (baseStart_4245346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245346 prefixEnd_4245346 := by exact prefixLift 4245346
  have htrace : WordTrace (prefixWord ++ tailWord_4245346) baseStart_4245346 baseEnd_4245346 := by
    simpa [prefixWord, tailWord_4245346, baseEnd_4245346] using wordTrace_append hprefix tailTrace_4245346
  have hstable : (prefixWord ++ tailWord_4245346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245346).length < 2 ^ (prefixWord ++ tailWord_4245346).sum := by decide
  have hdescent : baseEnd_4245346 < baseStart_4245346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245349 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4245349 : Nat := 118140960795 + 4245349 * 2 ^ 59
def prefixEnd_4245349 : Nat := 4983230072969 + 3 ^ 40 * 4245349 * 2
def baseEnd_4245349 : Nat := 2179904583084415786213501

theorem tailTrace_4245349 : CollatzResearch.WordTrace tailWord_4245349 prefixEnd_4245349 2179904583084415786213501 := by
  unfold tailWord_4245349
  simp only [CollatzResearch.WordTrace]
  refine ⟨154840598696833095730299101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103227065797888730486866067 154840598696833095730299101)
  ·
    refine ⟨58065224511312410898862163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154840598696833095730299101 58065224511312410898862163)
    ·
      refine ⟨87097836766968616348293245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58065224511312410898862163 87097836766968616348293245)
      ·
        refine ⟨32661688787613231130609967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87097836766968616348293245 32661688787613231130609967)
        ·
          refine ⟨48992533181419846695914951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32661688787613231130609967 48992533181419846695914951)
          ·
            refine ⟨73488799772129770043872427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48992533181419846695914951 73488799772129770043872427)
            ·
              refine ⟨110233199658194655065808641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73488799772129770043872427 110233199658194655065808641)
              ·
                refine ⟨82674899743645991299356481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110233199658194655065808641 82674899743645991299356481)
                ·
                  refine ⟨62006174807734493474517361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82674899743645991299356481 62006174807734493474517361)
                  ·
                    refine ⟨46504631105800870105888021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62006174807734493474517361 46504631105800870105888021)
                    ·
                      refine ⟨2179904583084415786213501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46504631105800870105888021 2179904583084415786213501)
                      ·
                        rfl

theorem cell23_4245349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4245349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245349 prefixEnd_4245349 := by exact prefixLift 4245349
  have htrace : WordTrace (prefixWord ++ tailWord_4245349) baseStart_4245349 baseEnd_4245349 := by
    simpa [prefixWord, tailWord_4245349, baseEnd_4245349] using wordTrace_append hprefix tailTrace_4245349
  have hstable : (prefixWord ++ tailWord_4245349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245349).length < 2 ^ (prefixWord ++ tailWord_4245349).sum := by decide
  have hdescent : baseEnd_4245349 < baseStart_4245349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245357 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4245357 : Nat := 118140960795 + 4245357 * 2 ^ 59
def prefixEnd_4245357 : Nat := 4983230072969 + 3 ^ 40 * 4245357 * 2
def baseEnd_4245357 : Nat := 2179908690929651754913465

theorem tailTrace_4245357 : CollatzResearch.WordTrace tailWord_4245357 prefixEnd_4245357 2179908690929651754913465 := by
  unfold tailWord_4245357
  simp only [CollatzResearch.WordTrace]
  refine ⟨154840890480804113096590325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103227260320536075397726883 154840890480804113096590325)
  ·
    refine ⟨14516333482575385602805343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154840890480804113096590325 14516333482575385602805343)
    ·
      refine ⟨21774500223863078404208015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14516333482575385602805343 21774500223863078404208015)
      ·
        refine ⟨32661750335794617606312023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21774500223863078404208015 32661750335794617606312023)
        ·
          refine ⟨48992625503691926409468035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32661750335794617606312023 48992625503691926409468035)
          ·
            refine ⟨73488938255537889614202053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48992625503691926409468035 73488938255537889614202053)
            ·
              refine ⟨13779175922913354302662885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73488938255537889614202053 13779175922913354302662885)
              ·
                refine ⟨2583595485546253931749291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13779175922913354302662885 2583595485546253931749291)
                ·
                  refine ⟨3875393228319380897623937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583595485546253931749291 3875393228319380897623937)
                  ·
                    refine ⟨2906544921239535673217953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3875393228319380897623937 2906544921239535673217953)
                    ·
                      refine ⟨2179908690929651754913465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906544921239535673217953 2179908690929651754913465)
                      ·
                        rfl

theorem cell23_4245357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4245357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245357 prefixEnd_4245357 := by exact prefixLift 4245357
  have htrace : WordTrace (prefixWord ++ tailWord_4245357) baseStart_4245357 baseEnd_4245357 := by
    simpa [prefixWord, tailWord_4245357, baseEnd_4245357] using wordTrace_append hprefix tailTrace_4245357
  have hstable : (prefixWord ++ tailWord_4245357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245357).length < 2 ^ (prefixWord ++ tailWord_4245357).sum := by decide
  have hdescent : baseEnd_4245357 < baseStart_4245357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245377 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4245377 : Nat := 118140960795 + 4245377 * 2 ^ 59
def prefixEnd_4245377 : Nat := 4983230072969 + 3 ^ 40 * 4245377 * 2
def baseEnd_4245377 : Nat := 2179918960542741676663373

theorem tailTrace_4245377 : CollatzResearch.WordTrace tailWord_4245377 prefixEnd_4245377 2179918960542741676663373 := by
  unfold tailWord_4245377
  simp only [CollatzResearch.WordTrace]
  refine ⟨154841619940731656512318385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103227746627154437674878923 154841619940731656512318385)
  ·
    refine ⟨116131214955548742384238789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154841619940731656512318385 116131214955548742384238789)
    ·
      refine ⟨21774602804165389197044773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116131214955548742384238789 21774602804165389197044773)
      ·
        refine ⟨4082738025781010474445895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21774602804165389197044773 4082738025781010474445895)
        ·
          refine ⟨6124107038671515711668843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082738025781010474445895 6124107038671515711668843)
          ·
            refine ⟨9186160558007273567503265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124107038671515711668843 9186160558007273567503265)
            ·
              refine ⟨6889620418505455175627449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186160558007273567503265 6889620418505455175627449)
              ·
                refine ⟨5167215313879091381720587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6889620418505455175627449 5167215313879091381720587)
                ·
                  refine ⟨7750822970818637072580881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167215313879091381720587 7750822970818637072580881)
                  ·
                    refine ⟨5813117228113977804435661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7750822970818637072580881 5813117228113977804435661)
                    ·
                      refine ⟨2179918960542741676663373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813117228113977804435661 2179918960542741676663373)
                      ·
                        rfl

theorem cell23_4245377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4245377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245377 prefixEnd_4245377 := by exact prefixLift 4245377
  have htrace : WordTrace (prefixWord ++ tailWord_4245377) baseStart_4245377 baseEnd_4245377 := by
    simpa [prefixWord, tailWord_4245377, baseEnd_4245377] using wordTrace_append hprefix tailTrace_4245377
  have hstable : (prefixWord ++ tailWord_4245377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245377).length < 2 ^ (prefixWord ++ tailWord_4245377).sum := by decide
  have hdescent : baseEnd_4245377 < baseStart_4245377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245426 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4245426 : Nat := 118140960795 + 4245426 * 2 ^ 59
def prefixEnd_4245426 : Nat := 4983230072969 + 3 ^ 40 * 4245426 * 2
def baseEnd_4245426 : Nat := 2179944121094811984950647

theorem tailTrace_4245426 : CollatzResearch.WordTrace tailWord_4245426 prefixEnd_4245426 2179944121094811984950647 := by
  unfold tailWord_4245426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38710851779388534470213033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103228938078369425253901421 38710851779388534470213033)
  ·
    refine ⟨29033138834541400852659775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38710851779388534470213033 29033138834541400852659775)
    ·
      refine ⟨43549708251812101278989663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29033138834541400852659775 43549708251812101278989663)
      ·
        refine ⟨65324562377718151918484495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43549708251812101278989663 65324562377718151918484495)
        ·
          refine ⟨97986843566577227877726743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65324562377718151918484495 97986843566577227877726743)
          ·
            refine ⟨146980265349865841816590115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97986843566577227877726743 146980265349865841816590115)
            ·
              refine ⟨220470398024798762724885173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146980265349865841816590115 220470398024798762724885173)
              ·
                refine ⟨20669099814824884005457985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220470398024798762724885173 20669099814824884005457985)
                ·
                  refine ⟨15501824861118663004093489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20669099814824884005457985 15501824861118663004093489)
                  ·
                    refine ⟨11626368645838997253070117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15501824861118663004093489 11626368645838997253070117)
                    ·
                      refine ⟨2179944121094811984950647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11626368645838997253070117 2179944121094811984950647)
                      ·
                        rfl

theorem cell23_4245426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4245426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245426 prefixEnd_4245426 := by exact prefixLift 4245426
  have htrace : WordTrace (prefixWord ++ tailWord_4245426) baseStart_4245426 baseEnd_4245426 := by
    simpa [prefixWord, tailWord_4245426, baseEnd_4245426] using wordTrace_append hprefix tailTrace_4245426
  have hstable : (prefixWord ++ tailWord_4245426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245426).length < 2 ^ (prefixWord ++ tailWord_4245426).sum := by decide
  have hdescent : baseEnd_4245426 < baseStart_4245426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245473 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_4245473 : Nat := 118140960795 + 4245473 * 2 ^ 59
def prefixEnd_4245473 : Nat := 4983230072969 + 3 ^ 40 * 4245473 * 2
def baseEnd_4245473 : Nat := 2179968254685573301062931

theorem tailTrace_4245473 : CollatzResearch.WordTrace tailWord_4245473 prefixEnd_4245473 2179968254685573301062931 := by
  unfold tailWord_4245473
  simp only [CollatzResearch.WordTrace]
  refine ⟨154845121348383864907813073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103230080898922576605208715 154845121348383864907813073)
  ·
    refine ⟨116133841011287898680859805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154845121348383864907813073 116133841011287898680859805)
    ·
      refine ⟨43550190379232962005322427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116133841011287898680859805 43550190379232962005322427)
      ·
        refine ⟨65325285568849443007983641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43550190379232962005322427 65325285568849443007983641)
        ·
          refine ⟨48993964176637082255987731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65325285568849443007983641 48993964176637082255987731)
          ·
            refine ⟨73490946264955623383981597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48993964176637082255987731 73490946264955623383981597)
            ·
              refine ⟨27559104849358358768993099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73490946264955623383981597 27559104849358358768993099)
              ·
                refine ⟨41338657274037538153489649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27559104849358358768993099 41338657274037538153489649)
                ·
                  refine ⟨31003992955528153615117237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41338657274037538153489649 31003992955528153615117237)
                  ·
                    refine ⟨2906624339580764401417241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31003992955528153615117237 2906624339580764401417241)
                    ·
                      refine ⟨2179968254685573301062931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906624339580764401417241 2179968254685573301062931)
                      ·
                        rfl

theorem cell23_4245473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_4245473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245473 prefixEnd_4245473 := by exact prefixLift 4245473
  have htrace : WordTrace (prefixWord ++ tailWord_4245473) baseStart_4245473 baseEnd_4245473 := by
    simpa [prefixWord, tailWord_4245473, baseEnd_4245473] using wordTrace_append hprefix tailTrace_4245473
  have hstable : (prefixWord ++ tailWord_4245473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245473).length < 2 ^ (prefixWord ++ tailWord_4245473).sum := by decide
  have hdescent : baseEnd_4245473 < baseStart_4245473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245476 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4245476 : Nat := 118140960795 + 4245476 * 2 ^ 59
def prefixEnd_4245476 : Nat := 4983230072969 + 3 ^ 40 * 4245476 * 2
def baseEnd_4245476 : Nat := 2179969795127536789325417

theorem tailTrace_4245476 : CollatzResearch.WordTrace tailWord_4245476 prefixEnd_4245476 2179969795127536789325417 := by
  unfold tailWord_4245476
  simp only [CollatzResearch.WordTrace]
  refine ⟨77422615383686498210086141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103230153844915330946781521 77422615383686498210086141)
  ·
    refine ⟨29033480768882436828782303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77422615383686498210086141 29033480768882436828782303)
    ·
      refine ⟨43550221153323655243173455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29033480768882436828782303 43550221153323655243173455)
      ·
        refine ⟨65325331729985482864760183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43550221153323655243173455 65325331729985482864760183)
        ·
          refine ⟨97987997594978224297140275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65325331729985482864760183 97987997594978224297140275)
          ·
            refine ⟨146981996392467336445710413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97987997594978224297140275 146981996392467336445710413)
            ·
              refine ⟨55118248647175251167141405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146981996392467336445710413 55118248647175251167141405)
              ·
                refine ⟨20669343242690719187678027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55118248647175251167141405 20669343242690719187678027)
                ·
                  refine ⟨31004014864036078781517041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20669343242690719187678027 31004014864036078781517041)
                  ·
                    refine ⟨23253011148027059086137781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31004014864036078781517041 23253011148027059086137781)
                    ·
                      refine ⟨2179969795127536789325417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23253011148027059086137781 2179969795127536789325417)
                      ·
                        rfl

theorem cell23_4245476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4245476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245476 prefixEnd_4245476 := by exact prefixLift 4245476
  have htrace : WordTrace (prefixWord ++ tailWord_4245476) baseStart_4245476 baseEnd_4245476 := by
    simpa [prefixWord, tailWord_4245476, baseEnd_4245476] using wordTrace_append hprefix tailTrace_4245476
  have hstable : (prefixWord ++ tailWord_4245476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245476).length < 2 ^ (prefixWord ++ tailWord_4245476).sum := by decide
  have hdescent : baseEnd_4245476 < baseStart_4245476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245516 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4245516 : Nat := 118140960795 + 4245516 * 2 ^ 59
def prefixEnd_4245516 : Nat := 4983230072969 + 3 ^ 40 * 4245516 * 2
def baseEnd_4245516 : Nat := 2179990334353716632825233

theorem tailTrace_4245516 : CollatzResearch.WordTrace tailWord_4245516 prefixEnd_4245516 2179990334353716632825233 := by
  unfold tailWord_4245516
  simp only [CollatzResearch.WordTrace]
  refine ⟨77423344843614041625814201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103231126458152055501085601 77423344843614041625814201)
  ·
    refine ⟨58067508632710531219360651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77423344843614041625814201 58067508632710531219360651)
    ·
      refine ⟨87101262949065796829040977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58067508632710531219360651 87101262949065796829040977)
      ·
        refine ⟨65325947211799347621780733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87101262949065796829040977 65325947211799347621780733)
        ·
          refine ⟨24497230204424755358167775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65325947211799347621780733 24497230204424755358167775)
          ·
            refine ⟨36745845306637133037251663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24497230204424755358167775 36745845306637133037251663)
            ·
              refine ⟨55118767959955699555877495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36745845306637133037251663 55118767959955699555877495)
              ·
                refine ⟨82678151939933549333816243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55118767959955699555877495 82678151939933549333816243)
                ·
                  refine ⟨124017227909900324000724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82678151939933549333816243 124017227909900324000724365)
                  ·
                    refine ⟨46506460466212621500271637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124017227909900324000724365 46506460466212621500271637)
                    ·
                      refine ⟨2179990334353716632825233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46506460466212621500271637 2179990334353716632825233)
                      ·
                        rfl

theorem cell23_4245516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4245516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245516 prefixEnd_4245516 := by exact prefixLift 4245516
  have htrace : WordTrace (prefixWord ++ tailWord_4245516) baseStart_4245516 baseEnd_4245516 := by
    simpa [prefixWord, tailWord_4245516, baseEnd_4245516] using wordTrace_append hprefix tailTrace_4245516
  have hstable : (prefixWord ++ tailWord_4245516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245516).length < 2 ^ (prefixWord ++ tailWord_4245516).sum := by decide
  have hdescent : baseEnd_4245516 < baseStart_4245516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245523 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3]
def baseStart_4245523 : Nat := 118140960795 + 4245523 * 2 ^ 59
def prefixEnd_4245523 : Nat := 4983230072969 + 3 ^ 40 * 4245523 * 2
def baseEnd_4245523 : Nat := 2179993928718298105437701

theorem tailTrace_4245523 : CollatzResearch.WordTrace tailWord_4245523 prefixEnd_4245523 2179993928718298105437701 := by
  unfold tailWord_4245523
  simp only [CollatzResearch.WordTrace]
  refine ⟨154846944998202723447133223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103231296665468482298088815 154846944998202723447133223)
  ·
    refine ⟨232270417497304085170699835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154846944998202723447133223 232270417497304085170699835)
    ·
      refine ⟨348405626245956127756049753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232270417497304085170699835 348405626245956127756049753)
      ·
        refine ⟨261304219684467095817037315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348405626245956127756049753 261304219684467095817037315)
        ·
          refine ⟨391956329526700643725555973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261304219684467095817037315 391956329526700643725555973)
          ·
            refine ⟨73491811786256370698541745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 391956329526700643725555973 73491811786256370698541745)
            ·
              refine ⟨55118858839692278023906309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73491811786256370698541745 55118858839692278023906309)
              ·
                refine ⟨10334786032442302129482433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55118858839692278023906309 10334786032442302129482433)
                ·
                  refine ⟨7751089524331726597111825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10334786032442302129482433 7751089524331726597111825)
                  ·
                    refine ⟨5813317143248794947833869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7751089524331726597111825 5813317143248794947833869)
                    ·
                      refine ⟨2179993928718298105437701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813317143248794947833869 2179993928718298105437701)
                      ·
                        rfl

theorem cell23_4245523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_4245523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245523 prefixEnd_4245523 := by exact prefixLift 4245523
  have htrace : WordTrace (prefixWord ++ tailWord_4245523) baseStart_4245523 baseEnd_4245523 := by
    simpa [prefixWord, tailWord_4245523, baseEnd_4245523] using wordTrace_append hprefix tailTrace_4245523
  have hstable : (prefixWord ++ tailWord_4245523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245523).length < 2 ^ (prefixWord ++ tailWord_4245523).sum := by decide
  have hdescent : baseEnd_4245523 < baseStart_4245523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245530 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_4245530 : Nat := 118140960795 + 4245530 * 2 ^ 59
def prefixEnd_4245530 : Nat := 4983230072969 + 3 ^ 40 * 4245530 * 2
def baseEnd_4245530 : Nat := 726665841027626526016723

theorem tailTrace_4245530 : CollatzResearch.WordTrace tailWord_4245530 prefixEnd_4245530 726665841027626526016723 := by
  unfold tailWord_4245530
  simp only [CollatzResearch.WordTrace]
  refine ⟨38711800077294340910659511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103231466872784909095092029 38711800077294340910659511)
  ·
    refine ⟨58067700115941511365989267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38711800077294340910659511 58067700115941511365989267)
    ·
      refine ⟨87101550173912267048983901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58067700115941511365989267 87101550173912267048983901)
      ·
        refine ⟨32663081315217100143368963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87101550173912267048983901 32663081315217100143368963)
        ·
          refine ⟨48994621972825650215053445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32663081315217100143368963 48994621972825650215053445)
          ·
            refine ⟨9186491619904809415322521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48994621972825650215053445 9186491619904809415322521)
            ·
              refine ⟨6889868714928607061491891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186491619904809415322521 6889868714928607061491891)
              ·
                refine ⟨10334803072392910592237837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6889868714928607061491891 10334803072392910592237837)
                ·
                  refine ⟨3875551152147341472089189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10334803072392910592237837 3875551152147341472089189)
                  ·
                    refine ⟨726665841027626526016723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875551152147341472089189 726665841027626526016723)
                    ·
                      rfl

theorem cell23_4245530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_4245530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245530 prefixEnd_4245530 := by exact prefixLift 4245530
  have htrace : WordTrace (prefixWord ++ tailWord_4245530) baseStart_4245530 baseEnd_4245530 := by
    simpa [prefixWord, tailWord_4245530, baseEnd_4245530] using wordTrace_append hprefix tailTrace_4245530
  have hstable : (prefixWord ++ tailWord_4245530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245530).length < 2 ^ (prefixWord ++ tailWord_4245530).sum := by decide
  have hdescent : baseEnd_4245530 < baseStart_4245530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245580 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4245580 : Nat := 118140960795 + 4245580 * 2 ^ 59
def prefixEnd_4245580 : Nat := 4983230072969 + 3 ^ 40 * 4245580 * 2
def baseEnd_4245580 : Nat := 2180023197115604382424939

theorem tailTrace_4245580 : CollatzResearch.WordTrace tailWord_4245580 prefixEnd_4245580 2180023197115604382424939 := by
  unfold tailWord_4245580
  simp only [CollatzResearch.WordTrace]
  refine ⟨77424511979498111090979097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103232682639330814787972129 77424511979498111090979097)
  ·
    refine ⟨58068383984623583318234323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77424511979498111090979097 58068383984623583318234323)
    ·
      refine ⟨87102575976935374977351485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58068383984623583318234323 87102575976935374977351485)
      ·
        refine ⟨32663465991350765616506807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87102575976935374977351485 32663465991350765616506807)
        ·
          refine ⟨48995198987026148424760211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32663465991350765616506807 48995198987026148424760211)
          ·
            refine ⟨73492798480539222637140317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48995198987026148424760211 73492798480539222637140317)
            ·
              refine ⟨27559799430202208488927619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73492798480539222637140317 27559799430202208488927619)
              ·
                refine ⟨41339699145303312733391429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27559799430202208488927619 41339699145303312733391429)
                ·
                  refine ⟨7751193589744371137510893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41339699145303312733391429 7751193589744371137510893)
                  ·
                    refine ⟨2906697596154139176566585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7751193589744371137510893 2906697596154139176566585)
                    ·
                      refine ⟨2180023197115604382424939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906697596154139176566585 2180023197115604382424939)
                      ·
                        rfl

theorem cell23_4245580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4245580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245580 prefixEnd_4245580 := by exact prefixLift 4245580
  have htrace : WordTrace (prefixWord ++ tailWord_4245580) baseStart_4245580 baseEnd_4245580 := by
    simpa [prefixWord, tailWord_4245580, baseEnd_4245580] using wordTrace_append hprefix tailTrace_4245580
  have hstable : (prefixWord ++ tailWord_4245580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245580).length < 2 ^ (prefixWord ++ tailWord_4245580).sum := by decide
  have hdescent : baseEnd_4245580 < baseStart_4245580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245593 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_4245593 : Nat := 118140960795 + 4245593 * 2 ^ 59
def prefixEnd_4245593 : Nat := 4983230072969 + 3 ^ 40 * 4245593 * 2
def baseEnd_4245593 : Nat := 2180029872364112831562379

theorem tailTrace_4245593 : CollatzResearch.WordTrace tailWord_4245593 prefixEnd_4245593 2180029872364112831562379 := by
  unfold tailWord_4245593
  simp only [CollatzResearch.WordTrace]
  refine ⟨154849498107949125402181433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103232998738632750268120955 154849498107949125402181433)
  ·
    refine ⟨116137123580961844051636075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154849498107949125402181433 116137123580961844051636075)
    ·
      refine ⟨174205685371442766077454113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116137123580961844051636075 174205685371442766077454113)
      ·
        refine ⟨130654264028582074558090585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174205685371442766077454113 130654264028582074558090585)
        ·
          refine ⟨97990698021436555918567939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130654264028582074558090585 97990698021436555918567939)
          ·
            refine ⟨146986047032154833877851909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97990698021436555918567939 146986047032154833877851909)
            ·
              refine ⟨27559883818529031352097233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146986047032154833877851909 27559883818529031352097233)
              ·
                refine ⟨20669912863896773514072925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27559883818529031352097233 20669912863896773514072925)
                ·
                  refine ⟨7751217323961290067777347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20669912863896773514072925 7751217323961290067777347)
                  ·
                    refine ⟨11626825985941935101666021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7751217323961290067777347 11626825985941935101666021)
                    ·
                      refine ⟨2180029872364112831562379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11626825985941935101666021 2180029872364112831562379)
                      ·
                        rfl

theorem cell23_4245593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_4245593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245593 prefixEnd_4245593 := by exact prefixLift 4245593
  have htrace : WordTrace (prefixWord ++ tailWord_4245593) baseStart_4245593 baseEnd_4245593 := by
    simpa [prefixWord, tailWord_4245593, baseEnd_4245593] using wordTrace_append hprefix tailTrace_4245593
  have hstable : (prefixWord ++ tailWord_4245593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245593).length < 2 ^ (prefixWord ++ tailWord_4245593).sum := by decide
  have hdescent : baseEnd_4245593 < baseStart_4245593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245623 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_4245623 : Nat := 118140960795 + 4245623 * 2 ^ 59
def prefixEnd_4245623 : Nat := 4983230072969 + 3 ^ 40 * 4245623 * 2
def baseEnd_4245623 : Nat := 2180045276783747714187241

theorem tailTrace_4245623 : CollatzResearch.WordTrace tailWord_4245623 prefixEnd_4245623 2180045276783747714187241 := by
  unfold tailWord_4245623
  simp only [CollatzResearch.WordTrace]
  refine ⟨154850592297840440525773523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103233728198560293683849015 154850592297840440525773523)
  ·
    refine ⟨232275888446760660788660285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154850592297840440525773523 232275888446760660788660285)
    ·
      refine ⟨87103458167535247795747607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232275888446760660788660285 87103458167535247795747607)
      ·
        refine ⟨130655187251302871693621411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87103458167535247795747607 130655187251302871693621411)
        ·
          refine ⟨195982780876954307540432117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130655187251302871693621411 195982780876954307540432117)
          ·
            refine ⟨18373385707214466331915511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195982780876954307540432117 18373385707214466331915511)
            ·
              refine ⟨27560078560821699497873267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18373385707214466331915511 27560078560821699497873267)
              ·
                refine ⟨41340117841232549246809901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27560078560821699497873267 41340117841232549246809901)
                ·
                  refine ⟨15502544190462205967553713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41340117841232549246809901 15502544190462205967553713)
                  ·
                    refine ⟨11626908142846654475665285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15502544190462205967553713 11626908142846654475665285)
                    ·
                      refine ⟨2180045276783747714187241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11626908142846654475665285 2180045276783747714187241)
                      ·
                        rfl

theorem cell23_4245623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_4245623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245623 prefixEnd_4245623 := by exact prefixLift 4245623
  have htrace : WordTrace (prefixWord ++ tailWord_4245623) baseStart_4245623 baseEnd_4245623 := by
    simpa [prefixWord, tailWord_4245623, baseEnd_4245623] using wordTrace_append hprefix tailTrace_4245623
  have hstable : (prefixWord ++ tailWord_4245623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245623).length < 2 ^ (prefixWord ++ tailWord_4245623).sum := by decide
  have hdescent : baseEnd_4245623 < baseStart_4245623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245633 : List Nat := [1, 2, 4, 2, 3, 11]
def baseStart_4245633 : Nat := 118140960795 + 4245633 * 2 ^ 59
def prefixEnd_4245633 : Nat := 4983230072969 + 3 ^ 40 * 4245633 * 2
def baseEnd_4245633 : Nat := 8971400870741945164865

theorem tailTrace_4245633 : CollatzResearch.WordTrace tailWord_4245633 prefixEnd_4245633 8971400870741945164865 := by
  unfold tailWord_4245633
  simp only [CollatzResearch.WordTrace]
  refine ⟨154850957027804212233637553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103233971351869474822425035 154850957027804212233637553)
  ·
    refine ⟨116138217770853159175228165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154850957027804212233637553 116138217770853159175228165)
    ·
      refine ⟨21775915832034967345355281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116138217770853159175228165 21775915832034967345355281)
      ·
        refine ⟨16331936874026225509016461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21775915832034967345355281 16331936874026225509016461)
        ·
          refine ⟨6124476327759834565881173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16331936874026225509016461 6124476327759834565881173)
          ·
            refine ⟨8971400870741945164865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6124476327759834565881173 8971400870741945164865)
            ·
              rfl

theorem cell23_4245633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 11].length) (baseStart_4245633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245633 prefixEnd_4245633 := by exact prefixLift 4245633
  have htrace : WordTrace (prefixWord ++ tailWord_4245633) baseStart_4245633 baseEnd_4245633 := by
    simpa [prefixWord, tailWord_4245633, baseEnd_4245633] using wordTrace_append hprefix tailTrace_4245633
  have hstable : (prefixWord ++ tailWord_4245633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245633).length < 2 ^ (prefixWord ++ tailWord_4245633).sum := by decide
  have hdescent : baseEnd_4245633 < baseStart_4245633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245637 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_4245637 : Nat := 118140960795 + 4245637 * 2 ^ 59
def prefixEnd_4245637 : Nat := 4983230072969 + 3 ^ 40 * 4245637 * 2
def baseEnd_4245637 : Nat := 726684155170970219804059

theorem tailTrace_4245637 : CollatzResearch.WordTrace tailWord_4245637 prefixEnd_4245637 726684155170970219804059 := by
  unfold tailWord_4245637
  simp only [CollatzResearch.WordTrace]
  refine ⟨154851102919789720916783165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103234068613193147277855443 154851102919789720916783165)
  ·
    refine ⟨58069163594921145343793687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154851102919789720916783165 58069163594921145343793687)
    ·
      refine ⟨87103745392381718015690531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58069163594921145343793687 87103745392381718015690531)
      ·
        refine ⟨130655618088572577023535797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87103745392381718015690531 130655618088572577023535797)
        ·
          refine ⟨12248964195803679095956481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130655618088572577023535797 12248964195803679095956481)
          ·
            refine ⟨9186723146852759321967361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12248964195803679095956481 9186723146852759321967361)
            ·
              refine ⟨6890042360139569491475521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186723146852759321967361 6890042360139569491475521)
              ·
                refine ⟨5167531770104677118606641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890042360139569491475521 5167531770104677118606641)
                ·
                  refine ⟨3875648827578507838954981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5167531770104677118606641 3875648827578507838954981)
                  ·
                    refine ⟨726684155170970219804059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875648827578507838954981 726684155170970219804059)
                    ·
                      rfl

theorem cell23_4245637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_4245637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245637 prefixEnd_4245637 := by exact prefixLift 4245637
  have htrace : WordTrace (prefixWord ++ tailWord_4245637) baseStart_4245637 baseEnd_4245637 := by
    simpa [prefixWord, tailWord_4245637, baseEnd_4245637] using wordTrace_append hprefix tailTrace_4245637
  have hstable : (prefixWord ++ tailWord_4245637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245637).length < 2 ^ (prefixWord ++ tailWord_4245637).sum := by decide
  have hdescent : baseEnd_4245637 < baseStart_4245637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245677 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4245677 : Nat := 118140960795 + 4245677 * 2 ^ 59
def prefixEnd_4245677 : Nat := 4983230072969 + 3 ^ 40 * 4245677 * 2
def baseEnd_4245677 : Nat := 2180073004739090502911993

theorem tailTrace_4245677 : CollatzResearch.WordTrace tailWord_4245677 prefixEnd_4245677 2180073004739090502911993 := by
  unfold tailWord_4245677
  simp only [CollatzResearch.WordTrace]
  refine ⟨154852561839644807748239285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103235041226429871832159523 154852561839644807748239285)
  ·
    refine ⟨14517427672466700726397433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154852561839644807748239285 14517427672466700726397433)
    ·
      refine ⟨10888070754350025544798075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14517427672466700726397433 10888070754350025544798075)
      ·
        refine ⟨16332106131525038317197113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888070754350025544798075 16332106131525038317197113)
        ·
          refine ⟨12249079598643778737897835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16332106131525038317197113 12249079598643778737897835)
          ·
            refine ⟨18373619397965668106846753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12249079598643778737897835 18373619397965668106846753)
            ·
              refine ⟨13780214548474251080135065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18373619397965668106846753 13780214548474251080135065)
              ·
                refine ⟨10335160911355688310101299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13780214548474251080135065 10335160911355688310101299)
                ·
                  refine ⟨15502741367033532465151949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10335160911355688310101299 15502741367033532465151949)
                  ·
                    refine ⟨5813528012637574674431981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15502741367033532465151949 5813528012637574674431981)
                    ·
                      refine ⟨2180073004739090502911993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813528012637574674431981 2180073004739090502911993)
                      ·
                        rfl

theorem cell23_4245677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4245677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245677 prefixEnd_4245677 := by exact prefixLift 4245677
  have htrace : WordTrace (prefixWord ++ tailWord_4245677) baseStart_4245677 baseEnd_4245677 := by
    simpa [prefixWord, tailWord_4245677, baseEnd_4245677] using wordTrace_append hprefix tailTrace_4245677
  have hstable : (prefixWord ++ tailWord_4245677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245677).length < 2 ^ (prefixWord ++ tailWord_4245677).sum := by decide
  have hdescent : baseEnd_4245677 < baseStart_4245677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245678 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4245678 : Nat := 118140960795 + 4245678 * 2 ^ 59
def prefixEnd_4245678 : Nat := 4983230072969 + 3 ^ 40 * 4245678 * 2
def baseEnd_4245678 : Nat := 2180073518219744998999489

theorem tailTrace_4245678 : CollatzResearch.WordTrace tailWord_4245678 prefixEnd_4245678 2180073518219744998999489 := by
  unfold tailWord_4245678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356574789080148114878211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103235065541760789946017125 19356574789080148114878211)
  ·
    refine ⟨29034862183620222172317317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356574789080148114878211 29034862183620222172317317)
    ·
      refine ⟨5444036659428791657309497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29034862183620222172317317 5444036659428791657309497)
      ·
        refine ⟨4083027494571593742982123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444036659428791657309497 4083027494571593742982123)
        ·
          refine ⟨6124541241857390614473185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083027494571593742982123 6124541241857390614473185)
          ·
            refine ⟨4593405931393042960854889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124541241857390614473185 4593405931393042960854889)
            ·
              refine ⟨3445054448544782220641167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593405931393042960854889 3445054448544782220641167)
              ·
                refine ⟨5167581672817173330961751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445054448544782220641167 5167581672817173330961751)
                ·
                  refine ⟨7751372509225759996442627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167581672817173330961751 7751372509225759996442627)
                  ·
                    refine ⟨11627058763838639994663941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7751372509225759996442627 11627058763838639994663941)
                    ·
                      refine ⟨2180073518219744998999489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11627058763838639994663941 2180073518219744998999489)
                      ·
                        rfl

theorem cell23_4245678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4245678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245678 prefixEnd_4245678 := by exact prefixLift 4245678
  have htrace : WordTrace (prefixWord ++ tailWord_4245678) baseStart_4245678 baseEnd_4245678 := by
    simpa [prefixWord, tailWord_4245678, baseEnd_4245678] using wordTrace_append hprefix tailTrace_4245678
  have hstable : (prefixWord ++ tailWord_4245678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245678).length < 2 ^ (prefixWord ++ tailWord_4245678).sum := by decide
  have hdescent : baseEnd_4245678 < baseStart_4245678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245681 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_4245681 : Nat := 118140960795 + 4245681 * 2 ^ 59
def prefixEnd_4245681 : Nat := 4983230072969 + 3 ^ 40 * 4245681 * 2
def baseEnd_4245681 : Nat := 2180075058661708487261975

theorem tailTrace_4245681 : CollatzResearch.WordTrace tailWord_4245681 prefixEnd_4245681 2180075058661708487261975 := by
  unfold tailWord_4245681
  simp only [CollatzResearch.WordTrace]
  refine ⟨154852707731630316431384897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103235138487753544287589931 154852707731630316431384897)
  ·
    refine ⟨116139530798722737323538673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154852707731630316431384897 116139530798722737323538673)
    ·
      refine ⟨87104648099042052992654005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116139530798722737323538673 87104648099042052992654005)
      ·
        refine ⟨8166060759285192468061313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87104648099042052992654005 8166060759285192468061313)
        ·
          refine ⟨6124545569463894351045985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8166060759285192468061313 6124545569463894351045985)
          ·
            refine ⟨4593409177097920763284489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124545569463894351045985 4593409177097920763284489)
            ·
              refine ⟨3445056882823440572463367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593409177097920763284489 3445056882823440572463367)
              ·
                refine ⟨5167585324235160858695051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445056882823440572463367 5167585324235160858695051)
                ·
                  refine ⟨7751377986352741288042577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167585324235160858695051 7751377986352741288042577)
                  ·
                    refine ⟨5813533489764555966031933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7751377986352741288042577 5813533489764555966031933)
                    ·
                      refine ⟨2180075058661708487261975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813533489764555966031933 2180075058661708487261975)
                      ·
                        rfl

theorem cell23_4245681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_4245681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245681 prefixEnd_4245681 := by exact prefixLift 4245681
  have htrace : WordTrace (prefixWord ++ tailWord_4245681) baseStart_4245681 baseEnd_4245681 := by
    simpa [prefixWord, tailWord_4245681, baseEnd_4245681] using wordTrace_append hprefix tailTrace_4245681
  have hstable : (prefixWord ++ tailWord_4245681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245681).length < 2 ^ (prefixWord ++ tailWord_4245681).sum := by decide
  have hdescent : baseEnd_4245681 < baseStart_4245681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245684 : List Nat := [2, 5, 3, 1, 1, 1, 10]
def baseStart_4245684 : Nat := 118140960795 + 4245684 * 2 ^ 59
def prefixEnd_4245684 : Nat := 4983230072969 + 3 ^ 40 * 4245684 * 2
def baseEnd_4245684 : Nat := 26914525914860147845981

theorem tailTrace_4245684 : CollatzResearch.WordTrace tailWord_4245684 prefixEnd_4245684 26914525914860147845981 := by
  unfold tailWord_4245684
  simp only [CollatzResearch.WordTrace]
  refine ⟨77426408575309723971872053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103235211433746298629162737 77426408575309723971872053)
  ·
    refine ⟨7258725803935286622363005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77426408575309723971872053 7258725803935286622363005)
    ·
      refine ⟨2722022176475732483386127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7258725803935286622363005 2722022176475732483386127)
      ·
        refine ⟨4083033264713598725079191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722022176475732483386127 4083033264713598725079191)
        ·
          refine ⟨6124549897070398087618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4083033264713598725079191 6124549897070398087618787)
          ·
            refine ⟨9186824845605597131428181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124549897070398087618787 9186824845605597131428181)
            ·
              refine ⟨26914525914860147845981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9186824845605597131428181 26914525914860147845981)
              ·
                rfl

theorem cell23_4245684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 10].length) (baseStart_4245684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245684 prefixEnd_4245684 := by exact prefixLift 4245684
  have htrace : WordTrace (prefixWord ++ tailWord_4245684) baseStart_4245684 baseEnd_4245684 := by
    simpa [prefixWord, tailWord_4245684, baseEnd_4245684] using wordTrace_append hprefix tailTrace_4245684
  have hstable : (prefixWord ++ tailWord_4245684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245684).length < 2 ^ (prefixWord ++ tailWord_4245684).sum := by decide
  have hdescent : baseEnd_4245684 < baseStart_4245684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245694 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_4245694 : Nat := 118140960795 + 4245694 * 2 ^ 59
def prefixEnd_4245694 : Nat := 4983230072969 + 3 ^ 40 * 4245694 * 2
def baseEnd_4245694 : Nat := 2180081733910216936399415

theorem tailTrace_4245694 : CollatzResearch.WordTrace tailWord_4245694 prefixEnd_4245694 2180081733910216936399415 := by
  unfold tailWord_4245694
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356647735072902456451017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103235454587055479767738757 19356647735072902456451017)
  ·
    refine ⟨14517485801304676842338263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19356647735072902456451017 14517485801304676842338263)
    ·
      refine ⟨21776228701957015263507395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14517485801304676842338263 21776228701957015263507395)
      ·
        refine ⟨32664343052935522895261093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21776228701957015263507395 32664343052935522895261093)
        ·
          refine ⟨6124564322425410542861455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32664343052935522895261093 6124564322425410542861455)
          ·
            refine ⟨9186846483638115814292183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124564322425410542861455 9186846483638115814292183)
            ·
              refine ⟨13780269725457173721438275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9186846483638115814292183 13780269725457173721438275)
              ·
                refine ⟨20670404588185760582157413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13780269725457173721438275 20670404588185760582157413)
                ·
                  refine ⟨3875700860284830109154515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20670404588185760582157413 3875700860284830109154515)
                  ·
                    refine ⟨5813551290427245163731773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3875700860284830109154515 5813551290427245163731773)
                    ·
                      refine ⟨2180081733910216936399415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813551290427245163731773 2180081733910216936399415)
                      ·
                        rfl

theorem cell23_4245694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_4245694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245694 prefixEnd_4245694 := by exact prefixLift 4245694
  have htrace : WordTrace (prefixWord ++ tailWord_4245694) baseStart_4245694 baseEnd_4245694 := by
    simpa [prefixWord, tailWord_4245694, baseEnd_4245694] using wordTrace_append hprefix tailTrace_4245694
  have hstable : (prefixWord ++ tailWord_4245694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245694).length < 2 ^ (prefixWord ++ tailWord_4245694).sum := by decide
  have hdescent : baseEnd_4245694 < baseStart_4245694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245703 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_4245703 : Nat := 118140960795 + 4245703 * 2 ^ 59
def prefixEnd_4245703 : Nat := 4983230072969 + 3 ^ 40 * 4245703 * 2
def baseEnd_4245703 : Nat := 2180086355236107401186873

theorem tailTrace_4245703 : CollatzResearch.WordTrace tailWord_4245703 prefixEnd_4245703 2180086355236107401186873 := by
  unfold tailWord_4245703
  simp only [CollatzResearch.WordTrace]
  refine ⟨154853510137550614188685763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103235673425033742792457175 154853510137550614188685763)
  ·
    refine ⟨232280265206325921283028645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154853510137550614188685763 232280265206325921283028645)
    ·
      refine ⟨43552549726186110240567871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232280265206325921283028645 43552549726186110240567871)
      ·
        refine ⟨65328824589279165360851807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43552549726186110240567871 65328824589279165360851807)
        ·
          refine ⟨97993236883918748041277711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65328824589279165360851807 97993236883918748041277711)
          ·
            refine ⟨146989855325878122061916567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97993236883918748041277711 146989855325878122061916567)
            ·
              refine ⟨220484782988817183092874851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146989855325878122061916567 220484782988817183092874851)
              ·
                refine ⟨330727174483225774639312277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220484782988817183092874851 330727174483225774639312277)
                ·
                  refine ⟨15502836303901208186217763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330727174483225774639312277 15502836303901208186217763)
                  ·
                    refine ⟨23254254455851812279326645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15502836303901208186217763 23254254455851812279326645)
                    ·
                      refine ⟨2180086355236107401186873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23254254455851812279326645 2180086355236107401186873)
                      ·
                        rfl

theorem cell23_4245703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_4245703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245703 prefixEnd_4245703 := by exact prefixLift 4245703
  have htrace : WordTrace (prefixWord ++ tailWord_4245703) baseStart_4245703 baseEnd_4245703 := by
    simpa [prefixWord, tailWord_4245703, baseEnd_4245703] using wordTrace_append hprefix tailTrace_4245703
  have hstable : (prefixWord ++ tailWord_4245703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245703).length < 2 ^ (prefixWord ++ tailWord_4245703).sum := by decide
  have hdescent : baseEnd_4245703 < baseStart_4245703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245710 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_4245710 : Nat := 118140960795 + 4245710 * 2 ^ 59
def prefixEnd_4245710 : Nat := 4983230072969 + 3 ^ 40 * 4245710 * 2
def baseEnd_4245710 : Nat := 726696649866896291266447

theorem tailTrace_4245710 : CollatzResearch.WordTrace tailWord_4245710 prefixEnd_4245710 726696649866896291266447 := by
  unfold tailWord_4245710
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356720681065656798023823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103235843632350169589460389 19356720681065656798023823)
  ·
    refine ⟨29035081021598485197035735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356720681065656798023823 29035081021598485197035735)
    ·
      refine ⟨43552621532397727795553603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29035081021598485197035735 43552621532397727795553603)
      ·
        refine ⟨65328932298596591693330405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43552621532397727795553603 65328932298596591693330405)
        ·
          refine ⟨12249174805986860942499451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65328932298596591693330405 12249174805986860942499451)
          ·
            refine ⟨18373762208980291413749177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12249174805986860942499451 18373762208980291413749177)
            ·
              refine ⟨13780321656735218560311883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18373762208980291413749177 13780321656735218560311883)
              ·
                refine ⟨20670482485102827840467825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13780321656735218560311883 20670482485102827840467825)
                ·
                  refine ⟨15502861863827120880350869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20670482485102827840467825 15502861863827120880350869)
                  ·
                    refine ⟨726696649866896291266447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15502861863827120880350869 726696649866896291266447)
                    ·
                      rfl

theorem cell23_4245710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_4245710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245710 prefixEnd_4245710 := by exact prefixLift 4245710
  have htrace : WordTrace (prefixWord ++ tailWord_4245710) baseStart_4245710 baseEnd_4245710 := by
    simpa [prefixWord, tailWord_4245710, baseEnd_4245710] using wordTrace_append hprefix tailTrace_4245710
  have hstable : (prefixWord ++ tailWord_4245710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245710).length < 2 ^ (prefixWord ++ tailWord_4245710).sum := by decide
  have hdescent : baseEnd_4245710 < baseStart_4245710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245753 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_4245753 : Nat := 118140960795 + 4245753 * 2 ^ 59
def prefixEnd_4245753 : Nat := 4983230072969 + 3 ^ 40 * 4245753 * 2
def baseEnd_4245753 : Nat := 726704009756277401853881

theorem tailTrace_4245753 : CollatzResearch.WordTrace tailWord_4245753 prefixEnd_4245753 726704009756277401853881 := by
  unfold tailWord_4245753
  simp only [CollatzResearch.WordTrace]
  refine ⟨154855333787369472728005913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103236889191579648485337275 154855333787369472728005913)
  ·
    refine ⟨116141500340527104546004435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154855333787369472728005913 116141500340527104546004435)
    ·
      refine ⟨174212250510790656819006653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116141500340527104546004435 174212250510790656819006653)
      ·
        refine ⟨65329593941546496307127495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174212250510790656819006653 65329593941546496307127495)
        ·
          refine ⟨97994390912319744460691243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65329593941546496307127495 97994390912319744460691243)
          ·
            refine ⟨146991586368479616691036865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97994390912319744460691243 146991586368479616691036865)
            ·
              refine ⟨110243689776359712518277649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146991586368479616691036865 110243689776359712518277649)
              ·
                refine ⟨82682767332269784388708237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110243689776359712518277649 82682767332269784388708237)
                ·
                  refine ⟨31006037749601169145765589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82682767332269784388708237 31006037749601169145765589)
                  ·
                    refine ⟨726704009756277401853881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31006037749601169145765589 726704009756277401853881)
                    ·
                      rfl

theorem cell23_4245753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_4245753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245753 prefixEnd_4245753 := by exact prefixLift 4245753
  have htrace : WordTrace (prefixWord ++ tailWord_4245753) baseStart_4245753 baseEnd_4245753 := by
    simpa [prefixWord, tailWord_4245753, baseEnd_4245753] using wordTrace_append hprefix tailTrace_4245753
  have hstable : (prefixWord ++ tailWord_4245753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245753).length < 2 ^ (prefixWord ++ tailWord_4245753).sum := by decide
  have hdescent : baseEnd_4245753 < baseStart_4245753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245768 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_4245768 : Nat := 118140960795 + 4245768 * 2 ^ 59
def prefixEnd_4245768 : Nat := 4983230072969 + 3 ^ 40 * 4245768 * 2
def baseEnd_4245768 : Nat := 2180119731478649646874075

theorem tailTrace_4245768 : CollatzResearch.WordTrace tailWord_4245768 prefixEnd_4245768 2180119731478649646874075 := by
  unfold tailWord_4245768
  simp only [CollatzResearch.WordTrace]
  refine ⟨77427940441157565144900979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103237253921543420193201305 77427940441157565144900979)
  ·
    refine ⟨116141910661736347717351469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77427940441157565144900979 116141910661736347717351469)
    ·
      refine ⟨43553216498151130394006801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116141910661736347717351469 43553216498151130394006801)
      ·
        refine ⟨32664912373613347795505101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43553216498151130394006801 32664912373613347795505101)
        ·
          refine ⟨12249342140105005423314413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32664912373613347795505101 12249342140105005423314413)
          ·
            refine ⟨4593503302539377033742905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12249342140105005423314413 4593503302539377033742905)
            ·
              refine ⟨3445127476904532775307179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593503302539377033742905 3445127476904532775307179)
              ·
                refine ⟨5167691215356799162960769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445127476904532775307179 5167691215356799162960769)
                ·
                  refine ⟨3875768411517599372220577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5167691215356799162960769 3875768411517599372220577)
                  ·
                    refine ⟨2906826308638199529165433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3875768411517599372220577 2906826308638199529165433)
                    ·
                      refine ⟨2180119731478649646874075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906826308638199529165433 2180119731478649646874075)
                      ·
                        rfl

theorem cell23_4245768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_4245768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245768 prefixEnd_4245768 := by exact prefixLift 4245768
  have htrace : WordTrace (prefixWord ++ tailWord_4245768) baseStart_4245768 baseEnd_4245768 := by
    simpa [prefixWord, tailWord_4245768, baseEnd_4245768] using wordTrace_append hprefix tailTrace_4245768
  have hstable : (prefixWord ++ tailWord_4245768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245768).length < 2 ^ (prefixWord ++ tailWord_4245768).sum := by decide
  have hdescent : baseEnd_4245768 < baseStart_4245768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245844 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_4245844 : Nat := 118140960795 + 4245844 * 2 ^ 59
def prefixEnd_4245844 : Nat := 4983230072969 + 3 ^ 40 * 4245844 * 2
def baseEnd_4245844 : Nat := 2180158756008391349523725

theorem tailTrace_4245844 : CollatzResearch.WordTrace tailWord_4245844 prefixEnd_4245844 2180158756008391349523725 := by
  unfold tailWord_4245844
  simp only [CollatzResearch.WordTrace]
  refine ⟨77429326415019897634784293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103239101886693196846379057 77429326415019897634784293)
  ·
    refine ⟨14517998702816230806522055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77429326415019897634784293 14517998702816230806522055)
    ·
      refine ⟨21776998054224346209783083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14517998702816230806522055 21776998054224346209783083)
      ·
        refine ⟨32665497081336519314674625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21776998054224346209783083 32665497081336519314674625)
        ·
          refine ⟨24499122811002389486005969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32665497081336519314674625 24499122811002389486005969)
          ·
            refine ⟨18374342108251792114504477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24499122811002389486005969 18374342108251792114504477)
            ·
              refine ⟨6890378290594422042939179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18374342108251792114504477 6890378290594422042939179)
              ·
                refine ⟨10335567435891633064408769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890378290594422042939179 10335567435891633064408769)
                ·
                  refine ⟨7751675576918724798306577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10335567435891633064408769 7751675576918724798306577)
                  ·
                    refine ⟨5813756682689043598729933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7751675576918724798306577 5813756682689043598729933)
                    ·
                      refine ⟨2180158756008391349523725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813756682689043598729933 2180158756008391349523725)
                      ·
                        rfl

theorem cell23_4245844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_4245844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245844 prefixEnd_4245844 := by exact prefixLift 4245844
  have htrace : WordTrace (prefixWord ++ tailWord_4245844) baseStart_4245844 baseEnd_4245844 := by
    simpa [prefixWord, tailWord_4245844, baseEnd_4245844] using wordTrace_append hprefix tailTrace_4245844
  have hstable : (prefixWord ++ tailWord_4245844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245844).length < 2 ^ (prefixWord ++ tailWord_4245844).sum := by decide
  have hdescent : baseEnd_4245844 < baseStart_4245844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245864 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 6]
def baseStart_4245864 : Nat := 118140960795 + 4245864 * 2 ^ 59
def prefixEnd_4245864 : Nat := 4983230072969 + 3 ^ 40 * 4245864 * 2
def baseEnd_4245864 : Nat := 242241002846831252363737

theorem tailTrace_4245864 : CollatzResearch.WordTrace tailWord_4245864 prefixEnd_4245864 242241002846831252363737 := by
  unfold tailWord_4245864
  simp only [CollatzResearch.WordTrace]
  refine ⟨77429691144983669342648323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103239588193311559123531097 77429691144983669342648323)
  ·
    refine ⟨116144536717475504013972485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77429691144983669342648323 116144536717475504013972485)
    ·
      refine ⟨21777100634526657002619841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116144536717475504013972485 21777100634526657002619841)
      ·
        refine ⟨16332825475894992751964881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21777100634526657002619841 16332825475894992751964881)
        ·
          refine ⟨12249619106921244563973661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16332825475894992751964881 12249619106921244563973661)
          ·
            refine ⟨4593607165095466711490123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12249619106921244563973661 4593607165095466711490123)
            ·
              refine ⟨6890410747643200067235185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593607165095466711490123 6890410747643200067235185)
              ·
                refine ⟨5167808060732400050426389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6890410747643200067235185 5167808060732400050426389)
                ·
                  refine ⟨242241002846831252363737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5167808060732400050426389 242241002846831252363737)
                  ·
                    rfl

theorem cell23_4245864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_4245864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245864 prefixEnd_4245864 := by exact prefixLift 4245864
  have htrace : WordTrace (prefixWord ++ tailWord_4245864) baseStart_4245864 baseEnd_4245864 := by
    simpa [prefixWord, tailWord_4245864, baseEnd_4245864] using wordTrace_append hprefix tailTrace_4245864
  have hstable : (prefixWord ++ tailWord_4245864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245864).length < 2 ^ (prefixWord ++ tailWord_4245864).sum := by decide
  have hdescent : baseEnd_4245864 < baseStart_4245864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245874 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4245874 : Nat := 118140960795 + 4245874 * 2 ^ 59
def prefixEnd_4245874 : Nat := 4983230072969 + 3 ^ 40 * 4245874 * 2
def baseEnd_4245874 : Nat := 2180174160428026232148587

theorem tailTrace_4245874 : CollatzResearch.WordTrace tailWord_4245874 prefixEnd_4245874 2180174160428026232148587 := by
  unfold tailWord_4245874
  simp only [CollatzResearch.WordTrace]
  refine ⟨38714936754982777598290169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103239831346620740262107117 38714936754982777598290169)
  ·
    refine ⟨29036202566237083198717627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38714936754982777598290169 29036202566237083198717627)
    ·
      refine ⟨43554303849355624798076441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29036202566237083198717627 43554303849355624798076441)
      ·
        refine ⟨32665727887016718598557331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43554303849355624798076441 32665727887016718598557331)
        ·
          refine ⟨48998591830525077897835997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32665727887016718598557331 48998591830525077897835997)
          ·
            refine ⟨18374471936446904211688499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48998591830525077897835997 18374471936446904211688499)
            ·
              refine ⟨27561707904670356317532749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18374471936446904211688499 27561707904670356317532749)
              ·
                refine ⟨10335640464251383619074781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27561707904670356317532749 10335640464251383619074781)
                ·
                  refine ⟨3875865174094268857153043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10335640464251383619074781 3875865174094268857153043)
                  ·
                    refine ⟨5813797761141403285729565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3875865174094268857153043 5813797761141403285729565)
                    ·
                      refine ⟨2180174160428026232148587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5813797761141403285729565 2180174160428026232148587)
                      ·
                        rfl

theorem cell23_4245874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4245874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245874 prefixEnd_4245874 := by exact prefixLift 4245874
  have htrace : WordTrace (prefixWord ++ tailWord_4245874) baseStart_4245874 baseEnd_4245874 := by
    simpa [prefixWord, tailWord_4245874, baseEnd_4245874] using wordTrace_append hprefix tailTrace_4245874
  have hstable : (prefixWord ++ tailWord_4245874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245874).length < 2 ^ (prefixWord ++ tailWord_4245874).sum := by decide
  have hdescent : baseEnd_4245874 < baseStart_4245874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245914 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4245914 : Nat := 118140960795 + 4245914 * 2 ^ 59
def prefixEnd_4245914 : Nat := 4983230072969 + 3 ^ 40 * 4245914 * 2
def baseEnd_4245914 : Nat := 2180194699654206075648403

theorem tailTrace_4245914 : CollatzResearch.WordTrace tailWord_4245914 prefixEnd_4245914 2180194699654206075648403 := by
  unfold tailWord_4245914
  simp only [CollatzResearch.WordTrace]
  refine ⟨38715301484946549306154199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103240803959857464816411197 38715301484946549306154199)
  ·
    refine ⟨58072952227419823959231299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38715301484946549306154199 58072952227419823959231299)
    ·
      refine ⟨87109428341129735938846949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58072952227419823959231299 87109428341129735938846949)
      ·
        refine ⟨16333017813961825488533803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87109428341129735938846949 16333017813961825488533803)
        ·
          refine ⟨24499526720942738232800705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16333017813961825488533803 24499526720942738232800705)
          ·
            refine ⟨18374645040707053674600529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24499526720942738232800705 18374645040707053674600529)
            ·
              refine ⟨13780983780530290255950397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18374645040707053674600529 13780983780530290255950397)
              ·
                refine ⟨5167868917698858845981399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13780983780530290255950397 5167868917698858845981399)
                ·
                  refine ⟨7751803376548288268972099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167868917698858845981399 7751803376548288268972099)
                  ·
                    refine ⟨11627705064822432403458149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7751803376548288268972099 11627705064822432403458149)
                    ·
                      refine ⟨2180194699654206075648403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11627705064822432403458149 2180194699654206075648403)
                      ·
                        rfl

theorem cell23_4245914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4245914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245914 prefixEnd_4245914 := by exact prefixLift 4245914
  have htrace : WordTrace (prefixWord ++ tailWord_4245914) baseStart_4245914 baseEnd_4245914 := by
    simpa [prefixWord, tailWord_4245914, baseEnd_4245914] using wordTrace_append hprefix tailTrace_4245914
  have hstable : (prefixWord ++ tailWord_4245914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245914).length < 2 ^ (prefixWord ++ tailWord_4245914).sum := by decide
  have hdescent : baseEnd_4245914 < baseStart_4245914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245918 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4245918 : Nat := 118140960795 + 4245918 * 2 ^ 59
def prefixEnd_4245918 : Nat := 4983230072969 + 3 ^ 40 * 4245918 * 2
def baseEnd_4245918 : Nat := 2180196753576824059998385

theorem tailTrace_4245918 : CollatzResearch.WordTrace tailWord_4245918 prefixEnd_4245918 2180196753576824059998385 := by
  unfold tailWord_4245918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19357668978971463238470301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103240901221181137271841605 19357668978971463238470301)
  ·
    refine ⟨7259125867114298714426363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19357668978971463238470301 7259125867114298714426363)
    ·
      refine ⟨10888688800671448071639545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7259125867114298714426363 10888688800671448071639545)
      ·
        refine ⟨8166516600503586053729659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10888688800671448071639545 8166516600503586053729659)
        ·
          refine ⟨12249774900755379080594489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8166516600503586053729659 12249774900755379080594489)
          ·
            refine ⟨9187331175566534310445867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12249774900755379080594489 9187331175566534310445867)
            ·
              refine ⟨13780996763349801465668801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9187331175566534310445867 13780996763349801465668801)
              ·
                refine ⟨10335747572512351099251601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13780996763349801465668801 10335747572512351099251601)
                ·
                  refine ⟨7751810679384263324438701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10335747572512351099251601 7751810679384263324438701)
                  ·
                    refine ⟨2906929004769098746664513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7751810679384263324438701 2906929004769098746664513)
                    ·
                      refine ⟨2180196753576824059998385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906929004769098746664513 2180196753576824059998385)
                      ·
                        rfl

theorem cell23_4245918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4245918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245918 prefixEnd_4245918 := by exact prefixLift 4245918
  have htrace : WordTrace (prefixWord ++ tailWord_4245918) baseStart_4245918 baseEnd_4245918 := by
    simpa [prefixWord, tailWord_4245918, baseEnd_4245918] using wordTrace_append hprefix tailTrace_4245918
  have hstable : (prefixWord ++ tailWord_4245918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245918).length < 2 ^ (prefixWord ++ tailWord_4245918).sum := by decide
  have hdescent : baseEnd_4245918 < baseStart_4245918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245920 : List Nat := [2, 1, 1, 4, 1, 3, 11]
def baseStart_4245920 : Nat := 118140960795 + 4245920 * 2 ^ 59
def prefixEnd_4245920 : Nat := 4983230072969 + 3 ^ 40 * 4245920 * 2
def baseEnd_4245920 : Nat := 26916021981952259903375

theorem tailTrace_4245920 : CollatzResearch.WordTrace tailWord_4245920 prefixEnd_4245920 26916021981952259903375 := by
  unfold tailWord_4245920
  simp only [CollatzResearch.WordTrace]
  refine ⟨77430712388882230124667607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103240949851842973499556809 77430712388882230124667607)
  ·
    refine ⟨116146068583323345187001411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77430712388882230124667607 116146068583323345187001411)
    ·
      refine ⟨174219102874985017780502117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116146068583323345187001411 174219102874985017780502117)
      ·
        refine ⟨32666081789059690833844147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174219102874985017780502117 32666081789059690833844147)
        ·
          refine ⟨48999122683589536250766221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32666081789059690833844147 48999122683589536250766221)
          ·
            refine ⟨18374671006346076094037333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48999122683589536250766221 18374671006346076094037333)
            ·
              refine ⟨26916021981952259903375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18374671006346076094037333 26916021981952259903375)
              ·
                rfl

theorem cell23_4245920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 11].length) (baseStart_4245920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245920 prefixEnd_4245920 := by exact prefixLift 4245920
  have htrace : WordTrace (prefixWord ++ tailWord_4245920) baseStart_4245920 baseEnd_4245920 := by
    simpa [prefixWord, tailWord_4245920, baseEnd_4245920] using wordTrace_append hprefix tailTrace_4245920
  have hstable : (prefixWord ++ tailWord_4245920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245920).length < 2 ^ (prefixWord ++ tailWord_4245920).sum := by decide
  have hdescent : baseEnd_4245920 < baseStart_4245920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245927 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4245927 : Nat := 118140960795 + 4245927 * 2 ^ 59
def prefixEnd_4245927 : Nat := 4983230072969 + 3 ^ 40 * 4245927 * 2
def baseEnd_4245927 : Nat := 2180201374902714524785843

theorem tailTrace_4245927 : CollatzResearch.WordTrace tailWord_4245927 prefixEnd_4245927 2180201374902714524785843 := by
  unfold tailWord_4245927
  simp only [CollatzResearch.WordTrace]
  refine ⟨154861680088739100444840035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103241120059159400296560023 154861680088739100444840035)
  ·
    refine ⟨232292520133108650667260053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154861680088739100444840035 232292520133108650667260053)
    ·
      refine ⟨10888711881239468000027815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 232292520133108650667260053 10888711881239468000027815)
      ·
        refine ⟨16333067821859202000041723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10888711881239468000027815 16333067821859202000041723)
        ·
          refine ⟨24499601732788803000062585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16333067821859202000041723 24499601732788803000062585)
          ·
            refine ⟨18374701299591602250046939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24499601732788803000062585 18374701299591602250046939)
            ·
              refine ⟨27562051949387403375070409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18374701299591602250046939 27562051949387403375070409)
              ·
                refine ⟨20671538962040552531302807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27562051949387403375070409 20671538962040552531302807)
                ·
                  refine ⟨31007308443060828796954211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20671538962040552531302807 31007308443060828796954211)
                  ·
                    refine ⟨46510962664591243195431317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31007308443060828796954211 46510962664591243195431317)
                    ·
                      refine ⟨2180201374902714524785843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46510962664591243195431317 2180201374902714524785843)
                      ·
                        rfl

theorem cell23_4245927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4245927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245927 prefixEnd_4245927 := by exact prefixLift 4245927
  have htrace : WordTrace (prefixWord ++ tailWord_4245927) baseStart_4245927 baseEnd_4245927 := by
    simpa [prefixWord, tailWord_4245927, baseEnd_4245927] using wordTrace_append hprefix tailTrace_4245927
  have hstable : (prefixWord ++ tailWord_4245927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245927).length < 2 ^ (prefixWord ++ tailWord_4245927).sum := by decide
  have hdescent : baseEnd_4245927 < baseStart_4245927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245937 : List Nat := [1, 2, 2, 4, 1, 3, 2, 8]
def baseStart_4245937 : Nat := 118140960795 + 4245937 * 2 ^ 59
def prefixEnd_4245937 : Nat := 4983230072969 + 3 ^ 40 * 4245937 * 2
def baseEnd_4245937 : Nat := 80748389248491092061511

theorem tailTrace_4245937 : CollatzResearch.WordTrace tailWord_4245937 prefixEnd_4245937 80748389248491092061511 := by
  unfold tailWord_4245937
  simp only [CollatzResearch.WordTrace]
  refine ⟨154862044818702872152704065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103241363212468581435136043 154862044818702872152704065)
  ·
    refine ⟨116146533614027154114528049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154862044818702872152704065 116146533614027154114528049)
    ·
      refine ⟨87109900210520365585896037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116146533614027154114528049 87109900210520365585896037)
      ·
        refine ⟨16333106289472568547355507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87109900210520365585896037 16333106289472568547355507)
        ·
          refine ⟨24499659434208852821033261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16333106289472568547355507 24499659434208852821033261)
          ·
            refine ⟨9187372287828319807887473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24499659434208852821033261 9187372287828319807887473)
            ·
              refine ⟨6890529215871239855915605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9187372287828319807887473 6890529215871239855915605)
              ·
                refine ⟨80748389248491092061511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6890529215871239855915605 80748389248491092061511)
                ·
                  rfl

theorem cell23_4245937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 8].length) (baseStart_4245937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245937 prefixEnd_4245937 := by exact prefixLift 4245937
  have htrace : WordTrace (prefixWord ++ tailWord_4245937) baseStart_4245937 baseEnd_4245937 := by
    simpa [prefixWord, tailWord_4245937, baseEnd_4245937] using wordTrace_append hprefix tailTrace_4245937
  have hstable : (prefixWord ++ tailWord_4245937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245937).length < 2 ^ (prefixWord ++ tailWord_4245937).sum := by decide
  have hdescent : baseEnd_4245937 < baseStart_4245937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245941 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4245941 : Nat := 118140960795 + 4245941 * 2 ^ 59
def prefixEnd_4245941 : Nat := 4983230072969 + 3 ^ 40 * 4245941 * 2
def baseEnd_4245941 : Nat := 726736187877292490003593

theorem tailTrace_4245941 : CollatzResearch.WordTrace tailWord_4245941 prefixEnd_4245941 726736187877292490003593 := by
  unfold tailWord_4245941
  simp only [CollatzResearch.WordTrace]
  refine ⟨154862190710688380835849677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103241460473792253890566451 154862190710688380835849677)
  ·
    refine ⟨58073321516508142813443629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154862190710688380835849677 58073321516508142813443629)
    ·
      refine ⟨21777495568690553555041361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58073321516508142813443629 21777495568690553555041361)
      ·
        refine ⟨16333121676517915166281021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21777495568690553555041361 16333121676517915166281021)
        ·
          refine ⟨6124920628694218187355383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16333121676517915166281021 6124920628694218187355383)
          ·
            refine ⟨9187380943041327281033075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124920628694218187355383 9187380943041327281033075)
            ·
              refine ⟨13781071414561990921549613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9187380943041327281033075 13781071414561990921549613)
              ·
                refine ⟨5167901780460746595581105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13781071414561990921549613 5167901780460746595581105)
                ·
                  refine ⟨3875926335345559946685829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5167901780460746595581105 3875926335345559946685829)
                  ·
                    refine ⟨726736187877292490003593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875926335345559946685829 726736187877292490003593)
                    ·
                      rfl

theorem cell23_4245941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4245941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245941 prefixEnd_4245941 := by exact prefixLift 4245941
  have htrace : WordTrace (prefixWord ++ tailWord_4245941) baseStart_4245941 baseEnd_4245941 := by
    simpa [prefixWord, tailWord_4245941, baseEnd_4245941] using wordTrace_append hprefix tailTrace_4245941
  have hstable : (prefixWord ++ tailWord_4245941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245941).length < 2 ^ (prefixWord ++ tailWord_4245941).sum := by decide
  have hdescent : baseEnd_4245941 < baseStart_4245941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246044 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 7]
def baseStart_4246044 : Nat := 118140960795 + 4246044 * 2 ^ 59
def prefixEnd_4246044 : Nat := 4983230072969 + 3 ^ 40 * 4246044 * 2
def baseEnd_4246044 : Nat := 242251272459921174113645

theorem tailTrace_4246044 : CollatzResearch.WordTrace tailWord_4246044 prefixEnd_4246044 242251272459921174113645 := by
  unfold tailWord_4246044
  simp only [CollatzResearch.WordTrace]
  refine ⟨77432973714657614713424593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103243964952876819617899457 77432973714657614713424593)
  ·
    refine ⟨58074730285993211035068445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77432973714657614713424593 58074730285993211035068445)
    ·
      refine ⟨21778023857247454138150667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58074730285993211035068445 21778023857247454138150667)
      ·
        refine ⟨32667035785871181207226001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21778023857247454138150667 32667035785871181207226001)
        ·
          refine ⟨24500276839403385905419501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32667035785871181207226001 24500276839403385905419501)
          ·
            refine ⟨9187603814776269714532313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24500276839403385905419501 9187603814776269714532313)
            ·
              refine ⟨6890702861082202285899235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9187603814776269714532313 6890702861082202285899235)
              ·
                refine ⟨10336054291623303428848853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890702861082202285899235 10336054291623303428848853)
                ·
                  refine ⟨242251272459921174113645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10336054291623303428848853 242251272459921174113645)
                  ·
                    rfl

theorem cell23_4246044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_4246044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246044 prefixEnd_4246044 := by exact prefixLift 4246044
  have htrace : WordTrace (prefixWord ++ tailWord_4246044) baseStart_4246044 baseEnd_4246044 := by
    simpa [prefixWord, tailWord_4246044, baseEnd_4246044] using wordTrace_append hprefix tailTrace_4246044
  have hstable : (prefixWord ++ tailWord_4246044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246044).length < 2 ^ (prefixWord ++ tailWord_4246044).sum := by decide
  have hdescent : baseEnd_4246044 < baseStart_4246044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246064 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2]
def baseStart_4246064 : Nat := 118140960795 + 4246064 * 2 ^ 59
def prefixEnd_4246064 : Nat := 4983230072969 + 3 ^ 40 * 4246064 * 2
def baseEnd_4246064 : Nat := 2180271721752380488772713

theorem tailTrace_4246064 : CollatzResearch.WordTrace tailWord_4246064 prefixEnd_4246064 2180271721752380488772713 := by
  unfold tailWord_4246064
  simp only [CollatzResearch.WordTrace]
  refine ⟨77433338444621386421288623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103244451259495181895051497 77433338444621386421288623)
  ·
    refine ⟨116150007666932079631932935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77433338444621386421288623 116150007666932079631932935)
    ·
      refine ⟨174225011500398119447899403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116150007666932079631932935 174225011500398119447899403)
      ·
        refine ⟨261337517250597179171849105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174225011500398119447899403 261337517250597179171849105)
        ·
          refine ⟨196003137937947884378886829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261337517250597179171849105 196003137937947884378886829)
          ·
            refine ⟨73501176726730456642082561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196003137937947884378886829 73501176726730456642082561)
            ·
              refine ⟨55125882545047842481561921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73501176726730456642082561 55125882545047842481561921)
              ·
                refine ⟨41344411908785881861171441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55125882545047842481561921 41344411908785881861171441)
                ·
                  refine ⟨31008308931589411395878581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41344411908785881861171441 31008308931589411395878581)
                  ·
                    refine ⟨2907028962336507318363617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31008308931589411395878581 2907028962336507318363617)
                    ·
                      refine ⟨2180271721752380488772713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907028962336507318363617 2180271721752380488772713)
                      ·
                        rfl

theorem cell23_4246064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2].length) (baseStart_4246064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246064 prefixEnd_4246064 := by exact prefixLift 4246064
  have htrace : WordTrace (prefixWord ++ tailWord_4246064) baseStart_4246064 baseEnd_4246064 := by
    simpa [prefixWord, tailWord_4246064, baseEnd_4246064] using wordTrace_append hprefix tailTrace_4246064
  have hstable : (prefixWord ++ tailWord_4246064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246064).length < 2 ^ (prefixWord ++ tailWord_4246064).sum := by decide
  have hdescent : baseEnd_4246064 < baseStart_4246064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246094 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_4246094 : Nat := 118140960795 + 4246094 * 2 ^ 59
def prefixEnd_4246094 : Nat := 4983230072969 + 3 ^ 40 * 4246094 * 2
def baseEnd_4246094 : Nat := 2180287126172015371397575

theorem tailTrace_4246094 : CollatzResearch.WordTrace tailWord_4246094 prefixEnd_4246094 2180287126172015371397575 := by
  unfold tailWord_4246094
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358471384891760995771167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103245180719422725310779557 19358471384891760995771167)
  ·
    refine ⟨29037707077337641493656751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358471384891760995771167 29037707077337641493656751)
    ·
      refine ⟨43556560616006462240485127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29037707077337641493656751 43556560616006462240485127)
      ·
        refine ⟨65334840924009693360727691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43556560616006462240485127 65334840924009693360727691)
        ·
          refine ⟨98002261386014540041091537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65334840924009693360727691 98002261386014540041091537)
          ·
            refine ⟨73501696039510905030818653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98002261386014540041091537 73501696039510905030818653)
            ·
              refine ⟨27563136014816589386556995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73501696039510905030818653 27563136014816589386556995)
              ·
                refine ⟨41344704022224884079835493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27563136014816589386556995 41344704022224884079835493)
                ·
                  refine ⟨7752132004167165764969155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41344704022224884079835493 7752132004167165764969155)
                  ·
                    refine ⟨11628198006250748647453733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7752132004167165764969155 11628198006250748647453733)
                    ·
                      refine ⟨2180287126172015371397575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11628198006250748647453733 2180287126172015371397575)
                      ·
                        rfl

theorem cell23_4246094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_4246094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246094 prefixEnd_4246094 := by exact prefixLift 4246094
  have htrace : WordTrace (prefixWord ++ tailWord_4246094) baseStart_4246094 baseEnd_4246094 := by
    simpa [prefixWord, tailWord_4246094, baseEnd_4246094] using wordTrace_append hprefix tailTrace_4246094
  have hstable : (prefixWord ++ tailWord_4246094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246094).length < 2 ^ (prefixWord ++ tailWord_4246094).sum := by decide
  have hdescent : baseEnd_4246094 < baseStart_4246094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246146 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_4246146 : Nat := 118140960795 + 4246146 * 2 ^ 59
def prefixEnd_4246146 : Nat := 4983230072969 + 3 ^ 40 * 4246146 * 2
def baseEnd_4246146 : Nat := 242257091907338796438593

theorem tailTrace_4246146 : CollatzResearch.WordTrace tailWord_4246146 prefixEnd_4246146 242257091907338796438593 := by
  unfold tailWord_4246146
  simp only [CollatzResearch.WordTrace]
  refine ⟨38717416918736425211765573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103246445116630467231374861 38717416918736425211765573)
  ·
    refine ⟨7259515672263079727206045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38717416918736425211765573 7259515672263079727206045)
    ·
      refine ⟨2722318377098654897702267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7259515672263079727206045 2722318377098654897702267)
      ·
        refine ⟨4083477565647982346553401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722318377098654897702267 4083477565647982346553401)
        ·
          refine ⟨3062608174235986759915051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083477565647982346553401 3062608174235986759915051)
          ·
            refine ⟨4593912261353980139872577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062608174235986759915051 4593912261353980139872577)
            ·
              refine ⟨3445434196015485104904433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593912261353980139872577 3445434196015485104904433)
              ·
                refine ⟨2584075647011613828678325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3445434196015485104904433 2584075647011613828678325)
                ·
                  refine ⟨242257091907338796438593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2584075647011613828678325 242257091907338796438593)
                  ·
                    rfl

theorem cell23_4246146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_4246146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246146 prefixEnd_4246146 := by exact prefixLift 4246146
  have htrace : WordTrace (prefixWord ++ tailWord_4246146) baseStart_4246146 baseEnd_4246146 := by
    simpa [prefixWord, tailWord_4246146, baseEnd_4246146] using wordTrace_append hprefix tailTrace_4246146
  have hstable : (prefixWord ++ tailWord_4246146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246146).length < 2 ^ (prefixWord ++ tailWord_4246146).sum := by decide
  have hdescent : baseEnd_4246146 < baseStart_4246146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246195 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 1, 1, 3]
def baseStart_4246195 : Nat := 118140960795 + 4246195 * 2 ^ 59
def prefixEnd_4246195 : Nat := 4983230072969 + 3 ^ 40 * 4246195 * 2
def baseEnd_4246195 : Nat := 2180338987718119476234611

theorem tailTrace_4246195 : CollatzResearch.WordTrace tailWord_4246195 prefixEnd_4246195 2180338987718119476234611 := by
  unfold tailWord_4246195
  simp only [CollatzResearch.WordTrace]
  refine ⟨154871454851768182215596039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103247636567845454810397359 154871454851768182215596039)
  ·
    refine ⟨232307182277652273323394059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154871454851768182215596039 232307182277652273323394059)
    ·
      refine ⟨348460773416478409985091089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232307182277652273323394059 348460773416478409985091089)
      ·
        refine ⟨261345580062358807488818317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348460773416478409985091089 261345580062358807488818317)
        ·
          refine ⟨98004592523384552808306869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261345580062358807488818317 98004592523384552808306869)
          ·
            refine ⟨9187930549067301825778769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98004592523384552808306869 9187930549067301825778769)
            ·
              refine ⟨6890947911800476369334077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9187930549067301825778769 6890947911800476369334077)
              ·
                refine ⟨2584105466925178638500279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6890947911800476369334077 2584105466925178638500279)
                ·
                  refine ⟨3876158200387767957750419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584105466925178638500279 3876158200387767957750419)
                  ·
                    refine ⟨5814237300581651936625629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876158200387767957750419 5814237300581651936625629)
                    ·
                      refine ⟨2180338987718119476234611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5814237300581651936625629 2180338987718119476234611)
                      ·
                        rfl

theorem cell23_4246195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 1, 3].length) (baseStart_4246195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246195 prefixEnd_4246195 := by exact prefixLift 4246195
  have htrace : WordTrace (prefixWord ++ tailWord_4246195) baseStart_4246195 baseEnd_4246195 := by
    simpa [prefixWord, tailWord_4246195, baseEnd_4246195] using wordTrace_append hprefix tailTrace_4246195
  have hstable : (prefixWord ++ tailWord_4246195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246195).length < 2 ^ (prefixWord ++ tailWord_4246195).sum := by decide
  have hdescent : baseEnd_4246195 < baseStart_4246195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246231 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_4246231 : Nat := 118140960795 + 4246231 * 2 ^ 59
def prefixEnd_4246231 : Nat := 4983230072969 + 3 ^ 40 * 4246231 * 2
def baseEnd_4246231 : Nat := 2180357473021681335384445

theorem tailTrace_4246231 : CollatzResearch.WordTrace tailWord_4246231 prefixEnd_4246231 2180357473021681335384445 := by
  unfold tailWord_4246231
  simp only [CollatzResearch.WordTrace]
  refine ⟨154872767879637760363906547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103248511919758506909271031 154872767879637760363906547)
  ·
    refine ⟨232309151819456640545859821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154872767879637760363906547 232309151819456640545859821)
    ·
      refine ⟨87115931932296240204697433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232309151819456640545859821 87115931932296240204697433)
      ·
        refine ⟨65336948949222180153523075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87115931932296240204697433 65336948949222180153523075)
        ·
          refine ⟨98005423423833270230284613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65336948949222180153523075 98005423423833270230284613)
          ·
            refine ⟨18376016891968738168178365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98005423423833270230284613 18376016891968738168178365)
            ·
              refine ⟨6891006334488276813066887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18376016891968738168178365 6891006334488276813066887)
              ·
                refine ⟨10336509501732415219600331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891006334488276813066887 10336509501732415219600331)
                ·
                  refine ⟨15504764252598622829400497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10336509501732415219600331 15504764252598622829400497)
                  ·
                    refine ⟨11628573189448967122050373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15504764252598622829400497 11628573189448967122050373)
                    ·
                      refine ⟨2180357473021681335384445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11628573189448967122050373 2180357473021681335384445)
                      ·
                        rfl

theorem cell23_4246231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_4246231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246231 prefixEnd_4246231 := by exact prefixLift 4246231
  have htrace : WordTrace (prefixWord ++ tailWord_4246231) baseStart_4246231 baseEnd_4246231 := by
    simpa [prefixWord, tailWord_4246231, baseEnd_4246231] using wordTrace_append hprefix tailTrace_4246231
  have hstable : (prefixWord ++ tailWord_4246231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246231).length < 2 ^ (prefixWord ++ tailWord_4246231).sum := by decide
  have hdescent : baseEnd_4246231 < baseStart_4246231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246241 : List Nat := [1, 2, 3, 1, 4, 1, 4, 7]
def baseStart_4246241 : Nat := 118140960795 + 4246241 * 2 ^ 59
def prefixEnd_4246241 : Nat := 4983230072969 + 3 ^ 40 * 4246241 * 2
def baseEnd_4246241 : Nat := 80754170660304677639237

theorem tailTrace_4246241 : CollatzResearch.WordTrace tailWord_4246241 prefixEnd_4246241 80754170660304677639237 := by
  unfold tailWord_4246241
  simp only [CollatzResearch.WordTrace]
  refine ⟨154873132609601532071770577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103248755073067688047847051 154873132609601532071770577)
  ·
    refine ⟨116154849457201149053827933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154873132609601532071770577 116154849457201149053827933)
    ·
      refine ⟨43558068546450430895185475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116154849457201149053827933 43558068546450430895185475)
      ·
        refine ⟨65337102819675646342778213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43558068546450430895185475 65337102819675646342778213)
        ·
          refine ⟨12250706778689183689270915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65337102819675646342778213 12250706778689183689270915)
          ·
            refine ⟨18376060168033775533906373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12250706778689183689270915 18376060168033775533906373)
            ·
              refine ⟨3445511281506332912607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18376060168033775533906373 3445511281506332912607445)
              ·
                refine ⟨80754170660304677639237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3445511281506332912607445 80754170660304677639237)
                ·
                  rfl

theorem cell23_4246241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 7].length) (baseStart_4246241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246241 prefixEnd_4246241 := by exact prefixLift 4246241
  have htrace : WordTrace (prefixWord ++ tailWord_4246241) baseStart_4246241 baseEnd_4246241 := by
    simpa [prefixWord, tailWord_4246241, baseEnd_4246241] using wordTrace_append hprefix tailTrace_4246241
  have hstable : (prefixWord ++ tailWord_4246241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246241).length < 2 ^ (prefixWord ++ tailWord_4246241).sum := by decide
  have hdescent : baseEnd_4246241 < baseStart_4246241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246264 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_4246264 : Nat := 118140960795 + 4246264 * 2 ^ 59
def prefixEnd_4246264 : Nat := 4983230072969 + 3 ^ 40 * 4246264 * 2
def baseEnd_4246264 : Nat := 2180374417883279706271793

theorem tailTrace_4246264 : CollatzResearch.WordTrace tailWord_4246264 prefixEnd_4246264 2180374417883279706271793 := by
  unfold tailWord_4246264
  simp only [CollatzResearch.WordTrace]
  refine ⟨77436985744259103499928923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103249314325678804666571897 77436985744259103499928923)
  ·
    refine ⟨116155478616388655249893385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77436985744259103499928923 116155478616388655249893385)
    ·
      refine ⟨87116608962291491437420039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116155478616388655249893385 87116608962291491437420039)
      ·
        refine ⟨130674913443437237156130059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87116608962291491437420039 130674913443437237156130059)
        ·
          refine ⟨196012370165155855734195089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130674913443437237156130059 196012370165155855734195089)
          ·
            refine ⟨147009277623866891800646317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196012370165155855734195089 147009277623866891800646317)
            ·
              refine ⟨55128479108950084425242369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147009277623866891800646317 55128479108950084425242369)
              ·
                refine ⟨41346359331712563318931777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55128479108950084425242369 41346359331712563318931777)
                ·
                  refine ⟨31009769498784422489198833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41346359331712563318931777 31009769498784422489198833)
                  ·
                    refine ⟨23257327124088316866899125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31009769498784422489198833 23257327124088316866899125)
                    ·
                      refine ⟨2180374417883279706271793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23257327124088316866899125 2180374417883279706271793)
                      ·
                        rfl

theorem cell23_4246264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_4246264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246264 prefixEnd_4246264 := by exact prefixLift 4246264
  have htrace : WordTrace (prefixWord ++ tailWord_4246264) baseStart_4246264 baseEnd_4246264 := by
    simpa [prefixWord, tailWord_4246264, baseEnd_4246264] using wordTrace_append hprefix tailTrace_4246264
  have hstable : (prefixWord ++ tailWord_4246264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246264).length < 2 ^ (prefixWord ++ tailWord_4246264).sum := by decide
  have hdescent : baseEnd_4246264 < baseStart_4246264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246268 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_4246268 : Nat := 118140960795 + 4246268 * 2 ^ 59
def prefixEnd_4246268 : Nat := 4983230072969 + 3 ^ 40 * 4246268 * 2
def baseEnd_4246268 : Nat := 2180376471805897690621775

theorem tailTrace_4246268 : CollatzResearch.WordTrace tailWord_4246268 prefixEnd_4246268 2180376471805897690621775 := by
  unfold tailWord_4246268
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437058690251857841501729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103249411587002477122002305 77437058690251857841501729)
  ·
    refine ⟨58077794017688893381126297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77437058690251857841501729 58077794017688893381126297)
    ·
      refine ⟨43558345513266670035844723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58077794017688893381126297 43558345513266670035844723)
      ·
        refine ⟨65337518269900005053767085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43558345513266670035844723 65337518269900005053767085)
        ·
          refine ⟨24501569351212501895162657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65337518269900005053767085 24501569351212501895162657)
          ·
            refine ⟨18376177013409376421371993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24501569351212501895162657 18376177013409376421371993)
            ·
              refine ⟨13782132760057032316028995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18376177013409376421371993 13782132760057032316028995)
              ·
                refine ⟨20673199140085548474043493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13782132760057032316028995 20673199140085548474043493)
                ·
                  refine ⟨3876224838766040338883155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20673199140085548474043493 3876224838766040338883155)
                  ·
                    refine ⟨5814337258149060508324733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876224838766040338883155 5814337258149060508324733)
                    ·
                      refine ⟨2180376471805897690621775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5814337258149060508324733 2180376471805897690621775)
                      ·
                        rfl

theorem cell23_4246268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_4246268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246268 prefixEnd_4246268 := by exact prefixLift 4246268
  have htrace : WordTrace (prefixWord ++ tailWord_4246268) baseStart_4246268 baseEnd_4246268 := by
    simpa [prefixWord, tailWord_4246268, baseEnd_4246268] using wordTrace_append hprefix tailTrace_4246268
  have hstable : (prefixWord ++ tailWord_4246268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246268).length < 2 ^ (prefixWord ++ tailWord_4246268).sum := by decide
  have hdescent : baseEnd_4246268 < baseStart_4246268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246284 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_4246284 : Nat := 118140960795 + 4246284 * 2 ^ 59
def prefixEnd_4246284 : Nat := 4983230072969 + 3 ^ 40 * 4246284 * 2
def baseEnd_4246284 : Nat := 726794895832123209340567

theorem tailTrace_4246284 : CollatzResearch.WordTrace tailWord_4246284 prefixEnd_4246284 726794895832123209340567 := by
  unfold tailWord_4246284
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437350474222875207792953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103249800632297166943723937 77437350474222875207792953)
  ·
    refine ⟨58078012855667156405844715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77437350474222875207792953 58078012855667156405844715)
    ·
      refine ⟨87117019283500734608767073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58078012855667156405844715 87117019283500734608767073)
      ·
        refine ⟨65337764462625550956575305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87117019283500734608767073 65337764462625550956575305)
        ·
          refine ⟨49003323346969163217431479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65337764462625550956575305 49003323346969163217431479)
          ·
            refine ⟨73504985020453744826147219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49003323346969163217431479 73504985020453744826147219)
            ·
              refine ⟨110257477530680617239220829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73504985020453744826147219 110257477530680617239220829)
              ·
                refine ⟨41346554074005231464707811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110257477530680617239220829 41346554074005231464707811)
                ·
                  refine ⟨62019831111007847197061717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41346554074005231464707811 62019831111007847197061717)
                  ·
                    refine ⟨726794895832123209340567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62019831111007847197061717 726794895832123209340567)
                    ·
                      rfl

theorem cell23_4246284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_4246284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246284 prefixEnd_4246284 := by exact prefixLift 4246284
  have htrace : WordTrace (prefixWord ++ tailWord_4246284) baseStart_4246284 baseEnd_4246284 := by
    simpa [prefixWord, tailWord_4246284, baseEnd_4246284] using wordTrace_append hprefix tailTrace_4246284
  have hstable : (prefixWord ++ tailWord_4246284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246284).length < 2 ^ (prefixWord ++ tailWord_4246284).sum := by decide
  have hdescent : baseEnd_4246284 < baseStart_4246284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246295 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4246295 : Nat := 118140960795 + 4246295 * 2 ^ 59
def prefixEnd_4246295 : Nat := 4983230072969 + 3 ^ 40 * 4246295 * 2
def baseEnd_4246295 : Nat := 2180390335783569084984151

theorem tailTrace_4246295 : CollatzResearch.WordTrace tailWord_4246295 prefixEnd_4246295 2180390335783569084984151 := by
  unfold tailWord_4246295
  simp only [CollatzResearch.WordTrace]
  refine ⟨154875102151405899294236339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103250068100937266196157559 154875102151405899294236339)
  ·
    refine ⟨232312653227108848941354509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154875102151405899294236339 232312653227108848941354509)
    ·
      refine ⟨87117244960165818353007941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232312653227108848941354509 87117244960165818353007941)
      ·
        refine ⟨16334483430031090941188989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87117244960165818353007941 16334483430031090941188989)
        ·
          refine ⟨6125431286261659102945871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16334483430031090941188989 6125431286261659102945871)
          ·
            refine ⟨9188146929392488654418807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6125431286261659102945871 9188146929392488654418807)
            ·
              refine ⟨13782220394088732981628211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9188146929392488654418807 13782220394088732981628211)
              ·
                refine ⟨20673330591133099472442317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13782220394088732981628211 20673330591133099472442317)
                ·
                  refine ⟨7752498971674912302165869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20673330591133099472442317 7752498971674912302165869)
                  ·
                    refine ⟨2907187114378092113312201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7752498971674912302165869 2907187114378092113312201)
                    ·
                      refine ⟨2180390335783569084984151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907187114378092113312201 2180390335783569084984151)
                      ·
                        rfl

theorem cell23_4246295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4246295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246295 prefixEnd_4246295 := by exact prefixLift 4246295
  have htrace : WordTrace (prefixWord ++ tailWord_4246295) baseStart_4246295 baseEnd_4246295 := by
    simpa [prefixWord, tailWord_4246295, baseEnd_4246295] using wordTrace_append hprefix tailTrace_4246295
  have hstable : (prefixWord ++ tailWord_4246295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246295).length < 2 ^ (prefixWord ++ tailWord_4246295).sum := by decide
  have hdescent : baseEnd_4246295 < baseStart_4246295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246312 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_4246312 : Nat := 118140960795 + 4246312 * 2 ^ 59
def prefixEnd_4246312 : Nat := 4983230072969 + 3 ^ 40 * 4246312 * 2
def baseEnd_4246312 : Nat := 2180399064954695518471573

theorem tailTrace_4246312 : CollatzResearch.WordTrace tailWord_4246312 prefixEnd_4246312 2180399064954695518471573 := by
  unfold tailWord_4246312
  simp only [CollatzResearch.WordTrace]
  refine ⟨77437861096172155598802595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103250481461562874131736793 77437861096172155598802595)
  ·
    refine ⟨116156791644258233398203893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77437861096172155598802595 116156791644258233398203893)
    ·
      refine ⟨10889699216649209381081615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116156791644258233398203893 10889699216649209381081615)
      ·
        refine ⟨16334548824973814071622423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10889699216649209381081615 16334548824973814071622423)
        ·
          refine ⟨24501823237460721107433635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16334548824973814071622423 24501823237460721107433635)
          ·
            refine ⟨36752734856191081661150453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24501823237460721107433635 36752734856191081661150453)
            ·
              refine ⟨3445568892767913905732855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36752734856191081661150453 3445568892767913905732855)
              ·
                refine ⟨5168353339151870858599283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445568892767913905732855 5168353339151870858599283)
                ·
                  refine ⟨7752530008727806287898925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168353339151870858599283 7752530008727806287898925)
                  ·
                    refine ⟨2907198753272927357962097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7752530008727806287898925 2907198753272927357962097)
                    ·
                      refine ⟨2180399064954695518471573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907198753272927357962097 2180399064954695518471573)
                      ·
                        rfl

theorem cell23_4246312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_4246312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246312 prefixEnd_4246312 := by exact prefixLift 4246312
  have htrace : WordTrace (prefixWord ++ tailWord_4246312) baseStart_4246312 baseEnd_4246312 := by
    simpa [prefixWord, tailWord_4246312, baseEnd_4246312] using wordTrace_append hprefix tailTrace_4246312
  have hstable : (prefixWord ++ tailWord_4246312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246312).length < 2 ^ (prefixWord ++ tailWord_4246312).sum := by decide
  have hdescent : baseEnd_4246312 < baseStart_4246312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246321 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_4246321 : Nat := 118140960795 + 4246321 * 2 ^ 59
def prefixEnd_4246321 : Nat := 4983230072969 + 3 ^ 40 * 4246321 * 2
def baseEnd_4246321 : Nat := 2180403686280585983259031

theorem tailTrace_4246321 : CollatzResearch.WordTrace tailWord_4246321 prefixEnd_4246321 2180403686280585983259031 := by
  unfold tailWord_4246321
  simp only [CollatzResearch.WordTrace]
  refine ⟨154876050449311705734682817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103250700299541137156455211 154876050449311705734682817)
  ·
    refine ⟨116157037836983779301012113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154876050449311705734682817 116157037836983779301012113)
    ·
      refine ⟨87117778377737834475759085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116157037836983779301012113 87117778377737834475759085)
      ·
        refine ⟨32669166891651687928409657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87117778377737834475759085 32669166891651687928409657)
        ·
          refine ⟨24501875168738765946307243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32669166891651687928409657 24501875168738765946307243)
          ·
            refine ⟨36752812753108148919460865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24501875168738765946307243 36752812753108148919460865)
            ·
              refine ⟨27564609564831111689595649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36752812753108148919460865 27564609564831111689595649)
              ·
                refine ⟨20673457173623333767196737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27564609564831111689595649 20673457173623333767196737)
                ·
                  refine ⟨15505092880217500325397553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20673457173623333767196737 15505092880217500325397553)
                  ·
                    refine ⟨11628819660163125244048165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15505092880217500325397553 11628819660163125244048165)
                    ·
                      refine ⟨2180403686280585983259031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11628819660163125244048165 2180403686280585983259031)
                      ·
                        rfl

theorem cell23_4246321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_4246321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246321 prefixEnd_4246321 := by exact prefixLift 4246321
  have htrace : WordTrace (prefixWord ++ tailWord_4246321) baseStart_4246321 baseEnd_4246321 := by
    simpa [prefixWord, tailWord_4246321, baseEnd_4246321] using wordTrace_append hprefix tailTrace_4246321
  have hstable : (prefixWord ++ tailWord_4246321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246321).length < 2 ^ (prefixWord ++ tailWord_4246321).sum := by decide
  have hdescent : baseEnd_4246321 < baseStart_4246321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246361 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_4246361 : Nat := 118140960795 + 4246361 * 2 ^ 59
def prefixEnd_4246361 : Nat := 4983230072969 + 3 ^ 40 * 4246361 * 2
def baseEnd_4246361 : Nat := 726808075168921942252949

theorem tailTrace_4246361 : CollatzResearch.WordTrace tailWord_4246361 prefixEnd_4246361 726808075168921942252949 := by
  unfold tailWord_4246361
  simp only [CollatzResearch.WordTrace]
  refine ⟨154877509369166792566138937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103251672912777861710759291 154877509369166792566138937)
  ·
    refine ⟨116158132026875094424604203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154877509369166792566138937 116158132026875094424604203)
    ·
      refine ⟨174237198040312641636906305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116158132026875094424604203 174237198040312641636906305)
      ·
        refine ⟨130677898530234481227679729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174237198040312641636906305 130677898530234481227679729)
        ·
          refine ⟨98008423897675860920759797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130677898530234481227679729 98008423897675860920759797)
          ·
            refine ⟨9188289740407111961321231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98008423897675860920759797 9188289740407111961321231)
            ·
              refine ⟨13782434610610667941981847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9188289740407111961321231 13782434610610667941981847)
              ·
                refine ⟨20673651915916001912972771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13782434610610667941981847 20673651915916001912972771)
                ·
                  refine ⟨31010477873874002869459157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20673651915916001912972771 31010477873874002869459157)
                  ·
                    refine ⟨726808075168921942252949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31010477873874002869459157 726808075168921942252949)
                    ·
                      rfl

theorem cell23_4246361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_4246361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246361 prefixEnd_4246361 := by exact prefixLift 4246361
  have htrace : WordTrace (prefixWord ++ tailWord_4246361) baseStart_4246361 baseEnd_4246361 := by
    simpa [prefixWord, tailWord_4246361, baseEnd_4246361] using wordTrace_append hprefix tailTrace_4246361
  have hstable : (prefixWord ++ tailWord_4246361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246361).length < 2 ^ (prefixWord ++ tailWord_4246361).sum := by decide
  have hdescent : baseEnd_4246361 < baseStart_4246361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246421 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 8]
def baseStart_4246421 : Nat := 118140960795 + 4246421 * 2 ^ 59
def prefixEnd_4246421 : Nat := 4983230072969 + 3 ^ 40 * 4246421 * 2
def baseEnd_4246421 : Nat := 242272781594003954667619

theorem tailTrace_4246421 : CollatzResearch.WordTrace tailWord_4246421 prefixEnd_4246421 242272781594003954667619 := by
  unfold tailWord_4246421
  simp only [CollatzResearch.WordTrace]
  refine ⟨154879697748949422813323117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103253131832632948542215411 154879697748949422813323117)
  ·
    refine ⟨58079886655856033554996169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154879697748949422813323117 58079886655856033554996169)
    ·
      refine ⟨43559914991892025166247127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58079886655856033554996169 43559914991892025166247127)
      ·
        refine ⟨65339872487838037749370691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43559914991892025166247127 65339872487838037749370691)
        ·
          refine ⟨98009808731757056624056037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65339872487838037749370691 98009808731757056624056037)
          ·
            refine ⟨18376839137204448117010507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98009808731757056624056037 18376839137204448117010507)
            ·
              refine ⟨27565258705806672175515761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18376839137204448117010507 27565258705806672175515761)
              ·
                refine ⟨20673944029355004131636821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27565258705806672175515761 20673944029355004131636821)
                ·
                  refine ⟨242272781594003954667619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20673944029355004131636821 242272781594003954667619)
                  ·
                    rfl

theorem cell23_4246421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_4246421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246421 prefixEnd_4246421 := by exact prefixLift 4246421
  have htrace : WordTrace (prefixWord ++ tailWord_4246421) baseStart_4246421 baseEnd_4246421 := by
    simpa [prefixWord, tailWord_4246421, baseEnd_4246421] using wordTrace_append hprefix tailTrace_4246421
  have hstable : (prefixWord ++ tailWord_4246421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246421).length < 2 ^ (prefixWord ++ tailWord_4246421).sum := by decide
  have hdescent : baseEnd_4246421 < baseStart_4246421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246475 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 2, 3, 2]
def baseStart_4246475 : Nat := 118140960795 + 4246475 * 2 ^ 59
def prefixEnd_4246475 : Nat := 4983230072969 + 3 ^ 40 * 4246475 * 2
def baseEnd_4246475 : Nat := 2180482762301378380733323

theorem tailTrace_4246475 : CollatzResearch.WordTrace tailWord_4246475 prefixEnd_4246475 2180482762301378380733323 := by
  unfold tailWord_4246475
  simp only [CollatzResearch.WordTrace]
  refine ⟨154881667290753790035788879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103254444860502526690525919 154881667290753790035788879)
  ·
    refine ⟨232322500936130685053683319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154881667290753790035788879 232322500936130685053683319)
    ·
      refine ⟨348483751404196027580524979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232322500936130685053683319 348483751404196027580524979)
      ·
        refine ⟨522725627106294041370787469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348483751404196027580524979 522725627106294041370787469)
        ·
          refine ⟨196022110164860265514045301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 522725627106294041370787469 196022110164860265514045301)
          ·
            refine ⟨18377072827955649891941747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196022110164860265514045301 18377072827955649891941747)
            ·
              refine ⟨27565609241933474837912621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18377072827955649891941747 27565609241933474837912621)
              ·
                refine ⟨10337103465725053064217233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27565609241933474837912621 10337103465725053064217233)
                ·
                  refine ⟨7752827599293789798162925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10337103465725053064217233 7752827599293789798162925)
                  ·
                    refine ⟨2907310349735171174311097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7752827599293789798162925 2907310349735171174311097)
                    ·
                      refine ⟨2180482762301378380733323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907310349735171174311097 2180482762301378380733323)
                      ·
                        rfl

theorem cell23_4246475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3, 2].length) (baseStart_4246475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246475 prefixEnd_4246475 := by exact prefixLift 4246475
  have htrace : WordTrace (prefixWord ++ tailWord_4246475) baseStart_4246475 baseEnd_4246475 := by
    simpa [prefixWord, tailWord_4246475, baseEnd_4246475] using wordTrace_append hprefix tailTrace_4246475
  have hstable : (prefixWord ++ tailWord_4246475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246475).length < 2 ^ (prefixWord ++ tailWord_4246475).sum := by decide
  have hdescent : baseEnd_4246475 < baseStart_4246475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246505 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 9, 2, 2]
def baseStart_4246505 : Nat := 118140960795 + 4246505 * 2 ^ 59
def prefixEnd_4246505 : Nat := 4983230072969 + 3 ^ 40 * 4246505 * 2
def baseEnd_4246505 : Nat := 2180498166721013263358185

theorem tailTrace_4246505 : CollatzResearch.WordTrace tailWord_4246505 prefixEnd_4246505 2180498166721013263358185 := by
  unfold tailWord_4246505
  simp only [CollatzResearch.WordTrace]
  refine ⟨154882761480645105159380969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103255174320430070106253979 154882761480645105159380969)
  ·
    refine ⟨116162071110483828869535727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154882761480645105159380969 116162071110483828869535727)
    ·
      refine ⟨174243106665725743304303591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116162071110483828869535727 174243106665725743304303591)
      ·
        refine ⟨261364659998588614956455387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174243106665725743304303591 261364659998588614956455387)
        ·
          refine ⟨392046989997882922434683081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261364659998588614956455387 392046989997882922434683081)
          ·
            refine ⟨294035242498412191826012311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392046989997882922434683081 294035242498412191826012311)
            ·
              refine ⟨441052863747618287739018467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294035242498412191826012311 441052863747618287739018467)
              ·
                refine ⟨661579295621427431608527701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441052863747618287739018467 661579295621427431608527701)
                ·
                  refine ⟨3876441185281801357081217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 661579295621427431608527701 3876441185281801357081217)
                  ·
                    refine ⟨2907330888961351017810913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3876441185281801357081217 2907330888961351017810913)
                    ·
                      refine ⟨2180498166721013263358185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907330888961351017810913 2180498166721013263358185)
                      ·
                        rfl

theorem cell23_4246505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2, 2].length) (baseStart_4246505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246505 prefixEnd_4246505 := by exact prefixLift 4246505
  have htrace : WordTrace (prefixWord ++ tailWord_4246505) baseStart_4246505 baseEnd_4246505 := by
    simpa [prefixWord, tailWord_4246505, baseEnd_4246505] using wordTrace_append hprefix tailTrace_4246505
  have hstable : (prefixWord ++ tailWord_4246505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246505).length < 2 ^ (prefixWord ++ tailWord_4246505).sum := by decide
  have hdescent : baseEnd_4246505 < baseStart_4246505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246525 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_4246525 : Nat := 118140960795 + 4246525 * 2 ^ 59
def prefixEnd_4246525 : Nat := 4983230072969 + 3 ^ 40 * 4246525 * 2
def baseEnd_4246525 : Nat := 2180508436334103185108093

theorem tailTrace_4246525 : CollatzResearch.WordTrace tailWord_4246525 prefixEnd_4246525 2180508436334103185108093 := by
  unfold tailWord_4246525
  simp only [CollatzResearch.WordTrace]
  refine ⟨154883490940572648575109029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103255660627048432383406019 154883490940572648575109029)
  ·
    refine ⟨29040654551357371607832943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154883490940572648575109029 29040654551357371607832943)
    ·
      refine ⟨43560981827036057411749415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29040654551357371607832943 43560981827036057411749415)
      ·
        refine ⟨65341472740554086117624123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43560981827036057411749415 65341472740554086117624123)
        ·
          refine ⟨98012209110831129176436185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65341472740554086117624123 98012209110831129176436185)
          ·
            refine ⟨73509156833123346882327139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98012209110831129176436185 73509156833123346882327139)
            ·
              refine ⟨110263735249685020323490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73509156833123346882327139 110263735249685020323490709)
              ·
                refine ⟨5168612589828985327663627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110263735249685020323490709 5168612589828985327663627)
                ·
                  refine ⟨7752918884743477991495441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168612589828985327663627 7752918884743477991495441)
                  ·
                    refine ⟨5814689163557608493621581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7752918884743477991495441 5814689163557608493621581)
                    ·
                      refine ⟨2180508436334103185108093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5814689163557608493621581 2180508436334103185108093)
                      ·
                        rfl

theorem cell23_4246525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_4246525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246525 prefixEnd_4246525 := by exact prefixLift 4246525
  have htrace : WordTrace (prefixWord ++ tailWord_4246525) baseStart_4246525 baseEnd_4246525 := by
    simpa [prefixWord, tailWord_4246525, baseEnd_4246525] using wordTrace_append hprefix tailTrace_4246525
  have hstable : (prefixWord ++ tailWord_4246525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246525).length < 2 ^ (prefixWord ++ tailWord_4246525).sum := by decide
  have hdescent : baseEnd_4246525 < baseStart_4246525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246526 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4246526 : Nat := 118140960795 + 4246526 * 2 ^ 59
def prefixEnd_4246526 : Nat := 4983230072969 + 3 ^ 40 * 4246526 * 2
def baseEnd_4246526 : Nat := 2180508949814757681195589

theorem tailTrace_4246526 : CollatzResearch.WordTrace tailWord_4246526 prefixEnd_4246526 2180508949814757681195589 := by
  unfold tailWord_4246526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19360440926696128218236929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103255684942379350497263621 19360440926696128218236929)
  ·
    refine ⟨14520330695022096163677697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19360440926696128218236929 14520330695022096163677697)
    ·
      refine ⟨10890248021266572122758273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14520330695022096163677697 10890248021266572122758273)
      ·
        refine ⟨8167686015949929092068705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10890248021266572122758273 8167686015949929092068705)
        ·
          refine ⟨6125764511962446819051529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8167686015949929092068705 6125764511962446819051529)
          ·
            refine ⟨4594323383971835114288647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6125764511962446819051529 4594323383971835114288647)
            ·
              refine ⟨6891485075957752671432971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594323383971835114288647 6891485075957752671432971)
              ·
                refine ⟨10337227613936629007149457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891485075957752671432971 10337227613936629007149457)
                ·
                  refine ⟨7752920710452471755362093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10337227613936629007149457 7752920710452471755362093)
                  ·
                    refine ⟨2907345266419676908260785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7752920710452471755362093 2907345266419676908260785)
                    ·
                      refine ⟨2180508949814757681195589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907345266419676908260785 2180508949814757681195589)
                      ·
                        rfl

theorem cell23_4246526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4246526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246526 prefixEnd_4246526 := by exact prefixLift 4246526
  have htrace : WordTrace (prefixWord ++ tailWord_4246526) baseStart_4246526 baseEnd_4246526 := by
    simpa [prefixWord, tailWord_4246526, baseEnd_4246526] using wordTrace_append hprefix tailTrace_4246526
  have hstable : (prefixWord ++ tailWord_4246526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246526).length < 2 ^ (prefixWord ++ tailWord_4246526).sum := by decide
  have hdescent : baseEnd_4246526 < baseStart_4246526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246539 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 1, 2, 2]
def baseStart_4246539 : Nat := 118140960795 + 4246539 * 2 ^ 59
def prefixEnd_4246539 : Nat := 4983230072969 + 3 ^ 40 * 4246539 * 2
def baseEnd_4246539 : Nat := 2180515625063266130333029

theorem tailTrace_4246539 : CollatzResearch.WordTrace tailWord_4246539 prefixEnd_4246539 2180515625063266130333029 := by
  unfold tailWord_4246539
  simp only [CollatzResearch.WordTrace]
  refine ⟨154884001562521928966118671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103256001041681285977412447 154884001562521928966118671)
  ·
    refine ⟨232326002343782893449178007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154884001562521928966118671 232326002343782893449178007)
    ·
      refine ⟨348489003515674340173767011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232326002343782893449178007 348489003515674340173767011)
      ·
        refine ⟨522733505273511510260650517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348489003515674340173767011 522733505273511510260650517)
        ·
          refine ⟨24503133059695852043467993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 522733505273511510260650517 24503133059695852043467993)
          ·
            refine ⟨18377349794771889032600995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24503133059695852043467993 18377349794771889032600995)
            ·
              refine ⟨27566024692157833548901493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18377349794771889032600995 27566024692157833548901493)
              ·
                refine ⟨2584314814889796895209515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27566024692157833548901493 2584314814889796895209515)
                ·
                  refine ⟨3876472222334695342814273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584314814889796895209515 3876472222334695342814273)
                  ·
                    refine ⟨2907354166751021507110705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3876472222334695342814273 2907354166751021507110705)
                    ·
                      refine ⟨2180515625063266130333029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907354166751021507110705 2180515625063266130333029)
                      ·
                        rfl

theorem cell23_4246539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 2, 2].length) (baseStart_4246539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246539 prefixEnd_4246539 := by exact prefixLift 4246539
  have htrace : WordTrace (prefixWord ++ tailWord_4246539) baseStart_4246539 baseEnd_4246539 := by
    simpa [prefixWord, tailWord_4246539, baseEnd_4246539] using wordTrace_append hprefix tailTrace_4246539
  have hstable : (prefixWord ++ tailWord_4246539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246539).length < 2 ^ (prefixWord ++ tailWord_4246539).sum := by decide
  have hdescent : baseEnd_4246539 < baseStart_4246539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246542 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4246542 : Nat := 118140960795 + 4246542 * 2 ^ 59
def prefixEnd_4246542 : Nat := 4983230072969 + 3 ^ 40 * 4246542 * 2
def baseEnd_4246542 : Nat := 2180517165505229618595515

theorem tailTrace_4246542 : CollatzResearch.WordTrace tailWord_4246542 prefixEnd_4246542 2180517165505229618595515 := by
  unfold tailWord_4246542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19360513872688882559809735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103256073987674040318985253 19360513872688882559809735)
  ·
    refine ⟨29040770809033323839714603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19360513872688882559809735 29040770809033323839714603)
    ·
      refine ⟨43561156213549985759571905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29040770809033323839714603 43561156213549985759571905)
      ·
        refine ⟨32670867160162489319678929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43561156213549985759571905 32670867160162489319678929)
        ·
          refine ⟨24503150370121866989759197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32670867160162489319678929 24503150370121866989759197)
          ·
            refine ⟨9188681388795700121159699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24503150370121866989759197 9188681388795700121159699)
            ·
              refine ⟨13783022083193550181739549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9188681388795700121159699 13783022083193550181739549)
              ·
                refine ⟨5168633281197581318152331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13783022083193550181739549 5168633281197581318152331)
                ·
                  refine ⟨7752949921796371977228497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5168633281197581318152331 7752949921796371977228497)
                  ·
                    refine ⟨5814712441347278982921373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7752949921796371977228497 5814712441347278982921373)
                    ·
                      refine ⟨2180517165505229618595515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5814712441347278982921373 2180517165505229618595515)
                      ·
                        rfl

theorem cell23_4246542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4246542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246542 prefixEnd_4246542 := by exact prefixLift 4246542
  have htrace : WordTrace (prefixWord ++ tailWord_4246542) baseStart_4246542 baseEnd_4246542 := by
    simpa [prefixWord, tailWord_4246542, baseEnd_4246542] using wordTrace_append hprefix tailTrace_4246542
  have hstable : (prefixWord ++ tailWord_4246542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246542).length < 2 ^ (prefixWord ++ tailWord_4246542).sum := by decide
  have hdescent : baseEnd_4246542 < baseStart_4246542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246595 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 4, 2]
def baseStart_4246595 : Nat := 118140960795 + 4246595 * 2 ^ 59
def prefixEnd_4246595 : Nat := 4983230072969 + 3 ^ 40 * 4246595 * 2
def baseEnd_4246595 : Nat := 2180544379979917911232771

theorem tailTrace_4246595 : CollatzResearch.WordTrace tailWord_4246595 prefixEnd_4246595 2180544379979917911232771 := by
  unfold tailWord_4246595
  simp only [CollatzResearch.WordTrace]
  refine ⟨154886044050319050530157239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103257362700212700353438159 154886044050319050530157239)
  ·
    refine ⟨232329066075478575795235859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154886044050319050530157239 232329066075478575795235859)
    ·
      refine ⟨348493599113217863692853789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232329066075478575795235859 348493599113217863692853789)
      ·
        refine ⟨130685099667456698884820171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348493599113217863692853789 130685099667456698884820171)
        ·
          refine ⟨196027649501185048327230257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130685099667456698884820171 196027649501185048327230257)
          ·
            refine ⟨147020737125888786245422693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196027649501185048327230257 147020737125888786245422693)
            ·
              refine ⟨27566388211104147421016755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147020737125888786245422693 27566388211104147421016755)
              ·
                refine ⟨41349582316656221131525133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27566388211104147421016755 41349582316656221131525133)
                ·
                  refine ⟨15506093368746082924321925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41349582316656221131525133 15506093368746082924321925)
                  ·
                    refine ⟨2907392506639890548310361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15506093368746082924321925 2907392506639890548310361)
                    ·
                      refine ⟨2180544379979917911232771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907392506639890548310361 2180544379979917911232771)
                      ·
                        rfl

theorem cell23_4246595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_4246595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246595 prefixEnd_4246595 := by exact prefixLift 4246595
  have htrace : WordTrace (prefixWord ++ tailWord_4246595) baseStart_4246595 baseEnd_4246595 := by
    simpa [prefixWord, tailWord_4246595, baseEnd_4246595] using wordTrace_append hprefix tailTrace_4246595
  have hstable : (prefixWord ++ tailWord_4246595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246595).length < 2 ^ (prefixWord ++ tailWord_4246595).sum := by decide
  have hdescent : baseEnd_4246595 < baseStart_4246595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246608 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_4246608 : Nat := 118140960795 + 4246608 * 2 ^ 59
def prefixEnd_4246608 : Nat := 4983230072969 + 3 ^ 40 * 4246608 * 2
def baseEnd_4246608 : Nat := 2180551055228426360370211

theorem tailTrace_4246608 : CollatzResearch.WordTrace tailWord_4246608 prefixEnd_4246608 2180551055228426360370211 := by
  unfold tailWord_4246608
  simp only [CollatzResearch.WordTrace]
  refine ⟨77443259099635976875190239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103257678799514635833586985 77443259099635976875190239)
  ·
    refine ⟨116164888649453965312785359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77443259099635976875190239 116164888649453965312785359)
    ·
      refine ⟨174247332974180947969178039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116164888649453965312785359 174247332974180947969178039)
      ·
        refine ⟨261370999461271421953767059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174247332974180947969178039 261370999461271421953767059)
        ·
          refine ⟨392056499191907132930650589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261370999461271421953767059 392056499191907132930650589)
          ·
            refine ⟨147021187196965174848993971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392056499191907132930650589 147021187196965174848993971)
            ·
              refine ⟨220531780795447762273490957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147021187196965174848993971 220531780795447762273490957)
              ·
                refine ⟨82699417798292910852559109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220531780795447762273490957 82699417798292910852559109)
                ·
                  refine ⟨15506140837179920784854833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82699417798292910852559109 15506140837179920784854833)
                  ·
                    refine ⟨11629605627884940588641125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15506140837179920784854833 11629605627884940588641125)
                    ·
                      refine ⟨2180551055228426360370211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11629605627884940588641125 2180551055228426360370211)
                      ·
                        rfl

theorem cell23_4246608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_4246608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246608 prefixEnd_4246608 := by exact prefixLift 4246608
  have htrace : WordTrace (prefixWord ++ tailWord_4246608) baseStart_4246608 baseEnd_4246608 := by
    simpa [prefixWord, tailWord_4246608, baseEnd_4246608] using wordTrace_append hprefix tailTrace_4246608
  have hstable : (prefixWord ++ tailWord_4246608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246608).length < 2 ^ (prefixWord ++ tailWord_4246608).sum := by decide
  have hdescent : baseEnd_4246608 < baseStart_4246608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246618 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_4246618 : Nat := 118140960795 + 4246618 * 2 ^ 59
def prefixEnd_4246618 : Nat := 4983230072969 + 3 ^ 40 * 4246618 * 2
def baseEnd_4246618 : Nat := 242284021114996813471685

theorem tailTrace_4246618 : CollatzResearch.WordTrace tailWord_4246618 prefixEnd_4246618 242284021114996813471685 := by
  unfold tailWord_4246618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38721720732308931364561127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103257921952823816972163005 38721720732308931364561127)
  ·
    refine ⟨58082581098463397046841691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38721720732308931364561127 58082581098463397046841691)
    ·
      refine ⟨87123871647695095570262537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58082581098463397046841691 87123871647695095570262537)
      ·
        refine ⟨65342903735771321677696903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87123871647695095570262537 65342903735771321677696903)
        ·
          refine ⟨98014355603656982516545355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65342903735771321677696903 98014355603656982516545355)
          ·
            refine ⟨147021533405485473774818033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98014355603656982516545355 147021533405485473774818033)
            ·
              refine ⟨110266150054114105331113525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147021533405485473774818033 110266150054114105331113525)
              ·
                refine ⟨10337451567573197374791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110266150054114105331113525 10337451567573197374791893)
                ·
                  refine ⟨242284021114996813471685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10337451567573197374791893 242284021114996813471685)
                  ·
                    rfl

theorem cell23_4246618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_4246618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246618 prefixEnd_4246618 := by exact prefixLift 4246618
  have htrace : WordTrace (prefixWord ++ tailWord_4246618) baseStart_4246618 baseEnd_4246618 := by
    simpa [prefixWord, tailWord_4246618, baseEnd_4246618] using wordTrace_append hprefix tailTrace_4246618
  have hstable : (prefixWord ++ tailWord_4246618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246618).length < 2 ^ (prefixWord ++ tailWord_4246618).sum := by decide
  have hdescent : baseEnd_4246618 < baseStart_4246618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246629 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_4246629 : Nat := 118140960795 + 4246629 * 2 ^ 59
def prefixEnd_4246629 : Nat := 4983230072969 + 3 ^ 40 * 4246629 * 2
def baseEnd_4246629 : Nat := 2180561838322170778207615

theorem tailTrace_4246629 : CollatzResearch.WordTrace tailWord_4246629 prefixEnd_4246629 2180561838322170778207615 := by
  unfold tailWord_4246629
  simp only [CollatzResearch.WordTrace]
  refine ⟨154887284132195874336894941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103258189421463916224596627 154887284132195874336894941)
  ·
    refine ⟨58082731549573452876335603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154887284132195874336894941 58082731549573452876335603)
    ·
      refine ⟨87124097324360179314503405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58082731549573452876335603 87124097324360179314503405)
      ·
        refine ⟨32671536496635067242938777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87124097324360179314503405 32671536496635067242938777)
        ·
          refine ⟨24503652372476300432204083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32671536496635067242938777 24503652372476300432204083)
          ·
            refine ⟨36755478558714450648306125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24503652372476300432204083 36755478558714450648306125)
            ·
              refine ⟨13783304459517918993114797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36755478558714450648306125 13783304459517918993114797)
              ·
                refine ⟨5168739172319219622418049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13783304459517918993114797 5168739172319219622418049)
                ·
                  refine ⟨3876554379239414716813537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168739172319219622418049 3876554379239414716813537)
                  ·
                    refine ⟨2907415784429561037610153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3876554379239414716813537 2907415784429561037610153)
                    ·
                      refine ⟨2180561838322170778207615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907415784429561037610153 2180561838322170778207615)
                      ·
                        rfl

theorem cell23_4246629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_4246629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246629 prefixEnd_4246629 := by exact prefixLift 4246629
  have htrace : WordTrace (prefixWord ++ tailWord_4246629) baseStart_4246629 baseEnd_4246629 := by
    simpa [prefixWord, tailWord_4246629, baseEnd_4246629] using wordTrace_append hprefix tailTrace_4246629
  have hstable : (prefixWord ++ tailWord_4246629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246629).length < 2 ^ (prefixWord ++ tailWord_4246629).sum := by decide
  have hdescent : baseEnd_4246629 < baseStart_4246629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246648 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_4246648 : Nat := 118140960795 + 4246648 * 2 ^ 59
def prefixEnd_4246648 : Nat := 4983230072969 + 3 ^ 40 * 4246648 * 2
def baseEnd_4246648 : Nat := 726857198151535401290009

theorem tailTrace_4246648 : CollatzResearch.WordTrace tailWord_4246648 prefixEnd_4246648 726857198151535401290009 := by
  unfold tailWord_4246648
  simp only [CollatzResearch.WordTrace]
  refine ⟨77443988559563520290918299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103258651412751360387891065 77443988559563520290918299)
  ·
    refine ⟨116165982839345280436377449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77443988559563520290918299 116165982839345280436377449)
    ·
      refine ⟨87124487129508960327283087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116165982839345280436377449 87124487129508960327283087)
      ·
        refine ⟨130686730694263440490924631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87124487129508960327283087 130686730694263440490924631)
        ·
          refine ⟨196030096041395160736386947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130686730694263440490924631 196030096041395160736386947)
          ·
            refine ⟨294045144062092741104580421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196030096041395160736386947 294045144062092741104580421)
            ·
              refine ⟨55133464511642388957108829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294045144062092741104580421 55133464511642388957108829)
              ·
                refine ⟨20675049191865895858915811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55133464511642388957108829 20675049191865895858915811)
                ·
                  refine ⟨31012573787798843788373717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20675049191865895858915811 31012573787798843788373717)
                  ·
                    refine ⟨726857198151535401290009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31012573787798843788373717 726857198151535401290009)
                    ·
                      rfl

theorem cell23_4246648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_4246648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246648 prefixEnd_4246648 := by exact prefixLift 4246648
  have htrace : WordTrace (prefixWord ++ tailWord_4246648) baseStart_4246648 baseEnd_4246648 := by
    simpa [prefixWord, tailWord_4246648, baseEnd_4246648] using wordTrace_append hprefix tailTrace_4246648
  have hstable : (prefixWord ++ tailWord_4246648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246648).length < 2 ^ (prefixWord ++ tailWord_4246648).sum := by decide
  have hdescent : baseEnd_4246648 < baseStart_4246648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246655 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 5, 2]
def baseStart_4246655 : Nat := 118140960795 + 4246655 * 2 ^ 59
def prefixEnd_4246655 : Nat := 4983230072969 + 3 ^ 40 * 4246655 * 2
def baseEnd_4246655 : Nat := 2180575188819187676482495

theorem tailTrace_4246655 : CollatzResearch.WordTrace tailWord_4246655 prefixEnd_4246655 2180575188819187676482495 := by
  unfold tailWord_4246655
  simp only [CollatzResearch.WordTrace]
  refine ⟨154888232430101680777341419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103258821620067787184894279 154888232430101680777341419)
  ·
    refine ⟨232332348645152521166012129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154888232430101680777341419 232332348645152521166012129)
    ·
      refine ⟨174249261483864390874509097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232332348645152521166012129 174249261483864390874509097)
      ·
        refine ⟨130686946112898293155881823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174249261483864390874509097 130686946112898293155881823)
        ·
          refine ⟨196030419169347439733822735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130686946112898293155881823 196030419169347439733822735)
          ·
            refine ⟨294045628754021159600734103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196030419169347439733822735 294045628754021159600734103)
            ·
              refine ⟨441068443131031739401101155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294045628754021159600734103 441068443131031739401101155)
              ·
                refine ⟨661602664696547609101651733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441068443131031739401101155 661602664696547609101651733)
                ·
                  refine ⟨31012624907650669176639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 661602664696547609101651733 31012624907650669176639925)
                  ·
                    refine ⟨2907433585092250235309993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31012624907650669176639925 2907433585092250235309993)
                    ·
                      refine ⟨2180575188819187676482495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907433585092250235309993 2180575188819187676482495)
                      ·
                        rfl

theorem cell23_4246655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_4246655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246655 prefixEnd_4246655 := by exact prefixLift 4246655
  have htrace : WordTrace (prefixWord ++ tailWord_4246655) baseStart_4246655 baseEnd_4246655 := by
    simpa [prefixWord, tailWord_4246655, baseEnd_4246655] using wordTrace_append hprefix tailTrace_4246655
  have hstable : (prefixWord ++ tailWord_4246655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246655).length < 2 ^ (prefixWord ++ tailWord_4246655).sum := by decide
  have hdescent : baseEnd_4246655 < baseStart_4246655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246665 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_4246665 : Nat := 118140960795 + 4246665 * 2 ^ 59
def prefixEnd_4246665 : Nat := 4983230072969 + 3 ^ 40 * 4246665 * 2
def baseEnd_4246665 : Nat := 726860107875244212452483

theorem tailTrace_4246665 : CollatzResearch.WordTrace tailWord_4246665 prefixEnd_4246665 726860107875244212452483 := by
  unfold tailWord_4246665
  simp only [CollatzResearch.WordTrace]
  refine ⟨154888597160065452485205449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103259064773376968323470299 154888597160065452485205449)
  ·
    refine ⟨116166447870049089363904087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154888597160065452485205449 116166447870049089363904087)
    ·
      refine ⟨174249671805073634045856131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116166447870049089363904087 174249671805073634045856131)
      ·
        refine ⟨261374507707610451068784197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174249671805073634045856131 261374507707610451068784197)
        ·
          refine ⟨49007720195176959575397037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261374507707610451068784197 49007720195176959575397037)
          ·
            refine ⟨18377895073191359840773889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49007720195176959575397037 18377895073191359840773889)
            ·
              refine ⟨13783421304893519880580417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18377895073191359840773889 13783421304893519880580417)
              ·
                refine ⟨10337565978670139910435313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13783421304893519880580417 10337565978670139910435313)
                ·
                  refine ⟨7753174484002604932826485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10337565978670139910435313 7753174484002604932826485)
                  ·
                    refine ⟨726860107875244212452483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7753174484002604932826485 726860107875244212452483)
                    ·
                      rfl

theorem cell23_4246665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_4246665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246665 prefixEnd_4246665 := by exact prefixLift 4246665
  have htrace : WordTrace (prefixWord ++ tailWord_4246665) baseStart_4246665 baseEnd_4246665 := by
    simpa [prefixWord, tailWord_4246665, baseEnd_4246665] using wordTrace_append hprefix tailTrace_4246665
  have hstable : (prefixWord ++ tailWord_4246665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246665).length < 2 ^ (prefixWord ++ tailWord_4246665).sum := by decide
  have hdescent : baseEnd_4246665 < baseStart_4246665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246685 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4246685 : Nat := 118140960795 + 4246685 * 2 ^ 59
def prefixEnd_4246685 : Nat := 4983230072969 + 3 ^ 40 * 4246685 * 2
def baseEnd_4246685 : Nat := 2180590593238822559107357

theorem tailTrace_4246685 : CollatzResearch.WordTrace tailWord_4246685 prefixEnd_4246685 2180590593238822559107357 := by
  unfold tailWord_4246685
  simp only [CollatzResearch.WordTrace]
  refine ⟨154889326619992995900933509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103259551079995330600622339 154889326619992995900933509)
  ·
    refine ⟨29041748741248686731425033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154889326619992995900933509 29041748741248686731425033)
    ·
      refine ⟨21781311555936515048568775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29041748741248686731425033 21781311555936515048568775)
      ·
        refine ⟨32671967333904772572853163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21781311555936515048568775 32671967333904772572853163)
        ·
          refine ⟨49007951000857158859279745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32671967333904772572853163 49007951000857158859279745)
          ·
            refine ⟨36755963250642869144459809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49007951000857158859279745 36755963250642869144459809)
            ·
              refine ⟨27566972437982151858344857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36755963250642869144459809 27566972437982151858344857)
              ·
                refine ⟨20675229328486613893758643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27566972437982151858344857 20675229328486613893758643)
                ·
                  refine ⟨31012843992729920840637965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20675229328486613893758643 31012843992729920840637965)
                  ·
                    refine ⟨11629816497273720315239237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31012843992729920840637965 11629816497273720315239237)
                    ·
                      refine ⟨2180590593238822559107357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11629816497273720315239237 2180590593238822559107357)
                      ·
                        rfl

theorem cell23_4246685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4246685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246685 prefixEnd_4246685 := by exact prefixLift 4246685
  have htrace : WordTrace (prefixWord ++ tailWord_4246685) baseStart_4246685 baseEnd_4246685 := by
    simpa [prefixWord, tailWord_4246685, baseEnd_4246685] using wordTrace_append hprefix tailTrace_4246685
  have hstable : (prefixWord ++ tailWord_4246685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246685).length < 2 ^ (prefixWord ++ tailWord_4246685).sum := by decide
  have hdescent : baseEnd_4246685 < baseStart_4246685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246836 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4246836 : Nat := 118140960795 + 4246836 * 2 ^ 59
def prefixEnd_4246836 : Nat := 4983230072969 + 3 ^ 40 * 4246836 * 2
def baseEnd_4246836 : Nat := 726889376272550489439721

theorem tailTrace_4246836 : CollatzResearch.WordTrace tailWord_4246836 prefixEnd_4246836 726889376272550489439721 := by
  unfold tailWord_4246836
  simp only [CollatzResearch.WordTrace]
  refine ⟨77447417021222974344840181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103263222694963965793120241 77447417021222974344840181)
  ·
    refine ⟨7260695345739653844828767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77447417021222974344840181 7260695345739653844828767)
    ·
      refine ⟨10891043018609480767243151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7260695345739653844828767 10891043018609480767243151)
      ·
        refine ⟨16336564527914221150864727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10891043018609480767243151 16336564527914221150864727)
        ·
          refine ⟨24504846791871331726297091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16336564527914221150864727 24504846791871331726297091)
          ·
            refine ⟨36757270187806997589445637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24504846791871331726297091 36757270187806997589445637)
            ·
              refine ⟨6891988160213812048021057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36757270187806997589445637 6891988160213812048021057)
              ·
                refine ⟨5168991120160359036015793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6891988160213812048021057 5168991120160359036015793)
                ·
                  refine ⟨3876743340120269277011845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5168991120160359036015793 3876743340120269277011845)
                  ·
                    refine ⟨726889376272550489439721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3876743340120269277011845 726889376272550489439721)
                    ·
                      rfl

theorem cell23_4246836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4246836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246836 prefixEnd_4246836 := by exact prefixLift 4246836
  have htrace : WordTrace (prefixWord ++ tailWord_4246836) baseStart_4246836 baseEnd_4246836 := by
    simpa [prefixWord, tailWord_4246836, baseEnd_4246836] using wordTrace_append hprefix tailTrace_4246836
  have hstable : (prefixWord ++ tailWord_4246836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246836).length < 2 ^ (prefixWord ++ tailWord_4246836).sum := by decide
  have hdescent : baseEnd_4246836 < baseStart_4246836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246842 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_4246842 : Nat := 118140960795 + 4246842 * 2 ^ 59
def prefixEnd_4246842 : Nat := 4983230072969 + 3 ^ 40 * 4246842 * 2
def baseEnd_4246842 : Nat := 2180671209701578444844135

theorem tailTrace_4246842 : CollatzResearch.WordTrace tailWord_4246842 prefixEnd_4246842 2180671209701578444844135 := by
  unfold tailWord_4246842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38723763220106052928599695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103263368586949474476265853 38723763220106052928599695)
  ·
    refine ⟨58085644830159079392899543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38723763220106052928599695 58085644830159079392899543)
    ·
      refine ⟨87128467245238619089349315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58085644830159079392899543 87128467245238619089349315)
      ·
        refine ⟨130692700867857928634023973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87128467245238619089349315 130692700867857928634023973)
        ·
          refine ⟨24504881412723361618879495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130692700867857928634023973 24504881412723361618879495)
          ·
            refine ⟨36757322119085042428319243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24504881412723361618879495 36757322119085042428319243)
            ·
              refine ⟨55135983178627563642478865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36757322119085042428319243 55135983178627563642478865)
              ·
                refine ⟨41351987383970672731859149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55135983178627563642478865 41351987383970672731859149)
                ·
                  refine ⟨15506995268989002274447181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41351987383970672731859149 15506995268989002274447181)
                  ·
                    refine ⟨5815123225870875852917693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15506995268989002274447181 5815123225870875852917693)
                    ·
                      refine ⟨2180671209701578444844135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815123225870875852917693 2180671209701578444844135)
                      ·
                        rfl

theorem cell23_4246842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_4246842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246842 prefixEnd_4246842 := by exact prefixLift 4246842
  have htrace : WordTrace (prefixWord ++ tailWord_4246842) baseStart_4246842 baseEnd_4246842 := by
    simpa [prefixWord, tailWord_4246842, baseEnd_4246842] using wordTrace_append hprefix tailTrace_4246842
  have hstable : (prefixWord ++ tailWord_4246842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246842).length < 2 ^ (prefixWord ++ tailWord_4246842).sum := by decide
  have hdescent : baseEnd_4246842 < baseStart_4246842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246849 : List Nat := [1, 2, 5, 2, 1, 3, 1, 8]
def baseStart_4246849 : Nat := 118140960795 + 4246849 * 2 ^ 59
def prefixEnd_4246849 : Nat := 4983230072969 + 3 ^ 40 * 4246849 * 2
def baseEnd_4246849 : Nat := 80765733483931848794689

theorem tailTrace_4246849 : CollatzResearch.WordTrace tailWord_4246849 prefixEnd_4246849 80765733483931848794689 := by
  unfold tailWord_4246849
  simp only [CollatzResearch.WordTrace]
  refine ⟨154895308191398851909903601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103263538794265901273269067 154895308191398851909903601)
  ·
    refine ⟨116171481143549138932427701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154895308191398851909903601 116171481143549138932427701)
    ·
      refine ⟨10891076357207731774915097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116171481143549138932427701 10891076357207731774915097)
      ·
        refine ⟨8168307267905798831186323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10891076357207731774915097 8168307267905798831186323)
        ·
          refine ⟨12252460901858698246779485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168307267905798831186323 12252460901858698246779485)
          ·
            refine ⟨4594672838197011842542307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12252460901858698246779485 4594672838197011842542307)
            ·
              refine ⟨6892009257295517763813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594672838197011842542307 6892009257295517763813461)
              ·
                refine ⟨80765733483931848794689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6892009257295517763813461 80765733483931848794689)
                ·
                  rfl

theorem cell23_4246849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 8].length) (baseStart_4246849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246849 prefixEnd_4246849 := by exact prefixLift 4246849
  have htrace : WordTrace (prefixWord ++ tailWord_4246849) baseStart_4246849 baseEnd_4246849 := by
    simpa [prefixWord, tailWord_4246849, baseEnd_4246849] using wordTrace_append hprefix tailTrace_4246849
  have hstable : (prefixWord ++ tailWord_4246849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246849).length < 2 ^ (prefixWord ++ tailWord_4246849).sum := by decide
  have hdescent : baseEnd_4246849 < baseStart_4246849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246877 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4246877 : Nat := 118140960795 + 4246877 * 2 ^ 59
def prefixEnd_4246877 : Nat := 4983230072969 + 3 ^ 40 * 4246877 * 2
def baseEnd_4246877 : Nat := 2180689181524485807906475

theorem tailTrace_4246877 : CollatzResearch.WordTrace tailWord_4246877 prefixEnd_4246877 2180689181524485807906475 := by
  unfold tailWord_4246877
  simp only [CollatzResearch.WordTrace]
  refine ⟨154896329435297412691922885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103264219623531608461281923 154896329435297412691922885)
  ·
    refine ⟨29043061769118264879735541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154896329435297412691922885 29043061769118264879735541)
    ·
      refine ⟨2722787040854837332475207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29043061769118264879735541 2722787040854837332475207)
      ·
        refine ⟨4084180561282255998712811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722787040854837332475207 4084180561282255998712811)
        ·
          refine ⟨6126270841923383998069217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084180561282255998712811 6126270841923383998069217)
          ·
            refine ⟨4594703131442537998551913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126270841923383998069217 4594703131442537998551913)
            ·
              refine ⟨3446027348581903498913935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4594703131442537998551913 3446027348581903498913935)
              ·
                refine ⟨5169041022872855248370903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446027348581903498913935 5169041022872855248370903)
                ·
                  refine ⟨7753561534309282872556355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169041022872855248370903 7753561534309282872556355)
                  ·
                    refine ⟨11630342301463924308834533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7753561534309282872556355 11630342301463924308834533)
                    ·
                      refine ⟨2180689181524485807906475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11630342301463924308834533 2180689181524485807906475)
                      ·
                        rfl

theorem cell23_4246877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4246877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246877 prefixEnd_4246877 := by exact prefixLift 4246877
  have htrace : WordTrace (prefixWord ++ tailWord_4246877) baseStart_4246877 baseEnd_4246877 := by
    simpa [prefixWord, tailWord_4246877, baseEnd_4246877] using wordTrace_append hprefix tailTrace_4246877
  have hstable : (prefixWord ++ tailWord_4246877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246877).length < 2 ^ (prefixWord ++ tailWord_4246877).sum := by decide
  have hdescent : baseEnd_4246877 < baseStart_4246877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246892 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_4246892 : Nat := 118140960795 + 4246892 * 2 ^ 59
def prefixEnd_4246892 : Nat := 4983230072969 + 3 ^ 40 * 4246892 * 2
def baseEnd_4246892 : Nat := 726898961244767749739635

theorem tailTrace_4246892 : CollatzResearch.WordTrace tailWord_4246892 prefixEnd_4246892 726898961244767749739635 := by
  unfold tailWord_4246892
  simp only [CollatzResearch.WordTrace]
  refine ⟨77448438265121535126859465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103264584353495380169145953 77448438265121535126859465)
  ·
    refine ⟨58086328698841151345144599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77448438265121535126859465 58086328698841151345144599)
    ·
      refine ⟨87129493048261727017716899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58086328698841151345144599 87129493048261727017716899)
      ·
        refine ⟨130694239572392590526575349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87129493048261727017716899 130694239572392590526575349)
        ·
          refine ⟨12252584959911805361866439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130694239572392590526575349 12252584959911805361866439)
          ·
            refine ⟨18378877439867708042799659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12252584959911805361866439 18378877439867708042799659)
            ·
              refine ⟨27568316159801562064199489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18378877439867708042799659 27568316159801562064199489)
              ·
                refine ⟨20676237119851171548149617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27568316159801562064199489 20676237119851171548149617)
                ·
                  refine ⟨15507177839888378661112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20676237119851171548149617 15507177839888378661112213)
                  ·
                    refine ⟨726898961244767749739635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15507177839888378661112213 726898961244767749739635)
                    ·
                      rfl

theorem cell23_4246892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_4246892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246892 prefixEnd_4246892 := by exact prefixLift 4246892
  have htrace : WordTrace (prefixWord ++ tailWord_4246892) baseStart_4246892 baseEnd_4246892 := by
    simpa [prefixWord, tailWord_4246892, baseEnd_4246892] using wordTrace_append hprefix tailTrace_4246892
  have hstable : (prefixWord ++ tailWord_4246892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246892).length < 2 ^ (prefixWord ++ tailWord_4246892).sum := by decide
  have hdescent : baseEnd_4246892 < baseStart_4246892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246893 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4246893 : Nat := 118140960795 + 4246893 * 2 ^ 59
def prefixEnd_4246893 : Nat := 4983230072969 + 3 ^ 40 * 4246893 * 2
def baseEnd_4246893 : Nat := 2180697397214957745306401

theorem tailTrace_4246893 : CollatzResearch.WordTrace tailWord_4246893 prefixEnd_4246893 2180697397214957745306401 := by
  unfold tailWord_4246893
  simp only [CollatzResearch.WordTrace]
  refine ⟨154896913003239447424505333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103264608668826298283003555 154896913003239447424505333)
  ·
    refine ⟨14521585594053698196047375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154896913003239447424505333 14521585594053698196047375)
    ·
      refine ⟨21782378391080547294071063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14521585594053698196047375 21782378391080547294071063)
      ·
        refine ⟨32673567586620820941106595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21782378391080547294071063 32673567586620820941106595)
        ·
          refine ⟨49010351379931231411659893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32673567586620820941106595 49010351379931231411659893)
          ·
            refine ⟨4594720441868552944843115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49010351379931231411659893 4594720441868552944843115)
            ·
              refine ⟨6892080662802829417264673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594720441868552944843115 6892080662802829417264673)
              ·
                refine ⟨5169060497102122062948505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6892080662802829417264673 5169060497102122062948505)
                ·
                  refine ⟨3876795372826591547211379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169060497102122062948505 3876795372826591547211379)
                  ·
                    refine ⟨5815193059239887320817069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876795372826591547211379 5815193059239887320817069)
                    ·
                      refine ⟨2180697397214957745306401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815193059239887320817069 2180697397214957745306401)
                      ·
                        rfl

theorem cell23_4246893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4246893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246893 prefixEnd_4246893 := by exact prefixLift 4246893
  have htrace : WordTrace (prefixWord ++ tailWord_4246893) baseStart_4246893 baseEnd_4246893 := by
    simpa [prefixWord, tailWord_4246893, baseEnd_4246893] using wordTrace_append hprefix tailTrace_4246893
  have hstable : (prefixWord ++ tailWord_4246893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246893).length < 2 ^ (prefixWord ++ tailWord_4246893).sum := by decide
  have hdescent : baseEnd_4246893 < baseStart_4246893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246910 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4246910 : Nat := 118140960795 + 4246910 * 2 ^ 59
def prefixEnd_4246910 : Nat := 4983230072969 + 3 ^ 40 * 4246910 * 2
def baseEnd_4246910 : Nat := 2180706126386084178793823

theorem tailTrace_4246910 : CollatzResearch.WordTrace tailWord_4246910 prefixEnd_4246910 2180706126386084178793823 := by
  unfold tailWord_4246910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362191630522232415984273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103265022029451906218582789 19362191630522232415984273)
  ·
    refine ⟨14521643722891674311988205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19362191630522232415984273 14521643722891674311988205)
    ·
      refine ⟨5445616396084377866995577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14521643722891674311988205 5445616396084377866995577)
      ·
        refine ⟨4084212297063283400246683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5445616396084377866995577 4084212297063283400246683)
        ·
          refine ⟨6126318445594925100370025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084212297063283400246683 6126318445594925100370025)
          ·
            refine ⟨4594738834196193825277519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126318445594925100370025 4594738834196193825277519)
            ·
              refine ⟨6892108251294290737916279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594738834196193825277519 6892108251294290737916279)
              ·
                refine ⟨10338162376941436106874419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892108251294290737916279 10338162376941436106874419)
                ·
                  refine ⟨15507243565412154160311629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10338162376941436106874419 15507243565412154160311629)
                  ·
                    refine ⟨5815216337029557810116861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15507243565412154160311629 5815216337029557810116861)
                    ·
                      refine ⟨2180706126386084178793823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815216337029557810116861 2180706126386084178793823)
                      ·
                        rfl

theorem cell23_4246910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4246910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246910 prefixEnd_4246910 := by exact prefixLift 4246910
  have htrace : WordTrace (prefixWord ++ tailWord_4246910) baseStart_4246910 baseEnd_4246910 := by
    simpa [prefixWord, tailWord_4246910, baseEnd_4246910] using wordTrace_append hprefix tailTrace_4246910
  have hstable : (prefixWord ++ tailWord_4246910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246910).length < 2 ^ (prefixWord ++ tailWord_4246910).sum := by decide
  have hdescent : baseEnd_4246910 < baseStart_4246910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4246916 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_4246916 : Nat := 118140960795 + 4246916 * 2 ^ 59
def prefixEnd_4246916 : Nat := 4983230072969 + 3 ^ 40 * 4246916 * 2
def baseEnd_4246916 : Nat := 2180709207270011155318795

theorem tailTrace_4246916 : CollatzResearch.WordTrace tailWord_4246916 prefixEnd_4246916 2180709207270011155318795 := by
  unfold tailWord_4246916
  simp only [CollatzResearch.WordTrace]
  refine ⟨77448875941078061176296301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103265167921437414901728401 77448875941078061176296301)
  ·
    refine ⟨29043328477904272941111113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77448875941078061176296301 29043328477904272941111113)
    ·
      refine ⟨21782496358428204705833335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29043328477904272941111113 21782496358428204705833335)
      ·
        refine ⟨32673744537642307058750003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21782496358428204705833335 32673744537642307058750003)
        ·
          refine ⟨49010616806463460588125005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32673744537642307058750003 49010616806463460588125005)
          ·
            refine ⟨18378981302423797720546877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49010616806463460588125005 18378981302423797720546877)
            ·
              refine ⟨6892117988408924145205079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18378981302423797720546877 6892117988408924145205079)
              ·
                refine ⟨10338176982613386217807619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892117988408924145205079 10338176982613386217807619)
                ·
                  refine ⟨15507265473920079326711429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10338176982613386217807619 15507265473920079326711429)
                  ·
                    refine ⟨2907612276360014873758393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15507265473920079326711429 2907612276360014873758393)
                    ·
                      refine ⟨2180709207270011155318795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907612276360014873758393 2180709207270011155318795)
                      ·
                        rfl

theorem cell23_4246916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_4246916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4246916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4246916 prefixEnd_4246916 := by exact prefixLift 4246916
  have htrace : WordTrace (prefixWord ++ tailWord_4246916) baseStart_4246916 baseEnd_4246916 := by
    simpa [prefixWord, tailWord_4246916, baseEnd_4246916] using wordTrace_append hprefix tailTrace_4246916
  have hstable : (prefixWord ++ tailWord_4246916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4246916).length < 2 ^ (prefixWord ++ tailWord_4246916).sum := by decide
  have hdescent : baseEnd_4246916 < baseStart_4246916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4246916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247012 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 8]
def baseStart_4247012 : Nat := 118140960795 + 4247012 * 2 ^ 59
def prefixEnd_4247012 : Nat := 4983230072969 + 3 ^ 40 * 4247012 * 2
def baseEnd_4247012 : Nat := 242306500156982531079817

theorem tailTrace_4247012 : CollatzResearch.WordTrace tailWord_4247012 prefixEnd_4247012 242306500156982531079817 := by
  unfold tailWord_4247012
  simp only [CollatzResearch.WordTrace]
  refine ⟨77450626644904165374043645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103267502193205553832058193 77450626644904165374043645)
  ·
    refine ⟨29043984991839062015266367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77450626644904165374043645 29043984991839062015266367)
    ·
      refine ⟨43565977487758593022899551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29043984991839062015266367 43565977487758593022899551)
      ·
        refine ⟨65348966231637889534349327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43565977487758593022899551 65348966231637889534349327)
        ·
          refine ⟨98023449347456834301523991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65348966231637889534349327 98023449347456834301523991)
          ·
            refine ⟨147035174021185251452285987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98023449347456834301523991 147035174021185251452285987)
            ·
              refine ⟨220552761031777877178428981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147035174021185251452285987 220552761031777877178428981)
              ·
                refine ⟨20676821346729175985477717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220552761031777877178428981 20676821346729175985477717)
                ·
                  refine ⟨242306500156982531079817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20676821346729175985477717 242306500156982531079817)
                  ·
                    rfl

theorem cell23_4247012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_4247012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247012 prefixEnd_4247012 := by exact prefixLift 4247012
  have htrace : WordTrace (prefixWord ++ tailWord_4247012) baseStart_4247012 baseEnd_4247012 := by
    simpa [prefixWord, tailWord_4247012, baseEnd_4247012] using wordTrace_append hprefix tailTrace_4247012
  have hstable : (prefixWord ++ tailWord_4247012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247012).length < 2 ^ (prefixWord ++ tailWord_4247012).sum := by decide
  have hdescent : baseEnd_4247012 < baseStart_4247012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247066 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2]
def baseStart_4247066 : Nat := 118140960795 + 4247066 * 2 ^ 59
def prefixEnd_4247066 : Nat := 4983230072969 + 3 ^ 40 * 4247066 * 2
def baseEnd_4247066 : Nat := 2180786229368185568443105

theorem tailTrace_4247066 : CollatzResearch.WordTrace tailWord_4247066 prefixEnd_4247066 2180786229368185568443105 := by
  unfold tailWord_4247066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725805707903174492638263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103268815221075131980368701 38725805707903174492638263)
  ·
    refine ⟨58088708561854761738957395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38725805707903174492638263 58088708561854761738957395)
    ·
      refine ⟨87133062842782142608436093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58088708561854761738957395 87133062842782142608436093)
      ·
        refine ⟨32674898566043303478163535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87133062842782142608436093 32674898566043303478163535)
        ·
          refine ⟨49012347849064955217245303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32674898566043303478163535 49012347849064955217245303)
          ·
            refine ⟨73518521773597432825867955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49012347849064955217245303 73518521773597432825867955)
            ·
              refine ⟨110277782660396149238801933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73518521773597432825867955 110277782660396149238801933)
              ·
                refine ⟨41354168497648555964550725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110277782660396149238801933 41354168497648555964550725)
                ·
                  refine ⟨7753906593309104243353261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41354168497648555964550725 7753906593309104243353261)
                  ·
                    refine ⟨2907714972490914091257473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7753906593309104243353261 2907714972490914091257473)
                    ·
                      refine ⟨2180786229368185568443105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907714972490914091257473 2180786229368185568443105)
                      ·
                        rfl

theorem cell23_4247066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_4247066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247066 prefixEnd_4247066 := by exact prefixLift 4247066
  have htrace : WordTrace (prefixWord ++ tailWord_4247066) baseStart_4247066 baseEnd_4247066 := by
    simpa [prefixWord, tailWord_4247066, baseEnd_4247066] using wordTrace_append hprefix tailTrace_4247066
  have hstable : (prefixWord ++ tailWord_4247066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247066).length < 2 ^ (prefixWord ++ tailWord_4247066).sum := by decide
  have hdescent : baseEnd_4247066 < baseStart_4247066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247073 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4247073 : Nat := 118140960795 + 4247073 * 2 ^ 59
def prefixEnd_4247073 : Nat := 4983230072969 + 3 ^ 40 * 4247073 * 2
def baseEnd_4247073 : Nat := 2180789823732767041055573

theorem tailTrace_4247073 : CollatzResearch.WordTrace tailWord_4247073 prefixEnd_4247073 2180789823732767041055573 := by
  unfold tailWord_4247073
  simp only [CollatzResearch.WordTrace]
  refine ⟨154903478142587338166057873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103268985428391558777371915 154903478142587338166057873)
  ·
    refine ⟨116177608606940503624543405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154903478142587338166057873 116177608606940503624543405)
    ·
      refine ⟨43566603227602688859203777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116177608606940503624543405 43566603227602688859203777)
      ·
        refine ⟨32674952420702016644402833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43566603227602688859203777 32674952420702016644402833)
        ·
          refine ⟨24506214315526512483302125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32674952420702016644402833 24506214315526512483302125)
          ·
            refine ⟨9189830368322442181238297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24506214315526512483302125 9189830368322442181238297)
            ·
              refine ⟨6892372776241831635928723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9189830368322442181238297 6892372776241831635928723)
              ·
                refine ⟨10338559164362747453893085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892372776241831635928723 10338559164362747453893085)
                ·
                  refine ⟨3876959686636030295209907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10338559164362747453893085 3876959686636030295209907)
                  ·
                    refine ⟨5815439529954045442814861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3876959686636030295209907 5815439529954045442814861)
                    ·
                      refine ⟨2180789823732767041055573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815439529954045442814861 2180789823732767041055573)
                      ·
                        rfl

theorem cell23_4247073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4247073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247073 prefixEnd_4247073 := by exact prefixLift 4247073
  have htrace : WordTrace (prefixWord ++ tailWord_4247073) baseStart_4247073 baseEnd_4247073 := by
    simpa [prefixWord, tailWord_4247073, baseEnd_4247073] using wordTrace_append hprefix tailTrace_4247073
  have hstable : (prefixWord ++ tailWord_4247073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247073).length < 2 ^ (prefixWord ++ tailWord_4247073).sum := by decide
  have hdescent : baseEnd_4247073 < baseStart_4247073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247096 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_4247096 : Nat := 118140960795 + 4247096 * 2 ^ 59
def prefixEnd_4247096 : Nat := 4983230072969 + 3 ^ 40 * 4247096 * 2
def baseEnd_4247096 : Nat := 2180801633787820451067967

theorem tailTrace_4247096 : CollatzResearch.WordTrace tailWord_4247096 prefixEnd_4247096 2180801633787820451067967 := by
  unfold tailWord_4247096
  simp only [CollatzResearch.WordTrace]
  refine ⟨77452158510752006547072571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103269544681002675396096761 77452158510752006547072571)
  ·
    refine ⟨116178237766128009820608857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77452158510752006547072571 116178237766128009820608857)
    ·
      refine ⟨87133678324596007365456643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116178237766128009820608857 87133678324596007365456643)
      ·
        refine ⟨130700517486894011048184965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87133678324596007365456643 130700517486894011048184965)
        ·
          refine ⟨24506347028792627071534681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130700517486894011048184965 24506347028792627071534681)
          ·
            refine ⟨18379760271594470303651011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24506347028792627071534681 18379760271594470303651011)
            ·
              refine ⟨27569640407391705455476517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18379760271594470303651011 27569640407391705455476517)
              ·
                refine ⟨5169307576385944772901847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27569640407391705455476517 5169307576385944772901847)
                ·
                  refine ⟨7753961364578917159352771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169307576385944772901847 7753961364578917159352771)
                  ·
                    refine ⟨11630942046868375739029157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7753961364578917159352771 11630942046868375739029157)
                    ·
                      refine ⟨2180801633787820451067967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11630942046868375739029157 2180801633787820451067967)
                      ·
                        rfl

theorem cell23_4247096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_4247096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247096 prefixEnd_4247096 := by exact prefixLift 4247096
  have htrace : WordTrace (prefixWord ++ tailWord_4247096) baseStart_4247096 baseEnd_4247096 := by
    simpa [prefixWord, tailWord_4247096, baseEnd_4247096] using wordTrace_append hprefix tailTrace_4247096
  have hstable : (prefixWord ++ tailWord_4247096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247096).length < 2 ^ (prefixWord ++ tailWord_4247096).sum := by decide
  have hdescent : baseEnd_4247096 < baseStart_4247096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247109 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4247109 : Nat := 118140960795 + 4247109 * 2 ^ 59
def prefixEnd_4247109 : Nat := 4983230072969 + 3 ^ 40 * 4247109 * 2
def baseEnd_4247109 : Nat := 2180808309036328900205407

theorem tailTrace_4247109 : CollatzResearch.WordTrace tailWord_4247109 prefixEnd_4247109 2180808309036328900205407 := by
  unfold tailWord_4247109
  simp only [CollatzResearch.WordTrace]
  refine ⟨154904791170456916314368381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103269860780304610876245587 154904791170456916314368381)
  ·
    refine ⟨58089296688921343617888143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154904791170456916314368381 58089296688921343617888143)
    ·
      refine ⟨87133945033382015426832215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58089296688921343617888143 87133945033382015426832215)
      ·
        refine ⟨130700917550073023140248323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87133945033382015426832215 130700917550073023140248323)
        ·
          refine ⟨196051376325109534710372485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130700917550073023140248323 196051376325109534710372485)
          ·
            refine ⟨36759633060958037758194841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196051376325109534710372485 36759633060958037758194841)
            ·
              refine ⟨27569724795718528318646131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36759633060958037758194841 27569724795718528318646131)
              ·
                refine ⟨41354587193577792477969197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27569724795718528318646131 41354587193577792477969197)
                ·
                  refine ⟨15507970197591672179238449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41354587193577792477969197 15507970197591672179238449)
                  ·
                    refine ⟨11630977648193754134428837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15507970197591672179238449 11630977648193754134428837)
                    ·
                      refine ⟨2180808309036328900205407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11630977648193754134428837 2180808309036328900205407)
                      ·
                        rfl

theorem cell23_4247109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4247109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247109 prefixEnd_4247109 := by exact prefixLift 4247109
  have htrace : WordTrace (prefixWord ++ tailWord_4247109) baseStart_4247109 baseEnd_4247109 := by
    simpa [prefixWord, tailWord_4247109, baseEnd_4247109] using wordTrace_append hprefix tailTrace_4247109
  have hstable : (prefixWord ++ tailWord_4247109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247109).length < 2 ^ (prefixWord ++ tailWord_4247109).sum := by decide
  have hdescent : baseEnd_4247109 < baseStart_4247109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247116 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4247116 : Nat := 118140960795 + 4247116 * 2 ^ 59
def prefixEnd_4247116 : Nat := 4983230072969 + 3 ^ 40 * 4247116 * 2
def baseEnd_4247116 : Nat := 2180811903400910372817875

theorem tailTrace_4247116 : CollatzResearch.WordTrace tailWord_4247116 prefixEnd_4247116 2180811903400910372817875 := by
  unfold tailWord_4247116
  simp only [CollatzResearch.WordTrace]
  refine ⟨77452523240715778254936601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103270030987621037673248801 77452523240715778254936601)
  ·
    refine ⟨58089392430536833691202451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77452523240715778254936601 58089392430536833691202451)
    ·
      refine ⟨87134088645805250536803677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58089392430536833691202451 87134088645805250536803677)
      ·
        refine ⟨32675283242176968951301379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87134088645805250536803677 32675283242176968951301379)
        ·
          refine ⟨49012924863265453426952069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32675283242176968951301379 49012924863265453426952069)
          ·
            refine ⟨9189923411862272517553513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49012924863265453426952069 9189923411862272517553513)
            ·
              refine ⟨6892442558896704388165135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9189923411862272517553513 6892442558896704388165135)
              ·
                refine ⟨10338663838345056582247703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892442558896704388165135 10338663838345056582247703)
                ·
                  refine ⟨15507995757517584873371555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10338663838345056582247703 15507995757517584873371555)
                  ·
                    refine ⟨23261993636276377310057333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15507995757517584873371555 23261993636276377310057333)
                    ·
                      refine ⟨2180811903400910372817875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23261993636276377310057333 2180811903400910372817875)
                      ·
                        rfl

theorem cell23_4247116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4247116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247116 prefixEnd_4247116 := by exact prefixLift 4247116
  have htrace : WordTrace (prefixWord ++ tailWord_4247116) baseStart_4247116 baseEnd_4247116 := by
    simpa [prefixWord, tailWord_4247116, baseEnd_4247116] using wordTrace_append hprefix tailTrace_4247116
  have hstable : (prefixWord ++ tailWord_4247116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247116).length < 2 ^ (prefixWord ++ tailWord_4247116).sum := by decide
  have hdescent : baseEnd_4247116 < baseStart_4247116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247130 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_4247130 : Nat := 118140960795 + 4247130 * 2 ^ 59
def prefixEnd_4247130 : Nat := 4983230072969 + 3 ^ 40 * 4247130 * 2
def baseEnd_4247130 : Nat := 2180819092130073318042811

theorem tailTrace_4247130 : CollatzResearch.WordTrace tailWord_4247130 prefixEnd_4247130 2180819092130073318042811 := by
  unfold tailWord_4247130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38726389275845209225220711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103270371402253891267255229 38726389275845209225220711)
  ·
    refine ⟨58089583913767813837831067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38726389275845209225220711 58089583913767813837831067)
    ·
      refine ⟨87134375870651720756746601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58089583913767813837831067 87134375870651720756746601)
      ·
        refine ⟨65350781902988790567559951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87134375870651720756746601 65350781902988790567559951)
        ·
          refine ⟨98026172854483185851339927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65350781902988790567559951 98026172854483185851339927)
          ·
            refine ⟨147039259281724778777009891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98026172854483185851339927 147039259281724778777009891)
            ·
              refine ⟨220558888922587168165514837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147039259281724778777009891 220558888922587168165514837)
              ·
                refine ⟨2584674479561568376939627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 220558888922587168165514837 2584674479561568376939627)
                ·
                  refine ⟨3877011719342352565409441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584674479561568376939627 3877011719342352565409441)
                  ·
                    refine ⟨2907758789506764424057081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877011719342352565409441 2907758789506764424057081)
                    ·
                      refine ⟨2180819092130073318042811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907758789506764424057081 2180819092130073318042811)
                      ·
                        rfl

theorem cell23_4247130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_4247130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247130 prefixEnd_4247130 := by exact prefixLift 4247130
  have htrace : WordTrace (prefixWord ++ tailWord_4247130) baseStart_4247130 baseEnd_4247130 := by
    simpa [prefixWord, tailWord_4247130, baseEnd_4247130] using wordTrace_append hprefix tailTrace_4247130
  have hstable : (prefixWord ++ tailWord_4247130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247130).length < 2 ^ (prefixWord ++ tailWord_4247130).sum := by decide
  have hdescent : baseEnd_4247130 < baseStart_4247130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247140 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_4247140 : Nat := 118140960795 + 4247140 * 2 ^ 59
def prefixEnd_4247140 : Nat := 4983230072969 + 3 ^ 40 * 4247140 * 2
def baseEnd_4247140 : Nat := 726941408978872759639255

theorem tailTrace_4247140 : CollatzResearch.WordTrace tailWord_4247140 prefixEnd_4247140 726941408978872759639255 := by
  unfold tailWord_4247140
  simp only [CollatzResearch.WordTrace]
  refine ⟨77452960916672304304373437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103270614555563072405831249 77452960916672304304373437)
  ·
    refine ⟨29044860343752114114140039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77452960916672304304373437 29044860343752114114140039)
    ·
      refine ⟨43567290515628171171210059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29044860343752114114140039 43567290515628171171210059)
      ·
        refine ⟨65350935773442256756815089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43567290515628171171210059 65350935773442256756815089)
        ·
          refine ⟨49013201830081692567611317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65350935773442256756815089 49013201830081692567611317)
          ·
            refine ⟨4594987671570158678213561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49013201830081692567611317 4594987671570158678213561)
            ·
              refine ⟨3446240753677619008660171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4594987671570158678213561 3446240753677619008660171)
              ·
                refine ⟨5169361130516428512990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446240753677619008660171 5169361130516428512990257)
                ·
                  refine ⟨3877020847887321384742693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169361130516428512990257 3877020847887321384742693)
                  ·
                    refine ⟨726941408978872759639255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877020847887321384742693 726941408978872759639255)
                    ·
                      rfl

theorem cell23_4247140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_4247140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247140 prefixEnd_4247140 := by exact prefixLift 4247140
  have htrace : WordTrace (prefixWord ++ tailWord_4247140) baseStart_4247140 baseEnd_4247140 := by
    simpa [prefixWord, tailWord_4247140, baseEnd_4247140] using wordTrace_append hprefix tailTrace_4247140
  have hstable : (prefixWord ++ tailWord_4247140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247140).length < 2 ^ (prefixWord ++ tailWord_4247140).sum := by decide
  have hdescent : baseEnd_4247140 < baseStart_4247140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247179 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 6]
def baseStart_4247179 : Nat := 118140960795 + 4247179 * 2 ^ 59
def prefixEnd_4247179 : Nat := 4983230072969 + 3 ^ 40 * 4247179 * 2
def baseEnd_4247179 : Nat := 726948084227381208776695

theorem tailTrace_4247179 : CollatzResearch.WordTrace tailWord_4247179 prefixEnd_4247179 726948084227381208776695 := by
  unfold tailWord_4247179
  simp only [CollatzResearch.WordTrace]
  refine ⟨154907344280203318269416591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103271562853468878846277727 154907344280203318269416591)
  ·
    refine ⟨232361016420304977404124887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154907344280203318269416591 232361016420304977404124887)
    ·
      refine ⟨348541524630457466106187331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232361016420304977404124887 348541524630457466106187331)
      ·
        refine ⟨522812286945686199159280997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348541524630457466106187331 522812286945686199159280997)
        ·
          refine ⟨98027303802316162342365187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 522812286945686199159280997 98027303802316162342365187)
          ·
            refine ⟨147040955703474243513547781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98027303802316162342365187 147040955703474243513547781)
            ·
              refine ⟨27570179194401420658790209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147040955703474243513547781 27570179194401420658790209)
              ·
                refine ⟨20677634395801065494092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27570179194401420658790209 20677634395801065494092657)
                ·
                  refine ⟨15508225796850799120569493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20677634395801065494092657 15508225796850799120569493)
                  ·
                    refine ⟨726948084227381208776695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15508225796850799120569493 726948084227381208776695)
                    ·
                      rfl

theorem cell23_4247179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 6].length) (baseStart_4247179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247179 prefixEnd_4247179 := by exact prefixLift 4247179
  have htrace : WordTrace (prefixWord ++ tailWord_4247179) baseStart_4247179 baseEnd_4247179 := by
    simpa [prefixWord, tailWord_4247179, baseEnd_4247179] using wordTrace_append hprefix tailTrace_4247179
  have hstable : (prefixWord ++ tailWord_4247179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247179).length < 2 ^ (prefixWord ++ tailWord_4247179).sum := by decide
  have hdescent : baseEnd_4247179 < baseStart_4247179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247189 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4247189 : Nat := 118140960795 + 4247189 * 2 ^ 59
def prefixEnd_4247189 : Nat := 4983230072969 + 3 ^ 40 * 4247189 * 2
def baseEnd_4247189 : Nat := 2180849387488688587205039

theorem tailTrace_4247189 : CollatzResearch.WordTrace tailWord_4247189 prefixEnd_4247189 2180849387488688587205039 := by
  unfold tailWord_4247189
  simp only [CollatzResearch.WordTrace]
  refine ⟨154907709010167089977280621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103271806006778059984853747 154907709010167089977280621)
  ·
    refine ⟨58090390878812658741480233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154907709010167089977280621 58090390878812658741480233)
    ·
      refine ⟨43567793159109494056110175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58090390878812658741480233 43567793159109494056110175)
      ·
        refine ⟨65351689738664241084165263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43567793159109494056110175 65351689738664241084165263)
        ·
          refine ⟨98027534607996361626247895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65351689738664241084165263 98027534607996361626247895)
          ·
            refine ⟨147041301911994542439371843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98027534607996361626247895 147041301911994542439371843)
            ·
              refine ⟨220561952867991813659057765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147041301911994542439371843 220561952867991813659057765)
              ·
                refine ⟨41355366162748465061073331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220561952867991813659057765 41355366162748465061073331)
                ·
                  refine ⟨62033049244122697591609997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41355366162748465061073331 62033049244122697591609997)
                  ·
                    refine ⟨23262393466546011596853749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62033049244122697591609997 23262393466546011596853749)
                    ·
                      refine ⟨2180849387488688587205039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23262393466546011596853749 2180849387488688587205039)
                      ·
                        rfl

theorem cell23_4247189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4247189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247189 prefixEnd_4247189 := by exact prefixLift 4247189
  have htrace : WordTrace (prefixWord ++ tailWord_4247189) baseStart_4247189 baseEnd_4247189 := by
    simpa [prefixWord, tailWord_4247189, baseEnd_4247189] using wordTrace_append hprefix tailTrace_4247189
  have hstable : (prefixWord ++ tailWord_4247189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247189).length < 2 ^ (prefixWord ++ tailWord_4247189).sum := by decide
  have hdescent : baseEnd_4247189 < baseStart_4247189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247203 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 4, 2]
def baseStart_4247203 : Nat := 118140960795 + 4247203 * 2 ^ 59
def prefixEnd_4247203 : Nat := 4983230072969 + 3 ^ 40 * 4247203 * 2
def baseEnd_4247203 : Nat := 2180856576217851532429975

theorem tailTrace_4247203 : CollatzResearch.WordTrace tailWord_4247203 prefixEnd_4247203 2180856576217851532429975 := by
  unfold tailWord_4247203
  simp only [CollatzResearch.WordTrace]
  refine ⟨154908219632116370368290263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103272146421410913578860175 154908219632116370368290263)
  ·
    refine ⟨232362329448174555552435395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154908219632116370368290263 232362329448174555552435395)
    ·
      refine ⟨348543494172261833328653093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232362329448174555552435395 348543494172261833328653093)
      ·
        refine ⟨65351905157299093749122455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348543494172261833328653093 65351905157299093749122455)
        ·
          refine ⟨98027857735948640623683683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65351905157299093749122455 98027857735948640623683683)
          ·
            refine ⟨147041786603922960935525525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98027857735948640623683683 147041786603922960935525525)
            ·
              refine ⟨6892583747058888793852759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147041786603922960935525525 6892583747058888793852759)
              ·
                refine ⟨10338875620588333190779139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892583747058888793852759 10338875620588333190779139)
                ·
                  refine ⟨15508313430882499786168709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10338875620588333190779139 15508313430882499786168709)
                  ·
                    refine ⟨2907808768290468709906633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15508313430882499786168709 2907808768290468709906633)
                    ·
                      refine ⟨2180856576217851532429975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907808768290468709906633 2180856576217851532429975)
                      ·
                        rfl

theorem cell23_4247203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_4247203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247203 prefixEnd_4247203 := by exact prefixLift 4247203
  have htrace : WordTrace (prefixWord ++ tailWord_4247203) baseStart_4247203 baseEnd_4247203 := by
    simpa [prefixWord, tailWord_4247203, baseEnd_4247203] using wordTrace_append hprefix tailTrace_4247203
  have hstable : (prefixWord ++ tailWord_4247203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247203).length < 2 ^ (prefixWord ++ tailWord_4247203).sum := by decide
  have hdescent : baseEnd_4247203 < baseStart_4247203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247276 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_4247276 : Nat := 118140960795 + 4247276 * 2 ^ 59
def prefixEnd_4247276 : Nat := 4983230072969 + 3 ^ 40 * 4247276 * 2
def baseEnd_4247276 : Nat := 2180894060305629746817139

theorem tailTrace_4247276 : CollatzResearch.WordTrace tailWord_4247276 prefixEnd_4247276 2180894060305629746817139 := by
  unfold tailWord_4247276
  simp only [CollatzResearch.WordTrace]
  refine ⟨77455441080425951917848841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103273921440567935890465121 77455441080425951917848841)
  ·
    refine ⟨58091580810319463938386631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77455441080425951917848841 58091580810319463938386631)
    ·
      refine ⟨87137371215479195907579947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58091580810319463938386631 87137371215479195907579947)
      ·
        refine ⟨130706056823218793861369921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87137371215479195907579947 130706056823218793861369921)
        ·
          refine ⟨98029542617414095396027441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130706056823218793861369921 98029542617414095396027441)
          ·
            refine ⟨73522156963060571547020581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98029542617414095396027441 73522156963060571547020581)
            ·
              refine ⟨13785404430573857165066359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73522156963060571547020581 13785404430573857165066359)
              ·
                refine ⟨20678106645860785747599539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13785404430573857165066359 20678106645860785747599539)
                ·
                  refine ⟨31017159968791178621399309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20678106645860785747599539 31017159968791178621399309)
                  ·
                    refine ⟨11631434988296691983024741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31017159968791178621399309 11631434988296691983024741)
                    ·
                      refine ⟨2180894060305629746817139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11631434988296691983024741 2180894060305629746817139)
                      ·
                        rfl

theorem cell23_4247276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_4247276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247276 prefixEnd_4247276 := by exact prefixLift 4247276
  have htrace : WordTrace (prefixWord ++ tailWord_4247276) baseStart_4247276 baseEnd_4247276 := by
    simpa [prefixWord, tailWord_4247276, baseEnd_4247276] using wordTrace_append hprefix tailTrace_4247276
  have hstable : (prefixWord ++ tailWord_4247276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247276).length < 2 ^ (prefixWord ++ tailWord_4247276).sum := by decide
  have hdescent : baseEnd_4247276 < baseStart_4247276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247293 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_4247293 : Nat := 118140960795 + 4247293 * 2 ^ 59
def prefixEnd_4247293 : Nat := 4983230072969 + 3 ^ 40 * 4247293 * 2
def baseEnd_4247293 : Nat := 2180902789476756180304561

theorem tailTrace_4247293 : CollatzResearch.WordTrace tailWord_4247293 prefixEnd_4247293 2180902789476756180304561 := by
  unfold tailWord_4247293
  simp only [CollatzResearch.WordTrace]
  refine ⟨154911502201790315739066533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103274334801193543826044355 154911502201790315739066533)
  ·
    refine ⟨29045906662835684201074975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154911502201790315739066533 29045906662835684201074975)
    ·
      refine ⟨43568859994253526301612463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29045906662835684201074975 43568859994253526301612463)
      ·
        refine ⟨65353289991380289452418695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43568859994253526301612463 65353289991380289452418695)
        ·
          refine ⟨98029934987070434178628043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65353289991380289452418695 98029934987070434178628043)
          ·
            refine ⟨147044902480605651267942065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98029934987070434178628043 147044902480605651267942065)
            ·
              refine ⟨110283676860454238450956549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147044902480605651267942065 110283676860454238450956549)
              ·
                refine ⟨20678189411335169709554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110283676860454238450956549 20678189411335169709554353)
                ·
                  refine ⟨15508642058501377282165765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20678189411335169709554353 15508642058501377282165765)
                  ·
                    refine ⟨2907870385969008240406081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15508642058501377282165765 2907870385969008240406081)
                    ·
                      refine ⟨2180902789476756180304561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907870385969008240406081 2180902789476756180304561)
                      ·
                        rfl

theorem cell23_4247293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_4247293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247293 prefixEnd_4247293 := by exact prefixLift 4247293
  have htrace : WordTrace (prefixWord ++ tailWord_4247293) baseStart_4247293 baseEnd_4247293 := by
    simpa [prefixWord, tailWord_4247293, baseEnd_4247293] using wordTrace_append hprefix tailTrace_4247293
  have hstable : (prefixWord ++ tailWord_4247293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247293).length < 2 ^ (prefixWord ++ tailWord_4247293).sum := by decide
  have hdescent : baseEnd_4247293 < baseStart_4247293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247330 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4247330 : Nat := 118140960795 + 4247330 * 2 ^ 59
def prefixEnd_4247330 : Nat := 4983230072969 + 3 ^ 40 * 4247330 * 2
def baseEnd_4247330 : Nat := 2180921788260972535541891

theorem tailTrace_4247330 : CollatzResearch.WordTrace tailWord_4247330 prefixEnd_4247330 2180921788260972535541891 := by
  unfold tailWord_4247330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38728212925664067764540861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103275234468437514038775629 38728212925664067764540861)
  ·
    refine ⟨14523079847124025411702823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38728212925664067764540861 14523079847124025411702823)
    ·
      refine ⟨21784619770686038117554235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14523079847124025411702823 21784619770686038117554235)
      ·
        refine ⟨32676929656029057176331353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21784619770686038117554235 32676929656029057176331353)
        ·
          refine ⟨24507697242021792882248515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32676929656029057176331353 24507697242021792882248515)
          ·
            refine ⟨36761545863032689323372773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24507697242021792882248515 36761545863032689323372773)
            ·
              refine ⟨6892789849318629248132395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36761545863032689323372773 6892789849318629248132395)
              ·
                refine ⟨10339184773977943872198593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892789849318629248132395 10339184773977943872198593)
                ·
                  refine ⟨7754388580483457904148945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10339184773977943872198593 7754388580483457904148945)
                  ·
                    refine ⟨5815791435362593428111709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7754388580483457904148945 5815791435362593428111709)
                    ·
                      refine ⟨2180921788260972535541891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815791435362593428111709 2180921788260972535541891)
                      ·
                        rfl

theorem cell23_4247330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4247330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247330 prefixEnd_4247330 := by exact prefixLift 4247330
  have htrace : WordTrace (prefixWord ++ tailWord_4247330) baseStart_4247330 baseEnd_4247330 := by
    simpa [prefixWord, tailWord_4247330, baseEnd_4247330] using wordTrace_append hprefix tailTrace_4247330
  have hstable : (prefixWord ++ tailWord_4247330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247330).length < 2 ^ (prefixWord ++ tailWord_4247330).sum := by decide
  have hdescent : baseEnd_4247330 < baseStart_4247330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247343 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_4247343 : Nat := 118140960795 + 4247343 * 2 ^ 59
def prefixEnd_4247343 : Nat := 4983230072969 + 3 ^ 40 * 4247343 * 2
def baseEnd_4247343 : Nat := 2180928463509480984679331

theorem tailTrace_4247343 : CollatzResearch.WordTrace tailWord_4247343 prefixEnd_4247343 2180928463509480984679331 := by
  unfold tailWord_4247343
  simp only [CollatzResearch.WordTrace]
  refine ⟨154913325851609174278386683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103275550567739449518924455 154913325851609174278386683)
  ·
    refine ⟨232369988777413761417580025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154913325851609174278386683 232369988777413761417580025)
    ·
      refine ⟨174277491583060321063185019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232369988777413761417580025 174277491583060321063185019)
      ·
        refine ⟨261416237374590481594777529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174277491583060321063185019 261416237374590481594777529)
        ·
          refine ⟨196062178030942861196083147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261416237374590481594777529 196062178030942861196083147)
          ·
            refine ⟨294093267046414291794124721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196062178030942861196083147 294093267046414291794124721)
            ·
              refine ⟨220569950284810718845593541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294093267046414291794124721 220569950284810718845593541)
              ·
                refine ⟨41356865678402009783548789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220569950284810718845593541 41356865678402009783548789)
                ·
                  refine ⟨3877206157350188417207699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41356865678402009783548789 3877206157350188417207699)
                  ·
                    refine ⟨5815809236025282625811549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877206157350188417207699 5815809236025282625811549)
                    ·
                      refine ⟨2180928463509480984679331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815809236025282625811549 2180928463509480984679331)
                      ·
                        rfl

theorem cell23_4247343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_4247343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247343 prefixEnd_4247343 := by exact prefixLift 4247343
  have htrace : WordTrace (prefixWord ++ tailWord_4247343) baseStart_4247343 baseEnd_4247343 := by
    simpa [prefixWord, tailWord_4247343, baseEnd_4247343] using wordTrace_append hprefix tailTrace_4247343
  have hstable : (prefixWord ++ tailWord_4247343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247343).length < 2 ^ (prefixWord ++ tailWord_4247343).sum := by decide
  have hdescent : baseEnd_4247343 < baseStart_4247343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247350 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_4247350 : Nat := 118140960795 + 4247350 * 2 ^ 59
def prefixEnd_4247350 : Nat := 4983230072969 + 3 ^ 40 * 4247350 * 2
def baseEnd_4247350 : Nat := 242325784208229161921311

theorem tailTrace_4247350 : CollatzResearch.WordTrace tailWord_4247350 prefixEnd_4247350 242325784208229161921311 := by
  unfold tailWord_4247350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682098822661488404618219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103275720775055876315927669 9682098822661488404618219)
  ·
    refine ⟨14523148233992232606927329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9682098822661488404618219 14523148233992232606927329)
    ·
      refine ⟨10892361175494174455195497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14523148233992232606927329 10892361175494174455195497)
      ·
        refine ⟨8169270881620630841396623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10892361175494174455195497 8169270881620630841396623)
        ·
          refine ⟨12253906322430946262094935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169270881620630841396623 12253906322430946262094935)
          ·
            refine ⟨18380859483646419393142403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12253906322430946262094935 18380859483646419393142403)
            ·
              refine ⟨27571289225469629089713605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18380859483646419393142403 27571289225469629089713605)
              ·
                refine ⟨5169616729775555454321301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27571289225469629089713605 5169616729775555454321301)
                ·
                  refine ⟨242325784208229161921311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5169616729775555454321301 242325784208229161921311)
                  ·
                    rfl

theorem cell23_4247350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_4247350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247350 prefixEnd_4247350 := by exact prefixLift 4247350
  have htrace : WordTrace (prefixWord ++ tailWord_4247350) baseStart_4247350 baseEnd_4247350 := by
    simpa [prefixWord, tailWord_4247350, baseEnd_4247350] using wordTrace_append hprefix tailTrace_4247350
  have hstable : (prefixWord ++ tailWord_4247350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247350).length < 2 ^ (prefixWord ++ tailWord_4247350).sum := by decide
  have hdescent : baseEnd_4247350 < baseStart_4247350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247354 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_4247354 : Nat := 118140960795 + 4247354 * 2 ^ 59
def prefixEnd_4247354 : Nat := 4983230072969 + 3 ^ 40 * 4247354 * 2
def baseEnd_4247354 : Nat := 726978037265560147213927

theorem tailTrace_4247354 : CollatzResearch.WordTrace tailWord_4247354 prefixEnd_4247354 726978037265560147213927 := by
  unfold tailWord_4247354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38728431763642330789259279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103275818036379548771358077 38728431763642330789259279)
  ·
    refine ⟨58092647645463496183888919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38728431763642330789259279 58092647645463496183888919)
    ·
      refine ⟨87138971468195244275833379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58092647645463496183888919 87138971468195244275833379)
      ·
        refine ⟨130708457202292866413750069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87138971468195244275833379 130708457202292866413750069)
        ·
          refine ⟨12253917862714956226289069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130708457202292866413750069 12253917862714956226289069)
          ·
            refine ⟨4595219198518108584858401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12253917862714956226289069 4595219198518108584858401)
            ·
              refine ⟨3446414398888581438643801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4595219198518108584858401 3446414398888581438643801)
              ·
                refine ⟨2584810799166436078982851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446414398888581438643801 2584810799166436078982851)
                ·
                  refine ⟨3877216198749654118474277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584810799166436078982851 3877216198749654118474277)
                  ·
                    refine ⟨726978037265560147213927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877216198749654118474277 726978037265560147213927)
                    ·
                      rfl

theorem cell23_4247354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_4247354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247354 prefixEnd_4247354 := by exact prefixLift 4247354
  have htrace : WordTrace (prefixWord ++ tailWord_4247354) baseStart_4247354 baseEnd_4247354 := by
    simpa [prefixWord, tailWord_4247354, baseEnd_4247354] using wordTrace_append hprefix tailTrace_4247354
  have hstable : (prefixWord ++ tailWord_4247354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247354).length < 2 ^ (prefixWord ++ tailWord_4247354).sum := by decide
  have hdescent : baseEnd_4247354 < baseStart_4247354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247393 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_4247393 : Nat := 118140960795 + 4247393 * 2 ^ 59
def prefixEnd_4247393 : Nat := 4983230072969 + 3 ^ 40 * 4247393 * 2
def baseEnd_4247393 : Nat := 726984712514068596351367

theorem tailTrace_4247393 : CollatzResearch.WordTrace tailWord_4247393 prefixEnd_4247393 726984712514068596351367 := by
  unfold tailWord_4247393
  simp only [CollatzResearch.WordTrace]
  refine ⟨154915149501428032817706833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103276766334285355211804555 154915149501428032817706833)
  ·
    refine ⟨116186362126071024613280125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154915149501428032817706833 116186362126071024613280125)
    ·
      refine ⟨43569885797276634229980047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116186362126071024613280125 43569885797276634229980047)
      ·
        refine ⟨65354828695914951344970071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43569885797276634229980047 65354828695914951344970071)
        ·
          refine ⟨98032243043872427017455107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65354828695914951344970071 98032243043872427017455107)
          ·
            refine ⟨147048364565808640526182661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98032243043872427017455107 147048364565808640526182661)
            ·
              refine ⟨27571568356089120098659249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147048364565808640526182661 27571568356089120098659249)
              ·
                refine ⟨20678676267066840073994437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27571568356089120098659249 20678676267066840073994437)
                ·
                  refine ⟨3877251800075032513873957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20678676267066840073994437 3877251800075032513873957)
                  ·
                    refine ⟨726984712514068596351367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877251800075032513873957 726984712514068596351367)
                    ·
                      rfl

theorem cell23_4247393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_4247393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247393 prefixEnd_4247393 := by exact prefixLift 4247393
  have htrace : WordTrace (prefixWord ++ tailWord_4247393) baseStart_4247393 baseEnd_4247393 := by
    simpa [prefixWord, tailWord_4247393, baseEnd_4247393] using wordTrace_append hprefix tailTrace_4247393
  have hstable : (prefixWord ++ tailWord_4247393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247393).length < 2 ^ (prefixWord ++ tailWord_4247393).sum := by decide
  have hdescent : baseEnd_4247393 < baseStart_4247393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247394 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4247394 : Nat := 118140960795 + 4247394 * 2 ^ 59
def prefixEnd_4247394 : Nat := 4983230072969 + 3 ^ 40 * 4247394 * 2
def baseEnd_4247394 : Nat := 2180954651022860285141597

theorem tailTrace_4247394 : CollatzResearch.WordTrace tailWord_4247394 prefixEnd_4247394 2180954651022860285141597 := by
  unfold tailWord_4247394
  simp only [CollatzResearch.WordTrace]
  refine ⟨38728796493606102497123309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103276790649616273325662157 38728796493606102497123309)
  ·
    refine ⟨14523298685102288436421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38728796493606102497123309 14523298685102288436421241)
    ·
      refine ⟨10892474013826716327315931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14523298685102288436421241 10892474013826716327315931)
      ·
        refine ⟨16338711020740074490973897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10892474013826716327315931 16338711020740074490973897)
        ·
          refine ⟨12254033265555055868230423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16338711020740074490973897 12254033265555055868230423)
          ·
            refine ⟨18381049898332583802345635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12254033265555055868230423 18381049898332583802345635)
            ·
              refine ⟨27571574847498875703518453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18381049898332583802345635 27571574847498875703518453)
              ·
                refine ⟨2584835141953019597204855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27571574847498875703518453 2584835141953019597204855)
                ·
                  refine ⟨3877252712929529395807283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584835141953019597204855 3877252712929529395807283)
                  ·
                    refine ⟨5815879069394294093710925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877252712929529395807283 5815879069394294093710925)
                    ·
                      refine ⟨2180954651022860285141597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5815879069394294093710925 2180954651022860285141597)
                      ·
                        rfl

theorem cell23_4247394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4247394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247394 prefixEnd_4247394 := by exact prefixLift 4247394
  have htrace : WordTrace (prefixWord ++ tailWord_4247394) baseStart_4247394 baseEnd_4247394 := by
    simpa [prefixWord, tailWord_4247394, baseEnd_4247394] using wordTrace_append hprefix tailTrace_4247394
  have hstable : (prefixWord ++ tailWord_4247394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247394).length < 2 ^ (prefixWord ++ tailWord_4247394).sum := by decide
  have hdescent : baseEnd_4247394 < baseStart_4247394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247400 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4247400 : Nat := 118140960795 + 4247400 * 2 ^ 59
def prefixEnd_4247400 : Nat := 4983230072969 + 3 ^ 40 * 4247400 * 2
def baseEnd_4247400 : Nat := 2180957731906787261666569

theorem tailTrace_4247400 : CollatzResearch.WordTrace tailWord_4247400 prefixEnd_4247400 2180957731906787261666569 := by
  unfold tailWord_4247400
  simp only [CollatzResearch.WordTrace]
  refine ⟨77457702406201336506605827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103276936541601782008807769 77457702406201336506605827)
  ·
    refine ⟨116186553609302004759908741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77457702406201336506605827 116186553609302004759908741)
    ·
      refine ⟨21784978801744125892482889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116186553609302004759908741 21784978801744125892482889)
      ·
        refine ⟨16338734101308094419362167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21784978801744125892482889 16338734101308094419362167)
        ·
          refine ⟨24508101151962141629043251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16338734101308094419362167 24508101151962141629043251)
          ·
            refine ⟨36762151727943212443564877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24508101151962141629043251 36762151727943212443564877)
            ·
              refine ⟨13785806897978704666336829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36762151727943212443564877 13785806897978704666336829)
              ·
                refine ⟨5169677586742014249876311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13785806897978704666336829 5169677586742014249876311)
                ·
                  refine ⟨7754516380113021374814467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169677586742014249876311 7754516380113021374814467)
                  ·
                    refine ⟨11631774570169532062221701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7754516380113021374814467 11631774570169532062221701)
                    ·
                      refine ⟨2180957731906787261666569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11631774570169532062221701 2180957731906787261666569)
                      ·
                        rfl

theorem cell23_4247400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4247400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247400 prefixEnd_4247400 := by exact prefixLift 4247400
  have htrace : WordTrace (prefixWord ++ tailWord_4247400) baseStart_4247400 baseEnd_4247400 := by
    simpa [prefixWord, tailWord_4247400, baseEnd_4247400] using wordTrace_append hprefix tailTrace_4247400
  have hstable : (prefixWord ++ tailWord_4247400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247400).length < 2 ^ (prefixWord ++ tailWord_4247400).sum := by decide
  have hdescent : baseEnd_4247400 < baseStart_4247400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247413 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4247413 : Nat := 118140960795 + 4247413 * 2 ^ 59
def prefixEnd_4247413 : Nat := 4983230072969 + 3 ^ 40 * 4247413 * 2
def baseEnd_4247413 : Nat := 2180964407155295710804009

theorem tailTrace_4247413 : CollatzResearch.WordTrace tailWord_4247413 prefixEnd_4247413 2180964407155295710804009 := by
  unfold tailWord_4247413
  simp only [CollatzResearch.WordTrace]
  refine ⟨154915878961355576233434893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103277252640903717488956595 154915878961355576233434893)
  ·
    refine ⟨58093454610508341087538085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154915878961355576233434893 58093454610508341087538085)
    ·
      refine ⟨10892522739470313953913391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58093454610508341087538085 10892522739470313953913391)
      ·
        refine ⟨16338784109205470930870087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10892522739470313953913391 16338784109205470930870087)
        ·
          refine ⟨24508176163808206396305131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16338784109205470930870087 24508176163808206396305131)
          ·
            refine ⟨36762264245712309594457697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24508176163808206396305131 36762264245712309594457697)
            ·
              refine ⟨27571698184284232195843273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36762264245712309594457697 27571698184284232195843273)
              ·
                refine ⟨20678773638213174146882455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27571698184284232195843273 20678773638213174146882455)
                ·
                  refine ⟨31018160457319761220323683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20678773638213174146882455 31018160457319761220323683)
                  ·
                    refine ⟨46527240685979641830485525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31018160457319761220323683 46527240685979641830485525)
                    ·
                      refine ⟨2180964407155295710804009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46527240685979641830485525 2180964407155295710804009)
                      ·
                        rfl

theorem cell23_4247413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4247413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247413 prefixEnd_4247413 := by exact prefixLift 4247413
  have htrace : WordTrace (prefixWord ++ tailWord_4247413) baseStart_4247413 baseEnd_4247413 := by
    simpa [prefixWord, tailWord_4247413, baseEnd_4247413] using wordTrace_append hprefix tailTrace_4247413
  have hstable : (prefixWord ++ tailWord_4247413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247413).length < 2 ^ (prefixWord ++ tailWord_4247413).sum := by decide
  have hdescent : baseEnd_4247413 < baseStart_4247413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247417 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 3, 2, 2]
def baseStart_4247417 : Nat := 118140960795 + 4247417 * 2 ^ 59
def prefixEnd_4247417 : Nat := 4983230072969 + 3 ^ 40 * 4247417 * 2
def baseEnd_4247417 : Nat := 2180966461077913695153991

theorem tailTrace_4247417 : CollatzResearch.WordTrace tailWord_4247417 prefixEnd_4247417 2180966461077913695153991 := by
  unfold tailWord_4247417
  simp only [CollatzResearch.WordTrace]
  refine ⟨154916024853341084916580505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103277349902227389944387003 154916024853341084916580505)
  ·
    refine ⟨116187018640005813687435379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154916024853341084916580505 116187018640005813687435379)
    ·
      refine ⟨174280527960008720531153069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116187018640005813687435379 174280527960008720531153069)
      ·
        refine ⟨65355197985003270199182401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174280527960008720531153069 65355197985003270199182401)
        ·
          refine ⟨49016398488752452649386801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65355197985003270199182401 49016398488752452649386801)
          ·
            refine ⟨36762298866564339487040101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49016398488752452649386801 36762298866564339487040101)
            ·
              refine ⟨6892931037480813653820019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36762298866564339487040101 6892931037480813653820019)
              ·
                refine ⟨10339396556221220480730029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892931037480813653820019 10339396556221220480730029)
                ·
                  refine ⟨3877273708582957680273761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10339396556221220480730029 3877273708582957680273761)
                  ·
                    refine ⟨2907955281437218260205321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877273708582957680273761 2907955281437218260205321)
                    ·
                      refine ⟨2180966461077913695153991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2907955281437218260205321 2180966461077913695153991)
                      ·
                        rfl

theorem cell23_4247417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_4247417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247417 prefixEnd_4247417 := by exact prefixLift 4247417
  have htrace : WordTrace (prefixWord ++ tailWord_4247417) baseStart_4247417 baseEnd_4247417 := by
    simpa [prefixWord, tailWord_4247417, baseEnd_4247417] using wordTrace_append hprefix tailTrace_4247417
  have hstable : (prefixWord ++ tailWord_4247417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247417).length < 2 ^ (prefixWord ++ tailWord_4247417).sum := by decide
  have hdescent : baseEnd_4247417 < baseStart_4247417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247427 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 2, 4]
def baseStart_4247427 : Nat := 118140960795 + 4247427 * 2 ^ 59
def prefixEnd_4247427 : Nat := 4983230072969 + 3 ^ 40 * 4247427 * 2
def baseEnd_4247427 : Nat := 726990531961486218676315

theorem tailTrace_4247427 : CollatzResearch.WordTrace tailWord_4247427 prefixEnd_4247427 726990531961486218676315 := by
  unfold tailWord_4247427
  simp only [CollatzResearch.WordTrace]
  refine ⟨154916389583304856624444535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103277593055536571082963023 154916389583304856624444535)
  ·
    refine ⟨232374584374957284936666803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154916389583304856624444535 232374584374957284936666803)
    ·
      refine ⟨348561876562435927405000205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232374584374957284936666803 348561876562435927405000205)
      ·
        refine ⟨130710703710913472776875077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348561876562435927405000205 130710703710913472776875077)
        ·
          refine ⟨24508256945796276145664077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130710703710913472776875077 24508256945796276145664077)
          ·
            refine ⟨9190596354673603554624029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24508256945796276145664077 9190596354673603554624029)
            ·
              refine ⟨3446473633002601332984011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9190596354673603554624029 3446473633002601332984011)
              ·
                refine ⟨5169710449503901999476017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446473633002601332984011 5169710449503901999476017)
                ·
                  refine ⟨3877282837127926499607013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169710449503901999476017 3877282837127926499607013)
                  ·
                    refine ⟨726990531961486218676315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877282837127926499607013 726990531961486218676315)
                    ·
                      rfl

theorem cell23_4247427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 4].length) (baseStart_4247427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247427 prefixEnd_4247427 := by exact prefixLift 4247427
  have htrace : WordTrace (prefixWord ++ tailWord_4247427) baseStart_4247427 baseEnd_4247427 := by
    simpa [prefixWord, tailWord_4247427, baseEnd_4247427] using wordTrace_append hprefix tailTrace_4247427
  have hstable : (prefixWord ++ tailWord_4247427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247427).length < 2 ^ (prefixWord ++ tailWord_4247427).sum := by decide
  have hdescent : baseEnd_4247427 < baseStart_4247427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247454 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4247454 : Nat := 118140960795 + 4247454 * 2 ^ 59
def prefixEnd_4247454 : Nat := 4983230072969 + 3 ^ 40 * 4247454 * 2
def baseEnd_4247454 : Nat := 2180985459862130050391321

theorem tailTrace_4247454 : CollatzResearch.WordTrace tailWord_4247454 prefixEnd_4247454 2180985459862130050391321 := by
  unfold tailWord_4247454
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364671794275880029459677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103278249569471360157118277 19364671794275880029459677)
  ·
    refine ⟨7261751922853455011047379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19364671794275880029459677 7261751922853455011047379)
    ·
      refine ⟨10892627884280182516571069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7261751922853455011047379 10892627884280182516571069)
      ·
        refine ⟨4084735456605068443714151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10892627884280182516571069 4084735456605068443714151)
        ·
          refine ⟨6127103184907602665571227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084735456605068443714151 6127103184907602665571227)
          ·
            refine ⟨9190654777361403998356841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127103184907602665571227 9190654777361403998356841)
            ·
              refine ⟨6892991083021052998767631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9190654777361403998356841 6892991083021052998767631)
              ·
                refine ⟨10339486624531579498151447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892991083021052998767631 10339486624531579498151447)
                ·
                  refine ⟨15509229936797369247227171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10339486624531579498151447 15509229936797369247227171)
                  ·
                    refine ⟨23263844905196053870840757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15509229936797369247227171 23263844905196053870840757)
                    ·
                      refine ⟨2180985459862130050391321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23263844905196053870840757 2180985459862130050391321)
                      ·
                        rfl

theorem cell23_4247454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4247454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247454 prefixEnd_4247454 := by exact prefixLift 4247454
  have htrace : WordTrace (prefixWord ++ tailWord_4247454) baseStart_4247454 baseEnd_4247454 := by
    simpa [prefixWord, tailWord_4247454, baseEnd_4247454] using wordTrace_append hprefix tailTrace_4247454
  have hstable : (prefixWord ++ tailWord_4247454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247454).length < 2 ^ (prefixWord ++ tailWord_4247454).sum := by decide
  have hdescent : baseEnd_4247454 < baseStart_4247454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_4247493 : Nat := 118140960795 + 4247493 * 2 ^ 59
def prefixEnd_4247493 : Nat := 4983230072969 + 3 ^ 40 * 4247493 * 2
def baseEnd_4247493 : Nat := 2181005485607655397803641

theorem tailTrace_4247493 : CollatzResearch.WordTrace tailWord_4247493 prefixEnd_4247493 2181005485607655397803641 := by
  unfold tailWord_4247493
  simp only [CollatzResearch.WordTrace]
  refine ⟨154918796801065749896347133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103279197867377166597564755 154918796801065749896347133)
  ·
    refine ⟨58094548800399656211130175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154918796801065749896347133 58094548800399656211130175)
    ·
      refine ⟨87141823200599484316695263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58094548800399656211130175 87141823200599484316695263)
      ·
        refine ⟨130712734800899226475042895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87141823200599484316695263 130712734800899226475042895)
        ·
          refine ⟨196069102201348839712564343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130712734800899226475042895 196069102201348839712564343)
          ·
            refine ⟨294103653302023259568846515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196069102201348839712564343 294103653302023259568846515)
            ·
              refine ⟨441155479953034889353269773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294103653302023259568846515 441155479953034889353269773)
              ·
                refine ⟨165433304982388083507476165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441155479953034889353269773 165433304982388083507476165)
                ·
                  refine ⟨31018744684197765657651781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165433304982388083507476165 31018744684197765657651781)
                  ·
                    refine ⟨5816014628287081060809709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31018744684197765657651781 5816014628287081060809709)
                    ·
                      refine ⟨2181005485607655397803641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816014628287081060809709 2181005485607655397803641)
                      ·
                        rfl

theorem cell23_4247493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_4247493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247493 prefixEnd_4247493 := by exact prefixLift 4247493
  have htrace : WordTrace (prefixWord ++ tailWord_4247493) baseStart_4247493 baseEnd_4247493 := by
    simpa [prefixWord, tailWord_4247493, baseEnd_4247493] using wordTrace_append hprefix tailTrace_4247493
  have hstable : (prefixWord ++ tailWord_4247493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247493).length < 2 ^ (prefixWord ++ tailWord_4247493).sum := by decide
  have hdescent : baseEnd_4247493 < baseStart_4247493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247524 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_4247524 : Nat := 118140960795 + 4247524 * 2 ^ 59
def prefixEnd_4247524 : Nat := 4983230072969 + 3 ^ 40 * 4247524 * 2
def baseEnd_4247524 : Nat := 2181021403507944776515999

theorem tailTrace_4247524 : CollatzResearch.WordTrace tailWord_4247524 prefixEnd_4247524 2181021403507944776515999 := by
  unfold tailWord_4247524
  simp only [CollatzResearch.WordTrace]
  refine ⟨77459963731976721095362813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103279951642635628127150417 77459963731976721095362813)
  ·
    refine ⟨29047486399491270410761055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77459963731976721095362813 29047486399491270410761055)
    ·
      refine ⟨43571229599236905616141583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29047486399491270410761055 43571229599236905616141583)
      ·
        refine ⟨65356844398855358424212375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43571229599236905616141583 65356844398855358424212375)
        ·
          refine ⟨98035266598283037636318563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65356844398855358424212375 98035266598283037636318563)
          ·
            refine ⟨147052899897424556454477845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98035266598283037636318563 147052899897424556454477845)
            ·
              refine ⟨6893104682691776083803649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147052899897424556454477845 6893104682691776083803649)
              ·
                refine ⟨5169828512018832062852737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6893104682691776083803649 5169828512018832062852737)
                ·
                  refine ⟨3877371384014124047139553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169828512018832062852737 3877371384014124047139553)
                  ·
                    refine ⟨2908028538010593035354665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877371384014124047139553 2908028538010593035354665)
                    ·
                      refine ⟨2181021403507944776515999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908028538010593035354665 2181021403507944776515999)
                      ·
                        rfl

theorem cell23_4247524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_4247524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247524 prefixEnd_4247524 := by exact prefixLift 4247524
  have htrace : WordTrace (prefixWord ++ tailWord_4247524) baseStart_4247524 baseEnd_4247524 := by
    simpa [prefixWord, tailWord_4247524, baseEnd_4247524] using wordTrace_append hprefix tailTrace_4247524
  have hstable : (prefixWord ++ tailWord_4247524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247524).length < 2 ^ (prefixWord ++ tailWord_4247524).sum := by decide
  have hdescent : baseEnd_4247524 < baseStart_4247524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247600 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_4247600 : Nat := 118140960795 + 4247600 * 2 ^ 59
def prefixEnd_4247600 : Nat := 4983230072969 + 3 ^ 40 * 4247600 * 2
def baseEnd_4247600 : Nat := 2181060428037686479165649

theorem tailTrace_4247600 : CollatzResearch.WordTrace tailWord_4247600 prefixEnd_4247600 2181060428037686479165649 := by
  unfold tailWord_4247600
  simp only [CollatzResearch.WordTrace]
  refine ⟨77461349705839053585246127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103281799607785404780328169 77461349705839053585246127)
  ·
    refine ⟨116192024558758580377869191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77461349705839053585246127 116192024558758580377869191)
    ·
      refine ⟨174288036838137870566803787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116192024558758580377869191 174288036838137870566803787)
      ·
        refine ⟨261432055257206805850205681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174288036838137870566803787 261432055257206805850205681)
        ·
          refine ⟨196074041442905104387654261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261432055257206805850205681 196074041442905104387654261)
          ·
            refine ⟨18381941385272353536342587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196074041442905104387654261 18381941385272353536342587)
            ·
              refine ⟨27572912077908530304513881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18381941385272353536342587 27572912077908530304513881)
              ·
                refine ⟨20679684058431397728385411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27572912077908530304513881 20679684058431397728385411)
                ·
                  refine ⟨31019526087647096592578117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20679684058431397728385411 31019526087647096592578117)
                  ·
                    refine ⟨5816161141433830611108397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31019526087647096592578117 5816161141433830611108397)
                    ·
                      refine ⟨2181060428037686479165649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816161141433830611108397 2181060428037686479165649)
                      ·
                        rfl

theorem cell23_4247600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_4247600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247600 prefixEnd_4247600 := by exact prefixLift 4247600
  have htrace : WordTrace (prefixWord ++ tailWord_4247600) baseStart_4247600 baseEnd_4247600 := by
    simpa [prefixWord, tailWord_4247600, baseEnd_4247600] using wordTrace_append hprefix tailTrace_4247600
  have hstable : (prefixWord ++ tailWord_4247600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247600).length < 2 ^ (prefixWord ++ tailWord_4247600).sum := by decide
  have hdescent : baseEnd_4247600 < baseStart_4247600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247617 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4247617 : Nat := 118140960795 + 4247617 * 2 ^ 59
def prefixEnd_4247617 : Nat := 4983230072969 + 3 ^ 40 * 4247617 * 2
def baseEnd_4247617 : Nat := 2181069157208812912653071

theorem tailTrace_4247617 : CollatzResearch.WordTrace tailWord_4247617 prefixEnd_4247617 2181069157208812912653071 := by
  unfold tailWord_4247617
  simp only [CollatzResearch.WordTrace]
  refine ⟨154923319452616519073861105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103282212968411012715907403 154923319452616519073861105)
  ·
    refine ⟨116192489589462389305395829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154923319452616519073861105 116192489589462389305395829)
    ·
      refine ⟨10893045899012098997380859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116192489589462389305395829 10893045899012098997380859)
      ·
        refine ⟨16339568848518148496071289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10893045899012098997380859 16339568848518148496071289)
        ·
          refine ⟨12254676636388611372053467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16339568848518148496071289 12254676636388611372053467)
          ·
            refine ⟨18382014954582917058080201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12254676636388611372053467 18382014954582917058080201)
            ·
              refine ⟨13786511215937187793560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18382014954582917058080201 13786511215937187793560151)
              ·
                refine ⟨20679766823905781690340227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13786511215937187793560151 20679766823905781690340227)
                ·
                  refine ⟨31019650235858672535510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20679766823905781690340227 31019650235858672535510341)
                  ·
                    refine ⟨5816184419223501100408189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31019650235858672535510341 5816184419223501100408189)
                    ·
                      refine ⟨2181069157208812912653071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816184419223501100408189 2181069157208812912653071)
                      ·
                        rfl

theorem cell23_4247617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4247617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247617 prefixEnd_4247617 := by exact prefixLift 4247617
  have htrace : WordTrace (prefixWord ++ tailWord_4247617) baseStart_4247617 baseEnd_4247617 := by
    simpa [prefixWord, tailWord_4247617, baseEnd_4247617] using wordTrace_append hprefix tailTrace_4247617
  have hstable : (prefixWord ++ tailWord_4247617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247617).length < 2 ^ (prefixWord ++ tailWord_4247617).sum := by decide
  have hdescent : baseEnd_4247617 < baseStart_4247617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247634 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_4247634 : Nat := 118140960795 + 4247634 * 2 ^ 59
def prefixEnd_4247634 : Nat := 4983230072969 + 3 ^ 40 * 4247634 * 2
def baseEnd_4247634 : Nat := 2181077886379939346140493

theorem tailTrace_4247634 : CollatzResearch.WordTrace tailWord_4247634 prefixEnd_4247634 2181077886379939346140493 := by
  unfold tailWord_4247634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38730984873388732744307489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103282626329036620651486637 38730984873388732744307489)
  ·
    refine ⟨29048238655041549558230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38730984873388732744307489 29048238655041549558230617)
    ·
      refine ⟨21786178991281162168672963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29048238655041549558230617 21786178991281162168672963)
      ·
        refine ⟨32679268486921743253009445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21786178991281162168672963 32679268486921743253009445)
        ·
          refine ⟨6127362841297826859939271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32679268486921743253009445 6127362841297826859939271)
          ·
            refine ⟨9191044261946740289908907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127362841297826859939271 9191044261946740289908907)
            ·
              refine ⟨13786566392920110434863361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191044261946740289908907 13786566392920110434863361)
              ·
                refine ⟨10339924794690082826147521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13786566392920110434863361 10339924794690082826147521)
                ·
                  refine ⟨7754943596017562119610641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10339924794690082826147521 7754943596017562119610641)
                  ·
                    refine ⟨5816207697013171589707981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7754943596017562119610641 5816207697013171589707981)
                    ·
                      refine ⟨2181077886379939346140493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816207697013171589707981 2181077886379939346140493)
                      ·
                        rfl

theorem cell23_4247634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_4247634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247634 prefixEnd_4247634 := by exact prefixLift 4247634
  have htrace : WordTrace (prefixWord ++ tailWord_4247634) baseStart_4247634 baseEnd_4247634 := by
    simpa [prefixWord, tailWord_4247634, baseEnd_4247634] using wordTrace_append hprefix tailTrace_4247634
  have hstable : (prefixWord ++ tailWord_4247634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247634).length < 2 ^ (prefixWord ++ tailWord_4247634).sum := by decide
  have hdescent : baseEnd_4247634 < baseStart_4247634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247647 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_4247647 : Nat := 118140960795 + 4247647 * 2 ^ 59
def prefixEnd_4247647 : Nat := 4983230072969 + 3 ^ 40 * 4247647 * 2
def baseEnd_4247647 : Nat := 2181084561628447795277933

theorem tailTrace_4247647 : CollatzResearch.WordTrace tailWord_4247647 prefixEnd_4247647 2181084561628447795277933 := by
  unfold tailWord_4247647
  simp only [CollatzResearch.WordTrace]
  refine ⟨154924413642507834197453195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103282942428338556131635463 154924413642507834197453195)
  ·
    refine ⟨232386620463761751296179793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154924413642507834197453195 232386620463761751296179793)
    ·
      refine ⟨174289965347821313472134845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232386620463761751296179793 174289965347821313472134845)
      ·
        refine ⟨65358737005432992552050567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174289965347821313472134845 65358737005432992552050567)
        ·
          refine ⟨98038105508149488828075851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65358737005432992552050567 98038105508149488828075851)
          ·
            refine ⟨147057158262224233242113777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98038105508149488828075851 147057158262224233242113777)
            ·
              refine ⟨110292868696668174931585333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147057158262224233242113777 110292868696668174931585333)
              ·
                refine ⟨10339956440312641399836125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110292868696668174931585333 10339956440312641399836125)
                ·
                  refine ⟨3877483665117240524938547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10339956440312641399836125 3877483665117240524938547)
                  ·
                    refine ⟨5816225497675860787407821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877483665117240524938547 5816225497675860787407821)
                    ·
                      refine ⟨2181084561628447795277933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816225497675860787407821 2181084561628447795277933)
                      ·
                        rfl

theorem cell23_4247647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_4247647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247647 prefixEnd_4247647 := by exact prefixLift 4247647
  have htrace : WordTrace (prefixWord ++ tailWord_4247647) baseStart_4247647 baseEnd_4247647 := by
    simpa [prefixWord, tailWord_4247647, baseEnd_4247647] using wordTrace_append hprefix tailTrace_4247647
  have hstable : (prefixWord ++ tailWord_4247647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247647).length < 2 ^ (prefixWord ++ tailWord_4247647).sum := by decide
  have hdescent : baseEnd_4247647 < baseStart_4247647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247657 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 4, 3, 2]
def baseStart_4247657 : Nat := 118140960795 + 4247657 * 2 ^ 59
def prefixEnd_4247657 : Nat := 4983230072969 + 3 ^ 40 * 4247657 * 2
def baseEnd_4247657 : Nat := 2181089696434992756152887

theorem tailTrace_4247657 : CollatzResearch.WordTrace tailWord_4247657 prefixEnd_4247657 2181089696434992756152887 := by
  unfold tailWord_4247657
  simp only [CollatzResearch.WordTrace]
  refine ⟨154924778372471605905317225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103283185581647737270211483 154924778372471605905317225)
  ·
    refine ⟨116193583779353704428987919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154924778372471605905317225 116193583779353704428987919)
    ·
      refine ⟨174290375669030556643481879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116193583779353704428987919 174290375669030556643481879)
      ·
        refine ⟨261435563503545834965222819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174290375669030556643481879 261435563503545834965222819)
        ·
          refine ⟨392153345255318752447834229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261435563503545834965222819 392153345255318752447834229)
          ·
            refine ⟨36764376117686133041984459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 392153345255318752447834229 36764376117686133041984459)
            ·
              refine ⟨55146564176529199562976689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36764376117686133041984459 55146564176529199562976689)
              ·
                refine ⟨41359923132396899672232517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55146564176529199562976689 41359923132396899672232517)
                ·
                  refine ⟨7754985587324418688543597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41359923132396899672232517 7754985587324418688543597)
                  ·
                    refine ⟨2908119595246657008203849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7754985587324418688543597 2908119595246657008203849)
                    ·
                      refine ⟨2181089696434992756152887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908119595246657008203849 2181089696434992756152887)
                      ·
                        rfl

theorem cell23_4247657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3, 2].length) (baseStart_4247657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247657 prefixEnd_4247657 := by exact prefixLift 4247657
  have htrace : WordTrace (prefixWord ++ tailWord_4247657) baseStart_4247657 baseEnd_4247657 := by
    simpa [prefixWord, tailWord_4247657, baseEnd_4247657] using wordTrace_append hprefix tailTrace_4247657
  have hstable : (prefixWord ++ tailWord_4247657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247657).length < 2 ^ (prefixWord ++ tailWord_4247657).sum := by decide
  have hdescent : baseEnd_4247657 < baseStart_4247657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247684 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_4247684 : Nat := 118140960795 + 4247684 * 2 ^ 59
def prefixEnd_4247684 : Nat := 4983230072969 + 3 ^ 40 * 4247684 * 2
def baseEnd_4247684 : Nat := 727034520137554716838421

theorem tailTrace_4247684 : CollatzResearch.WordTrace tailWord_4247684 prefixEnd_4247684 727034520137554716838421 := by
  unfold tailWord_4247684
  simp only [CollatzResearch.WordTrace]
  refine ⟨77462881571686894758275053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103283842095582526344366737 77462881571686894758275053)
  ·
    refine ⟨29048580589382585534353145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77462881571686894758275053 29048580589382585534353145)
    ·
      refine ⟨21786435442036939150764859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29048580589382585534353145 21786435442036939150764859)
      ·
        refine ⟨32679653163055408726147289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21786435442036939150764859 32679653163055408726147289)
        ·
          refine ⟨24509739872291556544610467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32679653163055408726147289 24509739872291556544610467)
          ·
            refine ⟨36764609808437334816915701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24509739872291556544610467 36764609808437334816915701)
            ·
              refine ⟨3446682169541000139085847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36764609808437334816915701 3446682169541000139085847)
              ·
                refine ⟨5170023254311500208628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446682169541000139085847 5170023254311500208628771)
                ·
                  refine ⟨7755034881467250312943157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170023254311500208628771 7755034881467250312943157)
                  ·
                    refine ⟨727034520137554716838421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7755034881467250312943157 727034520137554716838421)
                    ·
                      rfl

theorem cell23_4247684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_4247684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247684 prefixEnd_4247684 := by exact prefixLift 4247684
  have htrace : WordTrace (prefixWord ++ tailWord_4247684) baseStart_4247684 baseEnd_4247684 := by
    simpa [prefixWord, tailWord_4247684, baseEnd_4247684] using wordTrace_append hprefix tailTrace_4247684
  have hstable : (prefixWord ++ tailWord_4247684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247684).length < 2 ^ (prefixWord ++ tailWord_4247684).sum := by decide
  have hdescent : baseEnd_4247684 < baseStart_4247684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247687 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_4247687 : Nat := 118140960795 + 4247687 * 2 ^ 59
def prefixEnd_4247687 : Nat := 4983230072969 + 3 ^ 40 * 4247687 * 2
def baseEnd_4247687 : Nat := 2181105100854627638777749

theorem tailTrace_4247687 : CollatzResearch.WordTrace tailWord_4247687 prefixEnd_4247687 2181105100854627638777749 := by
  unfold tailWord_4247687
  simp only [CollatzResearch.WordTrace]
  refine ⟨154925872562362921028909315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103283915041575280685939543 154925872562362921028909315)
  ·
    refine ⟨232388808843544381543363973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154925872562362921028909315 232388808843544381543363973)
    ·
      refine ⟨43572901658164571539380745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232388808843544381543363973 43572901658164571539380745)
      ·
        refine ⟨32679676243623428654535559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43572901658164571539380745 32679676243623428654535559)
        ·
          refine ⟨49019514365435142981803339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32679676243623428654535559 49019514365435142981803339)
          ·
            refine ⟨73529271548152714472705009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49019514365435142981803339 73529271548152714472705009)
            ·
              refine ⟨55146953661114535854528757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73529271548152714472705009 55146953661114535854528757)
              ·
                refine ⟨5170026905729487736362071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55146953661114535854528757 5170026905729487736362071)
                ·
                  refine ⟨7755040358594231604543107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170026905729487736362071 7755040358594231604543107)
                  ·
                    refine ⟨11632560537891347406814661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7755040358594231604543107 11632560537891347406814661)
                    ·
                      refine ⟨2181105100854627638777749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11632560537891347406814661 2181105100854627638777749)
                      ·
                        rfl

theorem cell23_4247687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_4247687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247687 prefixEnd_4247687 := by exact prefixLift 4247687
  have htrace : WordTrace (prefixWord ++ tailWord_4247687) baseStart_4247687 baseEnd_4247687 := by
    simpa [prefixWord, tailWord_4247687, baseEnd_4247687] using wordTrace_append hprefix tailTrace_4247687
  have hstable : (prefixWord ++ tailWord_4247687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247687).length < 2 ^ (prefixWord ++ tailWord_4247687).sum := by decide
  have hdescent : baseEnd_4247687 < baseStart_4247687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247714 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4247714 : Nat := 118140960795 + 4247714 * 2 ^ 59
def prefixEnd_4247714 : Nat := 4983230072969 + 3 ^ 40 * 4247714 * 2
def baseEnd_4247714 : Nat := 727039654944099677713375

theorem tailTrace_4247714 : CollatzResearch.WordTrace tailWord_4247714 prefixEnd_4247714 727039654944099677713375 := by
  unfold tailWord_4247714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38731714333316276160035549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103284571555510069760094797 38731714333316276160035549)
  ·
    refine ⟨14524392874993603560013331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38731714333316276160035549 14524392874993603560013331)
    ·
      refine ⟨21786589312490405340019997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14524392874993603560013331 21786589312490405340019997)
      ·
        refine ⟨8169970992183902002507499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21786589312490405340019997 8169970992183902002507499)
        ·
          refine ⟨12254956488275853003761249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169970992183902002507499 12254956488275853003761249)
          ·
            refine ⟨9191217366206889752820937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12254956488275853003761249 9191217366206889752820937)
            ·
              refine ⟨6893413024655167314615703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9191217366206889752820937 6893413024655167314615703)
              ·
                refine ⟨10340119536982750971923555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6893413024655167314615703 10340119536982750971923555)
                ·
                  refine ⟨15510179305474126457885333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10340119536982750971923555 15510179305474126457885333)
                  ·
                    refine ⟨727039654944099677713375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15510179305474126457885333 727039654944099677713375)
                    ·
                      rfl

theorem cell23_4247714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4247714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247714 prefixEnd_4247714 := by exact prefixLift 4247714
  have htrace : WordTrace (prefixWord ++ tailWord_4247714) baseStart_4247714 baseEnd_4247714 := by
    simpa [prefixWord, tailWord_4247714, baseEnd_4247714] using wordTrace_append hprefix tailTrace_4247714
  have hstable : (prefixWord ++ tailWord_4247714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247714).length < 2 ^ (prefixWord ++ tailWord_4247714).sum := by decide
  have hdescent : baseEnd_4247714 < baseStart_4247714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247717 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_4247717 : Nat := 118140960795 + 4247717 * 2 ^ 59
def prefixEnd_4247717 : Nat := 4983230072969 + 3 ^ 40 * 4247717 * 2
def baseEnd_4247717 : Nat := 2181120505274262521402611

theorem tailTrace_4247717 : CollatzResearch.WordTrace tailWord_4247717 prefixEnd_4247717 2181120505274262521402611 := by
  unfold tailWord_4247717
  simp only [CollatzResearch.WordTrace]
  refine ⟨154926966752254236152501405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103284644501502824101667603 154926966752254236152501405)
  ·
    refine ⟨58097612532095338557188027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154926966752254236152501405 58097612532095338557188027)
    ·
      refine ⟨87146418798143007835782041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58097612532095338557188027 87146418798143007835782041)
      ·
        refine ⟨65359814098607255876836531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87146418798143007835782041 65359814098607255876836531)
        ·
          refine ⟨98039721147910883815254797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65359814098607255876836531 98039721147910883815254797)
          ·
            refine ⟨36764895430466581430720549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98039721147910883815254797 36764895430466581430720549)
            ·
              refine ⟨6893417893212484018260103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36764895430466581430720549 6893417893212484018260103)
              ·
                refine ⟨10340126839818726027390155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6893417893212484018260103 10340126839818726027390155)
                ·
                  refine ⟨15510190259728089041085233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10340126839818726027390155 15510190259728089041085233)
                  ·
                    refine ⟨11632642694796066780813925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15510190259728089041085233 11632642694796066780813925)
                    ·
                      refine ⟨2181120505274262521402611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11632642694796066780813925 2181120505274262521402611)
                      ·
                        rfl

theorem cell23_4247717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_4247717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247717 prefixEnd_4247717 := by exact prefixLift 4247717
  have htrace : WordTrace (prefixWord ++ tailWord_4247717) baseStart_4247717 baseEnd_4247717 := by
    simpa [prefixWord, tailWord_4247717, baseEnd_4247717] using wordTrace_append hprefix tailTrace_4247717
  have hstable : (prefixWord ++ tailWord_4247717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247717).length < 2 ^ (prefixWord ++ tailWord_4247717).sum := by decide
  have hdescent : baseEnd_4247717 < baseStart_4247717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247737 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4247737 : Nat := 118140960795 + 4247737 * 2 ^ 59
def prefixEnd_4247737 : Nat := 4983230072969 + 3 ^ 40 * 4247737 * 2
def baseEnd_4247737 : Nat := 2181130774887352443152519

theorem tailTrace_4247737 : CollatzResearch.WordTrace tailWord_4247737 prefixEnd_4247737 2181130774887352443152519 := by
  unfold tailWord_4247737
  simp only [CollatzResearch.WordTrace]
  refine ⟨154927696212181779568229465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103285130808121186378819643 154927696212181779568229465)
  ·
    refine ⟨116195772159136334676172099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154927696212181779568229465 116195772159136334676172099)
    ·
      refine ⟨174293658238704502014258149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116195772159136334676172099 174293658238704502014258149)
      ·
        refine ⟨32680060919757094127673403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174293658238704502014258149 32680060919757094127673403)
        ·
          refine ⟨49020091379635641191510105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32680060919757094127673403 49020091379635641191510105)
          ·
            refine ⟨36765068534726730893632579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49020091379635641191510105 36765068534726730893632579)
            ·
              refine ⟨55147602802090096340448869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36765068534726730893632579 55147602802090096340448869)
              ·
                refine ⟨10340175525391893063834163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55147602802090096340448869 10340175525391893063834163)
                ·
                  refine ⟨15510263288087839595751245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10340175525391893063834163 15510263288087839595751245)
                  ·
                    refine ⟨5816348733032939848406717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15510263288087839595751245 5816348733032939848406717)
                    ·
                      refine ⟨2181130774887352443152519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816348733032939848406717 2181130774887352443152519)
                      ·
                        rfl

theorem cell23_4247737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4247737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247737 prefixEnd_4247737 := by exact prefixLift 4247737
  have htrace : WordTrace (prefixWord ++ tailWord_4247737) baseStart_4247737 baseEnd_4247737 := by
    simpa [prefixWord, tailWord_4247737, baseEnd_4247737] using wordTrace_append hprefix tailTrace_4247737
  have hstable : (prefixWord ++ tailWord_4247737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247737).length < 2 ^ (prefixWord ++ tailWord_4247737).sum := by decide
  have hdescent : baseEnd_4247737 < baseStart_4247737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247754 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_4247754 : Nat := 118140960795 + 4247754 * 2 ^ 59
def prefixEnd_4247754 : Nat := 4983230072969 + 3 ^ 40 * 4247754 * 2
def baseEnd_4247754 : Nat := 2181139504058478876639941

theorem tailTrace_4247754 : CollatzResearch.WordTrace tailWord_4247754 prefixEnd_4247754 2181139504058478876639941 := by
  unfold tailWord_4247754
  simp only [CollatzResearch.WordTrace]
  refine ⟨38732079063280047867899579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103285544168746794314398877 38732079063280047867899579)
  ·
    refine ⟨58098118594920071801849369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38732079063280047867899579 58098118594920071801849369)
    ·
      refine ⟨43573588946190053851387027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58098118594920071801849369 43573588946190053851387027)
      ·
        refine ⟨65360383419285080777080541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43573588946190053851387027 65360383419285080777080541)
        ·
          refine ⟨24510143782231905291405203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65360383419285080777080541 24510143782231905291405203)
          ·
            refine ⟨36765215673347857937107805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24510143782231905291405203 36765215673347857937107805)
            ·
              refine ⟨13786955877505446726415427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36765215673347857937107805 13786955877505446726415427)
              ·
                refine ⟨20680433816258170089623141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13786955877505446726415427 20680433816258170089623141)
                ·
                  refine ⟨3877581340548406891804339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20680433816258170089623141 3877581340548406891804339)
                  ·
                    refine ⟨5816372010822610337706509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877581340548406891804339 5816372010822610337706509)
                    ·
                      refine ⟨2181139504058478876639941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816372010822610337706509 2181139504058478876639941)
                      ·
                        rfl

theorem cell23_4247754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_4247754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247754 prefixEnd_4247754 := by exact prefixLift 4247754
  have htrace : WordTrace (prefixWord ++ tailWord_4247754) baseStart_4247754 baseEnd_4247754 := by
    simpa [prefixWord, tailWord_4247754, baseEnd_4247754] using wordTrace_append hprefix tailTrace_4247754
  have hstable : (prefixWord ++ tailWord_4247754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247754).length < 2 ^ (prefixWord ++ tailWord_4247754).sum := by decide
  have hdescent : baseEnd_4247754 < baseStart_4247754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247781 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4247781 : Nat := 118140960795 + 4247781 * 2 ^ 59
def prefixEnd_4247781 : Nat := 4983230072969 + 3 ^ 40 * 4247781 * 2
def baseEnd_4247781 : Nat := 2181153368036150271002317

theorem tailTrace_4247781 : CollatzResearch.WordTrace tailWord_4247781 prefixEnd_4247781 2181153368036150271002317 := by
  unfold tailWord_4247781
  simp only [CollatzResearch.WordTrace]
  refine ⟨154929301024022375082831197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103286200682681583388554131 154929301024022375082831197)
  ·
    refine ⟨58098487884008390656061699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154929301024022375082831197 58098487884008390656061699)
    ·
      refine ⟨87147731826012585984092549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58098487884008390656061699 87147731826012585984092549)
      ·
        refine ⟨16340199717377359872017353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87147731826012585984092549 16340199717377359872017353)
        ·
          refine ⟨12255149788033019904013015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16340199717377359872017353 12255149788033019904013015)
          ·
            refine ⟨18382724682049529856019523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12255149788033019904013015 18382724682049529856019523)
            ·
              refine ⟨27574087023074294784029285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18382724682049529856019523 27574087023074294784029285)
              ·
                refine ⟨5170141316826430272005491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27574087023074294784029285 5170141316826430272005491)
                ·
                  refine ⟨7755211975239645408008237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170141316826430272005491 7755211975239645408008237)
                  ·
                    refine ⟨2908204490714867028003089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7755211975239645408008237 2908204490714867028003089)
                    ·
                      refine ⟨2181153368036150271002317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908204490714867028003089 2181153368036150271002317)
                      ·
                        rfl

theorem cell23_4247781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4247781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247781 prefixEnd_4247781 := by exact prefixLift 4247781
  have htrace : WordTrace (prefixWord ++ tailWord_4247781) baseStart_4247781 baseEnd_4247781 := by
    simpa [prefixWord, tailWord_4247781, baseEnd_4247781] using wordTrace_append hprefix tailTrace_4247781
  have hstable : (prefixWord ++ tailWord_4247781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247781).length < 2 ^ (prefixWord ++ tailWord_4247781).sum := by decide
  have hdescent : baseEnd_4247781 < baseStart_4247781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247800 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 9]
def baseStart_4247800 : Nat := 118140960795 + 4247800 * 2 ^ 59
def prefixEnd_4247800 : Nat := 4983230072969 + 3 ^ 40 * 4247800 * 2
def baseEnd_4247800 : Nat := 242351458240953966296081

theorem tailTrace_4247800 : CollatzResearch.WordTrace tailWord_4247800 prefixEnd_4247800 242351458240953966296081 := by
  unfold tailWord_4247800
  simp only [CollatzResearch.WordTrace]
  refine ⟨77464997005476770663886427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103286662673969027551848569 77464997005476770663886427)
  ·
    refine ⟨116197495508215155995829641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77464997005476770663886427 116197495508215155995829641)
    ·
      refine ⟨87148121631161366996872231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116197495508215155995829641 87148121631161366996872231)
      ·
        refine ⟨130722182446742050495308347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87148121631161366996872231 130722182446742050495308347)
        ·
          refine ⟨196083273670113075742962521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130722182446742050495308347 196083273670113075742962521)
          ·
            refine ⟨147062455252584806807221891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196083273670113075742962521 147062455252584806807221891)
            ·
              refine ⟨220593682878877210210832837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147062455252584806807221891 220593682878877210210832837)
              ·
                refine ⟨41361315539789476914531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220593682878877210210832837 41361315539789476914531157)
                ·
                  refine ⟨242351458240953966296081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41361315539789476914531157 242351458240953966296081)
                  ·
                    rfl

theorem cell23_4247800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_4247800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247800 prefixEnd_4247800 := by exact prefixLift 4247800
  have htrace : WordTrace (prefixWord ++ tailWord_4247800) baseStart_4247800 baseEnd_4247800 := by
    simpa [prefixWord, tailWord_4247800, baseEnd_4247800] using wordTrace_append hprefix tailTrace_4247800
  have hstable : (prefixWord ++ tailWord_4247800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247800).length < 2 ^ (prefixWord ++ tailWord_4247800).sum := by decide
  have hdescent : baseEnd_4247800 < baseStart_4247800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247811 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 2, 2, 2]
def baseStart_4247811 : Nat := 118140960795 + 4247811 * 2 ^ 59
def prefixEnd_4247811 : Nat := 4983230072969 + 3 ^ 40 * 4247811 * 2
def baseEnd_4247811 : Nat := 2181168772455785153627179

theorem tailTrace_4247811 : CollatzResearch.WordTrace tailWord_4247811 prefixEnd_4247811 2181168772455785153627179 := by
  unfold tailWord_4247811
  simp only [CollatzResearch.WordTrace]
  refine ⟨154930395213913690206423287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103286930142609126804282191 154930395213913690206423287)
  ·
    refine ⟨232395592820870535309634931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154930395213913690206423287 232395592820870535309634931)
    ·
      refine ⟨348593389231305802964452397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232395592820870535309634931 348593389231305802964452397)
      ·
        refine ⟨130722520961739676111669649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348593389231305802964452397 130722520961739676111669649)
        ·
          refine ⟨98041890721304757083752237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130722520961739676111669649 98041890721304757083752237)
          ·
            refine ⟨36765709020489283906407089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98041890721304757083752237 36765709020489283906407089)
            ·
              refine ⟨27574281765366962929805317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36765709020489283906407089 27574281765366962929805317)
              ·
                refine ⟨5170177831006305549338497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27574281765366962929805317 5170177831006305549338497)
                ·
                  refine ⟨3877633373254729162003873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5170177831006305549338497 3877633373254729162003873)
                  ·
                    refine ⟨2908225029941046871502905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877633373254729162003873 2908225029941046871502905)
                    ·
                      refine ⟨2181168772455785153627179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908225029941046871502905 2181168772455785153627179)
                      ·
                        rfl

theorem cell23_4247811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_4247811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247811 prefixEnd_4247811 := by exact prefixLift 4247811
  have htrace : WordTrace (prefixWord ++ tailWord_4247811) baseStart_4247811 baseEnd_4247811 := by
    simpa [prefixWord, tailWord_4247811, baseEnd_4247811] using wordTrace_append hprefix tailTrace_4247811
  have hstable : (prefixWord ++ tailWord_4247811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247811).length < 2 ^ (prefixWord ++ tailWord_4247811).sum := by decide
  have hdescent : baseEnd_4247811 < baseStart_4247811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247817 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 7]
def baseStart_4247817 : Nat := 118140960795 + 4247817 * 2 ^ 59
def prefixEnd_4247817 : Nat := 4983230072969 + 3 ^ 40 * 4247817 * 2
def baseEnd_4247817 : Nat := 242352428148856903350239

theorem tailTrace_4247817 : CollatzResearch.WordTrace tailWord_4247817 prefixEnd_4247817 242352428148856903350239 := by
  unfold tailWord_4247817
  simp only [CollatzResearch.WordTrace]
  refine ⟨154930614051891953231141705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103287076034594635487427803 154930614051891953231141705)
  ·
    refine ⟨116197960538918964923356279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154930614051891953231141705 116197960538918964923356279)
    ·
      refine ⟨174296940808378447385034419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116197960538918964923356279 174296940808378447385034419)
      ·
        refine ⟨261445411212567671077551629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174296940808378447385034419 261445411212567671077551629)
        ·
          refine ⟨98042029204712876654081861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261445411212567671077551629 98042029204712876654081861)
          ·
            refine ⟨18382880475883664372640349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98042029204712876654081861 18382880475883664372640349)
            ·
              refine ⟨6893580178456374139740131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18382880475883664372640349 6893580178456374139740131)
              ·
                refine ⟨10340370267684561209610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6893580178456374139740131 10340370267684561209610197)
                ·
                  refine ⟨242352428148856903350239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10340370267684561209610197 242352428148856903350239)
                  ·
                    rfl

theorem cell23_4247817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_4247817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247817 prefixEnd_4247817 := by exact prefixLift 4247817
  have htrace : WordTrace (prefixWord ++ tailWord_4247817) baseStart_4247817 baseEnd_4247817 := by
    simpa [prefixWord, tailWord_4247817, baseEnd_4247817] using wordTrace_append hprefix tailTrace_4247817
  have hstable : (prefixWord ++ tailWord_4247817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247817).length < 2 ^ (prefixWord ++ tailWord_4247817).sum := by decide
  have hdescent : baseEnd_4247817 < baseStart_4247817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247827 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3]
def baseStart_4247827 : Nat := 118140960795 + 4247827 * 2 ^ 59
def prefixEnd_4247827 : Nat := 4983230072969 + 3 ^ 40 * 4247827 * 2
def baseEnd_4247827 : Nat := 2181176988146257091027105

theorem tailTrace_4247827 : CollatzResearch.WordTrace tailWord_4247827 prefixEnd_4247827 2181176988146257091027105 := by
  unfold tailWord_4247827
  simp only [CollatzResearch.WordTrace]
  refine ⟨154930978781855724939005735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103287319187903816626003823 154930978781855724939005735)
  ·
    refine ⟨232396468172783587408508603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154930978781855724939005735 232396468172783587408508603)
    ·
      refine ⟨348594702259175381112762905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232396468172783587408508603 348594702259175381112762905)
      ·
        refine ⟨261446026694381535834572179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348594702259175381112762905 261446026694381535834572179)
        ·
          refine ⟨392169040041572303751858269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261446026694381535834572179 392169040041572303751858269)
          ·
            refine ⟨147063390015589613906946851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392169040041572303751858269 147063390015589613906946851)
            ·
              refine ⟨220595085023384420860420277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147063390015589613906946851 220595085023384420860420277)
              ·
                refine ⟨20680789220942289455664401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220595085023384420860420277 20680789220942289455664401)
                ·
                  refine ⟨15510591915706717091748301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20680789220942289455664401 15510591915706717091748301)
                  ·
                    refine ⟨5816471968390018909405613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15510591915706717091748301 5816471968390018909405613)
                    ·
                      refine ⟨2181176988146257091027105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816471968390018909405613 2181176988146257091027105)
                      ·
                        rfl

theorem cell23_4247827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_4247827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247827 prefixEnd_4247827 := by exact prefixLift 4247827
  have htrace : WordTrace (prefixWord ++ tailWord_4247827) baseStart_4247827 baseEnd_4247827 := by
    simpa [prefixWord, tailWord_4247827, baseEnd_4247827] using wordTrace_append hprefix tailTrace_4247827
  have hstable : (prefixWord ++ tailWord_4247827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247827).length < 2 ^ (prefixWord ++ tailWord_4247827).sum := by decide
  have hdescent : baseEnd_4247827 < baseStart_4247827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247907 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 8]
def baseStart_4247907 : Nat := 118140960795 + 4247907 * 2 ^ 59
def prefixEnd_4247907 : Nat := 4983230072969 + 3 ^ 40 * 4247907 * 2
def baseEnd_4247907 : Nat := 242357562955401864225193

theorem tailTrace_4247907 : CollatzResearch.WordTrace tailWord_4247907 prefixEnd_4247907 242357562955401864225193 := by
  unfold tailWord_4247907
  simp only [CollatzResearch.WordTrace]
  refine ⟨154933896621565898601917975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103289264414377265734611983 154933896621565898601917975)
  ·
    refine ⟨232400844932348847902876963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154933896621565898601917975 232400844932348847902876963)
    ·
      refine ⟨348601267398523271854315445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232400844932348847902876963 348601267398523271854315445)
      ·
        refine ⟨32681368818611556736342073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 348601267398523271854315445 32681368818611556736342073)
        ·
          refine ⟨24511026613958667552256555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32681368818611556736342073 24511026613958667552256555)
          ·
            refine ⟨36766539920938001328384833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24511026613958667552256555 36766539920938001328384833)
            ·
              refine ⟨27574904940703500996288625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36766539920938001328384833 27574904940703500996288625)
              ·
                refine ⟨20681178705527625747216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27574904940703500996288625 20681178705527625747216469)
                ·
                  refine ⟨242357562955401864225193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20681178705527625747216469 242357562955401864225193)
                  ·
                    rfl

theorem cell23_4247907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 8].length) (baseStart_4247907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247907 prefixEnd_4247907 := by exact prefixLift 4247907
  have htrace : WordTrace (prefixWord ++ tailWord_4247907) baseStart_4247907 baseEnd_4247907 := by
    simpa [prefixWord, tailWord_4247907, baseEnd_4247907] using wordTrace_append hprefix tailTrace_4247907
  have hstable : (prefixWord ++ tailWord_4247907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247907).length < 2 ^ (prefixWord ++ tailWord_4247907).sum := by decide
  have hdescent : baseEnd_4247907 < baseStart_4247907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247914 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4247914 : Nat := 118140960795 + 4247914 * 2 ^ 59
def prefixEnd_4247914 : Nat := 4983230072969 + 3 ^ 40 * 4247914 * 2
def baseEnd_4247914 : Nat := 2181221660963198250639205

theorem tailTrace_4247914 : CollatzResearch.WordTrace tailWord_4247914 prefixEnd_4247914 2181221660963198250639205 := by
  unfold tailWord_4247914
  simp only [CollatzResearch.WordTrace]
  refine ⟨38733537983135134699355699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103289434621693692531615197 38733537983135134699355699)
  ·
    refine ⟨58100306974702702049033549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38733537983135134699355699 58100306974702702049033549)
    ·
      refine ⟨21787615115513513268387581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58100306974702702049033549 21787615115513513268387581)
      ·
        refine ⟨8170355668317567475645343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21787615115513513268387581 8170355668317567475645343)
        ·
          refine ⟨12255533502476351213468015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8170355668317567475645343 12255533502476351213468015)
          ·
            refine ⟨18383300253714526820202023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12255533502476351213468015 18383300253714526820202023)
            ·
              refine ⟨27574950380571790230303035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18383300253714526820202023 27574950380571790230303035)
              ·
                refine ⟨41362425570857685345454553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27574950380571790230303035 41362425570857685345454553)
                ·
                  refine ⟨31021819178143264009090915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41362425570857685345454553 31021819178143264009090915)
                  ·
                    refine ⟨46532728767214896013636373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31021819178143264009090915 46532728767214896013636373)
                    ·
                      refine ⟨2181221660963198250639205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46532728767214896013636373 2181221660963198250639205)
                      ·
                        rfl

theorem cell23_4247914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4247914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247914 prefixEnd_4247914 := by exact prefixLift 4247914
  have htrace : WordTrace (prefixWord ++ tailWord_4247914) baseStart_4247914 baseEnd_4247914 := by
    simpa [prefixWord, tailWord_4247914, baseEnd_4247914] using wordTrace_append hprefix tailTrace_4247914
  have hstable : (prefixWord ++ tailWord_4247914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247914).length < 2 ^ (prefixWord ++ tailWord_4247914).sum := by decide
  have hdescent : baseEnd_4247914 < baseStart_4247914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4247961 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 2, 3, 2]
def baseStart_4247961 : Nat := 118140960795 + 4247961 * 2 ^ 59
def prefixEnd_4247961 : Nat := 4983230072969 + 3 ^ 40 * 4247961 * 2
def baseEnd_4247961 : Nat := 2181245794553959566751489

theorem tailTrace_4247961 : CollatzResearch.WordTrace tailWord_4247961 prefixEnd_4247961 2181245794553959566751489 := by
  unfold tailWord_4247961
  simp only [CollatzResearch.WordTrace]
  refine ⟨154935866163370265824383737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103290577442246843882922491 154935866163370265824383737)
  ·
    refine ⟨116201899622527699368287803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154935866163370265824383737 116201899622527699368287803)
    ·
      refine ⟨174302849433791549052431705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116201899622527699368287803 174302849433791549052431705)
      ·
        refine ⟨130727137075343661789323779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174302849433791549052431705 130727137075343661789323779)
        ·
          refine ⟨196090705613015492683985669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130727137075343661789323779 196090705613015492683985669)
          ·
            refine ⟨36767007302440404878247313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196090705613015492683985669 36767007302440404878247313)
            ·
              refine ⟨27575255476830303658685485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36767007302440404878247313 27575255476830303658685485)
              ·
                refine ⟨10340720803811363872007057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27575255476830303658685485 10340720803811363872007057)
                ·
                  refine ⟨7755540602858522904005293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10340720803811363872007057 7755540602858522904005293)
                  ·
                    refine ⟨2908327726071946089001985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7755540602858522904005293 2908327726071946089001985)
                    ·
                      refine ⟨2181245794553959566751489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908327726071946089001985 2181245794553959566751489)
                      ·
                        rfl

theorem cell23_4247961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_4247961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4247961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4247961 prefixEnd_4247961 := by exact prefixLift 4247961
  have htrace : WordTrace (prefixWord ++ tailWord_4247961) baseStart_4247961 baseEnd_4247961 := by
    simpa [prefixWord, tailWord_4247961, baseEnd_4247961] using wordTrace_append hprefix tailTrace_4247961
  have hstable : (prefixWord ++ tailWord_4247961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4247961).length < 2 ^ (prefixWord ++ tailWord_4247961).sum := by decide
  have hdescent : baseEnd_4247961 < baseStart_4247961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4247961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248008 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_4248008 : Nat := 118140960795 + 4248008 * 2 ^ 59
def prefixEnd_4248008 : Nat := 4983230072969 + 3 ^ 40 * 4248008 * 2
def baseEnd_4248008 : Nat := 2181269928144720882863773

theorem tailTrace_4248008 : CollatzResearch.WordTrace tailWord_4248008 prefixEnd_4248008 2181269928144720882863773 := by
  unfold tailWord_4248008
  simp only [CollatzResearch.WordTrace]
  refine ⟨77468790197099996425672339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103291720262799995234229785 77468790197099996425672339)
  ·
    refine ⟨116203185295649994638508509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77468790197099996425672339 116203185295649994638508509)
    ·
      refine ⟨43576194485868747989440691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116203185295649994638508509 43576194485868747989440691)
      ·
        refine ⟨65364291728803121984161037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43576194485868747989440691 65364291728803121984161037)
        ·
          refine ⟨24511609398301170744060389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65364291728803121984161037 24511609398301170744060389)
          ·
            refine ⟨4595926762181469514511323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24511609398301170744060389 4595926762181469514511323)
            ·
              refine ⟨6893890143272204271766985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595926762181469514511323 6893890143272204271766985)
              ·
                refine ⟨5170417607454153203825239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6893890143272204271766985 5170417607454153203825239)
                ·
                  refine ⟨7755626411181229805737859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170417607454153203825239 7755626411181229805737859)
                  ·
                    refine ⟨11633439616771844708606789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7755626411181229805737859 11633439616771844708606789)
                    ·
                      refine ⟨2181269928144720882863773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11633439616771844708606789 2181269928144720882863773)
                      ·
                        rfl

theorem cell23_4248008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_4248008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248008 prefixEnd_4248008 := by exact prefixLift 4248008
  have htrace : WordTrace (prefixWord ++ tailWord_4248008) baseStart_4248008 baseEnd_4248008 := by
    simpa [prefixWord, tailWord_4248008, baseEnd_4248008] using wordTrace_append hprefix tailTrace_4248008
  have hstable : (prefixWord ++ tailWord_4248008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248008).length < 2 ^ (prefixWord ++ tailWord_4248008).sum := by decide
  have hdescent : baseEnd_4248008 < baseStart_4248008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248018 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4248018 : Nat := 118140960795 + 4248018 * 2 ^ 59
def prefixEnd_4248018 : Nat := 4983230072969 + 3 ^ 40 * 4248018 * 2
def baseEnd_4248018 : Nat := 727091687650421947912909

theorem tailTrace_4248018 : CollatzResearch.WordTrace tailWord_4248018 prefixEnd_4248018 727091687650421947912909 := by
  unfold tailWord_4248018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734486281040941139802177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103291963416109176372805805 38734486281040941139802177)
  ·
    refine ⟨29050864710780705854851633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38734486281040941139802177 29050864710780705854851633)
    ·
      refine ⟨21788148533085529391138725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29050864710780705854851633 21788148533085529391138725)
      ·
        refine ⟨4085277849953536760838511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21788148533085529391138725 4085277849953536760838511)
        ·
          refine ⟨6127916774930305141257767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085277849953536760838511 6127916774930305141257767)
          ·
            refine ⟨9191875162395457711886651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127916774930305141257767 9191875162395457711886651)
            ·
              refine ⟨13787812743593186567829977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191875162395457711886651 13787812743593186567829977)
              ·
                refine ⟨10340859557694889925872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13787812743593186567829977 10340859557694889925872483)
                ·
                  refine ⟨15511289336542334888808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10340859557694889925872483 15511289336542334888808725)
                  ·
                    refine ⟨727091687650421947912909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15511289336542334888808725 727091687650421947912909)
                    ·
                      rfl

theorem cell23_4248018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4248018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248018 prefixEnd_4248018 := by exact prefixLift 4248018
  have htrace : WordTrace (prefixWord ++ tailWord_4248018) baseStart_4248018 baseEnd_4248018 := by
    simpa [prefixWord, tailWord_4248018, baseEnd_4248018] using wordTrace_append hprefix tailTrace_4248018
  have hstable : (prefixWord ++ tailWord_4248018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248018).length < 2 ^ (prefixWord ++ tailWord_4248018).sum := by decide
  have hdescent : baseEnd_4248018 < baseStart_4248018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248021 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4248021 : Nat := 118140960795 + 4248021 * 2 ^ 59
def prefixEnd_4248021 : Nat := 4983230072969 + 3 ^ 40 * 4248021 * 2
def baseEnd_4248021 : Nat := 2181276603393229332001213

theorem tailTrace_4248021 : CollatzResearch.WordTrace tailWord_4248021 prefixEnd_4248021 2181276603393229332001213 := by
  unfold tailWord_4248021
  simp only [CollatzResearch.WordTrace]
  refine ⟨154938054543152896071567917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103292036362101930714378611 154938054543152896071567917)
  ·
    refine ⟨58101770453682336026837969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154938054543152896071567917 58101770453682336026837969)
    ·
      refine ⟨43576327840261752020128477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58101770453682336026837969 43576327840261752020128477)
      ·
        refine ⟨16341122940098157007548179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43576327840261752020128477 16341122940098157007548179)
        ·
          refine ⟨24511684410147235511322269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16341122940098157007548179 24511684410147235511322269)
          ·
            refine ⟨9191881653805213316745851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24511684410147235511322269 9191881653805213316745851)
            ·
              refine ⟨13787822480707819975118777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191881653805213316745851 13787822480707819975118777)
              ·
                refine ⟨10340866860530864981339083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13787822480707819975118777 10340866860530864981339083)
                ·
                  refine ⟨15511300290796297472008625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10340866860530864981339083 15511300290796297472008625)
                  ·
                    refine ⟨11633475218097223104006469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15511300290796297472008625 11633475218097223104006469)
                    ·
                      refine ⟨2181276603393229332001213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11633475218097223104006469 2181276603393229332001213)
                      ·
                        rfl

theorem cell23_4248021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4248021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248021 prefixEnd_4248021 := by exact prefixLift 4248021
  have htrace : WordTrace (prefixWord ++ tailWord_4248021) baseStart_4248021 baseEnd_4248021 := by
    simpa [prefixWord, tailWord_4248021, baseEnd_4248021] using wordTrace_append hprefix tailTrace_4248021
  have hstable : (prefixWord ++ tailWord_4248021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248021).length < 2 ^ (prefixWord ++ tailWord_4248021).sum := by decide
  have hdescent : baseEnd_4248021 < baseStart_4248021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248025 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 1, 2, 2]
def baseStart_4248025 : Nat := 118140960795 + 4248025 * 2 ^ 59
def prefixEnd_4248025 : Nat := 4983230072969 + 3 ^ 40 * 4248025 * 2
def baseEnd_4248025 : Nat := 2181278657315847316351195

theorem tailTrace_4248025 : CollatzResearch.WordTrace tailWord_4248025 prefixEnd_4248025 2181278657315847316351195 := by
  unfold tailWord_4248025
  simp only [CollatzResearch.WordTrace]
  refine ⟨154938200435138404754713529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103292133623425603169809019 154938200435138404754713529)
  ·
    refine ⟨116203650326353803566035147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154938200435138404754713529 116203650326353803566035147)
    ·
      refine ⟨174305475489530705349052721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116203650326353803566035147 174305475489530705349052721)
      ·
        refine ⟨130729106617148029011789541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174305475489530705349052721 130729106617148029011789541)
        ·
          refine ⟨24511707490715255439710539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130729106617148029011789541 24511707490715255439710539)
          ·
            refine ⟨36767561236072883159565809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24511707490715255439710539 36767561236072883159565809)
            ·
              refine ⟨27575670927054662369674357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36767561236072883159565809 27575670927054662369674357)
              ·
                refine ⟨2585219149411374597156971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27575670927054662369674357 2585219149411374597156971)
                ·
                  refine ⟨3877828724117061895735457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585219149411374597156971 3877828724117061895735457)
                  ·
                    refine ⟨2908371543087796421801593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877828724117061895735457 2908371543087796421801593)
                    ·
                      refine ⟨2181278657315847316351195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908371543087796421801593 2181278657315847316351195)
                      ·
                        rfl

theorem cell23_4248025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_4248025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248025 prefixEnd_4248025 := by exact prefixLift 4248025
  have htrace : WordTrace (prefixWord ++ tailWord_4248025) baseStart_4248025 baseEnd_4248025 := by
    simpa [prefixWord, tailWord_4248025, baseEnd_4248025] using wordTrace_append hprefix tailTrace_4248025
  have hstable : (prefixWord ++ tailWord_4248025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248025).length < 2 ^ (prefixWord ++ tailWord_4248025).sum := by decide
  have hdescent : baseEnd_4248025 < baseStart_4248025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248042 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_4248042 : Nat := 118140960795 + 4248042 * 2 ^ 59
def prefixEnd_4248042 : Nat := 4983230072969 + 3 ^ 40 * 4248042 * 2
def baseEnd_4248042 : Nat := 2181287386486973749838617

theorem tailTrace_4248042 : CollatzResearch.WordTrace tailWord_4248042 prefixEnd_4248042 2181287386486973749838617 := by
  unfold tailWord_4248042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734705119019204164520595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103292546984051211105388253 38734705119019204164520595)
  ·
    refine ⟨58102057678528806246780893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38734705119019204164520595 58102057678528806246780893)
    ·
      refine ⟨21788271629448302342542835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58102057678528806246780893 21788271629448302342542835)
      ·
        refine ⟨32682407444172453513814253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21788271629448302342542835 32682407444172453513814253)
        ·
          refine ⟨12255902791564670067680345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32682407444172453513814253 12255902791564670067680345)
          ·
            refine ⟨9191927093673502550760259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12255902791564670067680345 9191927093673502550760259)
            ·
              refine ⟨13787890640510253826140389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191927093673502550760259 13787890640510253826140389)
              ·
                refine ⟨2585229495095672592401323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13787890640510253826140389 2585229495095672592401323)
                ·
                  refine ⟨3877844242643508888601985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585229495095672592401323 3877844242643508888601985)
                  ·
                    refine ⟨2908383181982631666451489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877844242643508888601985 2908383181982631666451489)
                    ·
                      refine ⟨2181287386486973749838617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908383181982631666451489 2181287386486973749838617)
                      ·
                        rfl

theorem cell23_4248042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_4248042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248042 prefixEnd_4248042 := by exact prefixLift 4248042
  have htrace : WordTrace (prefixWord ++ tailWord_4248042) baseStart_4248042 baseEnd_4248042 := by
    simpa [prefixWord, tailWord_4248042, baseEnd_4248042] using wordTrace_append hprefix tailTrace_4248042
  have hstable : (prefixWord ++ tailWord_4248042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248042).length < 2 ^ (prefixWord ++ tailWord_4248042).sum := by decide
  have hdescent : baseEnd_4248042 < baseStart_4248042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248051 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 5, 3, 2]
def baseStart_4248051 : Nat := 118140960795 + 4248051 * 2 ^ 59
def prefixEnd_4248051 : Nat := 4983230072969 + 3 ^ 40 * 4248051 * 2
def baseEnd_4248051 : Nat := 2181292007812864214626075

theorem tailTrace_4248051 : CollatzResearch.WordTrace tailWord_4248051 prefixEnd_4248051 2181292007812864214626075 := by
  unfold tailWord_4248051
  simp only [CollatzResearch.WordTrace]
  refine ⟨154939148733044211195160007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103292765822029474130106671 154939148733044211195160007)
  ·
    refine ⟨232408723099566316792740011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154939148733044211195160007 232408723099566316792740011)
    ·
      refine ⟨348613084649349475189110017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232408723099566316792740011 348613084649349475189110017)
      ·
        refine ⟨261459813487012106391832513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348613084649349475189110017 261459813487012106391832513)
        ·
          refine ⟨196094860115259079793874385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261459813487012106391832513 196094860115259079793874385)
          ·
            refine ⟨147071145086444309845405789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196094860115259079793874385 147071145086444309845405789)
            ·
              refine ⟨55151679407416616192027171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147071145086444309845405789 55151679407416616192027171)
              ·
                refine ⟨82727519111124924288040757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55151679407416616192027171 82727519111124924288040757)
                ·
                  refine ⟨7755704916667961652003821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82727519111124924288040757 7755704916667961652003821)
                  ·
                    refine ⟨2908389343750485619501433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7755704916667961652003821 2908389343750485619501433)
                    ·
                      refine ⟨2181292007812864214626075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908389343750485619501433 2181292007812864214626075)
                      ·
                        rfl

theorem cell23_4248051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3, 2].length) (baseStart_4248051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248051 prefixEnd_4248051 := by exact prefixLift 4248051
  have htrace : WordTrace (prefixWord ++ tailWord_4248051) baseStart_4248051 baseEnd_4248051 := by
    simpa [prefixWord, tailWord_4248051, baseEnd_4248051] using wordTrace_append hprefix tailTrace_4248051
  have hstable : (prefixWord ++ tailWord_4248051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248051).length < 2 ^ (prefixWord ++ tailWord_4248051).sum := by decide
  have hdescent : baseEnd_4248051 < baseStart_4248051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248074 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4248074 : Nat := 118140960795 + 4248074 * 2 ^ 59
def prefixEnd_4248074 : Nat := 4983230072969 + 3 ^ 40 * 4248074 * 2
def baseEnd_4248074 : Nat := 727101272622639208212823

theorem tailTrace_4248074 : CollatzResearch.WordTrace tailWord_4248074 prefixEnd_4248074 727101272622639208212823 := by
  unfold tailWord_4248074
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734996902990221530811819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103293325074640590748831517 38734996902990221530811819)
  ·
    refine ⟨58102495354485332296217729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38734996902990221530811819 58102495354485332296217729)
    ·
      refine ⟨43576871515863999222163297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58102495354485332296217729 43576871515863999222163297)
      ·
        refine ⟨32682653636897999416622473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43576871515863999222163297 32682653636897999416622473)
        ·
          refine ⟨24511990227673499562466855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32682653636897999416622473 24511990227673499562466855)
          ·
            refine ⟨36767985341510249343700283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24511990227673499562466855 36767985341510249343700283)
            ·
              refine ⟨55151978012265374015550425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36767985341510249343700283 55151978012265374015550425)
              ·
                refine ⟨41363983509199030511662819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55151978012265374015550425 41363983509199030511662819)
                ·
                  refine ⟨62045975263798545767494229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41363983509199030511662819 62045975263798545767494229)
                  ·
                    refine ⟨727101272622639208212823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62045975263798545767494229 727101272622639208212823)
                    ·
                      rfl

theorem cell23_4248074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4248074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248074 prefixEnd_4248074 := by exact prefixLift 4248074
  have htrace : WordTrace (prefixWord ++ tailWord_4248074) baseStart_4248074 baseEnd_4248074 := by
    simpa [prefixWord, tailWord_4248074, baseEnd_4248074] using wordTrace_append hprefix tailTrace_4248074
  have hstable : (prefixWord ++ tailWord_4248074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248074).length < 2 ^ (prefixWord ++ tailWord_4248074).sum := by decide
  have hdescent : baseEnd_4248074 < baseStart_4248074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248081 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_4248081 : Nat := 118140960795 + 4248081 * 2 ^ 59
def prefixEnd_4248081 : Nat := 4983230072969 + 3 ^ 40 * 4248081 * 2
def baseEnd_4248081 : Nat := 2181307412232499097250937

theorem tailTrace_4248081 : CollatzResearch.WordTrace tailWord_4248081 prefixEnd_4248081 2181307412232499097250937 := by
  unfold tailWord_4248081
  simp only [CollatzResearch.WordTrace]
  refine ⟨154940242922935526318752097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103293495281957017545834731 154940242922935526318752097)
  ·
    refine ⟨116205182192201644739064073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154940242922935526318752097 116205182192201644739064073)
    ·
      refine ⟨87153886644151233554298055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116205182192201644739064073 87153886644151233554298055)
      ·
        refine ⟨130730829966226850331447083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87153886644151233554298055 130730829966226850331447083)
        ·
          refine ⟨196096244949340275497170625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130730829966226850331447083 196096244949340275497170625)
          ·
            refine ⟨147072183712005206622877969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196096244949340275497170625 147072183712005206622877969)
            ·
              refine ⟨110304137784003904967158477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147072183712005206622877969 110304137784003904967158477)
              ·
                refine ⟨41364051669001464362684429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110304137784003904967158477 41364051669001464362684429)
                ·
                  refine ⟨15511519375875549136006661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41364051669001464362684429 15511519375875549136006661)
                  ·
                    refine ⟨2908409882976665463001249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15511519375875549136006661 2908409882976665463001249)
                    ·
                      refine ⟨2181307412232499097250937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908409882976665463001249 2181307412232499097250937)
                      ·
                        rfl

theorem cell23_4248081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_4248081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248081 prefixEnd_4248081 := by exact prefixLift 4248081
  have htrace : WordTrace (prefixWord ++ tailWord_4248081) baseStart_4248081 baseEnd_4248081 := by
    simpa [prefixWord, tailWord_4248081, baseEnd_4248081] using wordTrace_append hprefix tailTrace_4248081
  have hstable : (prefixWord ++ tailWord_4248081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248081).length < 2 ^ (prefixWord ++ tailWord_4248081).sum := by decide
  have hdescent : baseEnd_4248081 < baseStart_4248081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248109 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4248109 : Nat := 118140960795 + 4248109 * 2 ^ 59
def prefixEnd_4248109 : Nat := 4983230072969 + 3 ^ 40 * 4248109 * 2
def baseEnd_4248109 : Nat := 2181321789690824987700809

theorem tailTrace_4248109 : CollatzResearch.WordTrace tailWord_4248109 prefixEnd_4248109 2181321789690824987700809 := by
  unfold tailWord_4248109
  simp only [CollatzResearch.WordTrace]
  refine ⟨154941264166834087100771381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103294176111222724733847587 154941264166834087100771381)
  ·
    refine ⟨14525743515640695665697317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154941264166834087100771381 14525743515640695665697317)
    ·
      refine ⟨2723576909182630437318247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14525743515640695665697317 2723576909182630437318247)
      ·
        refine ⟨4085365363773945655977371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723576909182630437318247 4085365363773945655977371)
        ·
          refine ⟨6128048045660918483966057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085365363773945655977371 6128048045660918483966057)
          ·
            refine ⟨4596036034245688862974543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6128048045660918483966057 4596036034245688862974543)
            ·
              refine ⟨6894054051368533294461815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596036034245688862974543 6894054051368533294461815)
              ·
                refine ⟨10341081077052799941692723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6894054051368533294461815 10341081077052799941692723)
                ·
                  refine ⟨15511621615579199912539085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10341081077052799941692723 15511621615579199912539085)
                  ·
                    refine ⟨5816858105842199967202157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15511621615579199912539085 5816858105842199967202157)
                    ·
                      refine ⟨2181321789690824987700809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5816858105842199967202157 2181321789690824987700809)
                      ·
                        rfl

theorem cell23_4248109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4248109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248109 prefixEnd_4248109 := by exact prefixLift 4248109
  have htrace : WordTrace (prefixWord ++ tailWord_4248109) baseStart_4248109 baseEnd_4248109 := by
    simpa [prefixWord, tailWord_4248109, baseEnd_4248109] using wordTrace_append hprefix tailTrace_4248109
  have hstable : (prefixWord ++ tailWord_4248109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248109).length < 2 ^ (prefixWord ++ tailWord_4248109).sum := by decide
  have hdescent : baseEnd_4248109 < baseStart_4248109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248138 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_4248138 : Nat := 118140960795 + 4248138 * 2 ^ 59
def prefixEnd_4248138 : Nat := 4983230072969 + 3 ^ 40 * 4248138 * 2
def baseEnd_4248138 : Nat := 242370742292200597137575

theorem tailTrace_4248138 : CollatzResearch.WordTrace tailWord_4248138 prefixEnd_4248138 242370742292200597137575 := by
  unfold tailWord_4248138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38735580470932256263394267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103294881255819350035718045 38735580470932256263394267)
  ·
    refine ⟨58103370706398384395091401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38735580470932256263394267 58103370706398384395091401)
    ·
      refine ⟨43577528029798788296318551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58103370706398384395091401 43577528029798788296318551)
      ·
        refine ⟨65366292044698182444477827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43577528029798788296318551 65366292044698182444477827)
        ·
          refine ⟨98049438067047273666716741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65366292044698182444477827 98049438067047273666716741)
          ·
            refine ⟨18384269637571363812509389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98049438067047273666716741 18384269637571363812509389)
            ·
              refine ⟨6894101114089261429691021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18384269637571363812509389 6894101114089261429691021)
              ·
                refine ⟨2585287917783473036134133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6894101114089261429691021 2585287917783473036134133)
                ·
                  refine ⟨242370742292200597137575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585287917783473036134133 242370742292200597137575)
                  ·
                    rfl

theorem cell23_4248138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_4248138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248138 prefixEnd_4248138 := by exact prefixLift 4248138
  have htrace : WordTrace (prefixWord ++ tailWord_4248138) baseStart_4248138 baseEnd_4248138 := by
    simpa [prefixWord, tailWord_4248138, baseEnd_4248138] using wordTrace_append hprefix tailTrace_4248138
  have hstable : (prefixWord ++ tailWord_4248138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248138).length < 2 ^ (prefixWord ++ tailWord_4248138).sum := by decide
  have hdescent : baseEnd_4248138 < baseStart_4248138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248151 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 2, 5]
def baseStart_4248151 : Nat := 118140960795 + 4248151 * 2 ^ 59
def prefixEnd_4248151 : Nat := 4983230072969 + 3 ^ 40 * 4248151 * 2
def baseEnd_4248151 : Nat := 727114451959437941125205

theorem tailTrace_4248151 : CollatzResearch.WordTrace tailWord_4248151 prefixEnd_4248151 727114451959437941125205 := by
  unfold tailWord_4248151
  simp only [CollatzResearch.WordTrace]
  refine ⟨154942796032681928273800307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103295197355121285515866871 154942796032681928273800307)
  ·
    refine ⟨232414194049022892410700461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154942796032681928273800307 232414194049022892410700461)
    ·
      refine ⟨87155322768383584654012673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232414194049022892410700461 87155322768383584654012673)
      ·
        refine ⟨65366492076287688490509505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87155322768383584654012673 65366492076287688490509505)
        ·
          refine ⟨49024869057215766367882129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65366492076287688490509505 49024869057215766367882129)
          ·
            refine ⟨36768651792911824775911597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49024869057215766367882129 36768651792911824775911597)
            ·
              refine ⟨13788244422341934290966849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36768651792911824775911597 13788244422341934290966849)
              ·
                refine ⟨10341183316756450718225137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13788244422341934290966849 10341183316756450718225137)
                ·
                  refine ⟨7755887487567338038668853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10341183316756450718225137 7755887487567338038668853)
                  ·
                    refine ⟨727114451959437941125205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7755887487567338038668853 727114451959437941125205)
                    ·
                      rfl

theorem cell23_4248151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_4248151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248151 prefixEnd_4248151 := by exact prefixLift 4248151
  have htrace : WordTrace (prefixWord ++ tailWord_4248151) baseStart_4248151 baseEnd_4248151 := by
    simpa [prefixWord, tailWord_4248151, baseEnd_4248151] using wordTrace_append hprefix tailTrace_4248151
  have hstable : (prefixWord ++ tailWord_4248151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248151).length < 2 ^ (prefixWord ++ tailWord_4248151).sum := by decide
  have hdescent : baseEnd_4248151 < baseStart_4248151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_4248154 : Nat := 118140960795 + 4248154 * 2 ^ 59
def prefixEnd_4248154 : Nat := 4983230072969 + 3 ^ 40 * 4248154 * 2
def baseEnd_4248154 : Nat := 2181344896320277311638101

theorem tailTrace_4248154 : CollatzResearch.WordTrace tailWord_4248154 prefixEnd_4248154 2181344896320277311638101 := by
  unfold tailWord_4248154
  simp only [CollatzResearch.WordTrace]
  refine ⟨38735726362917764946539879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103295270301114039857439677 38735726362917764946539879)
  ·
    refine ⟨58103589544376647419809819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38735726362917764946539879 58103589544376647419809819)
    ·
      refine ⟨87155384316564971129714729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58103589544376647419809819 87155384316564971129714729)
      ·
        refine ⟨65366538237423728347286047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87155384316564971129714729 65366538237423728347286047)
        ·
          refine ⟨98049807356135592520929071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65366538237423728347286047 98049807356135592520929071)
          ·
            refine ⟨147074711034203388781393607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98049807356135592520929071 147074711034203388781393607)
            ·
              refine ⟨220612066551305083172090411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147074711034203388781393607 220612066551305083172090411)
              ·
                refine ⟨330918099826957624758135617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220612066551305083172090411 330918099826957624758135617)
                ·
                  refine ⟨248188574870218218568601713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330918099826957624758135617 248188574870218218568601713)
                  ·
                    refine ⟨186141431152663663926451285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248188574870218218568601713 186141431152663663926451285)
                    ·
                      refine ⟨2181344896320277311638101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 186141431152663663926451285 2181344896320277311638101)
                      ·
                        rfl

theorem cell23_4248154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_4248154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248154 prefixEnd_4248154 := by exact prefixLift 4248154
  have htrace : WordTrace (prefixWord ++ tailWord_4248154) baseStart_4248154 baseEnd_4248154 := by
    simpa [prefixWord, tailWord_4248154, baseEnd_4248154] using wordTrace_append hprefix tailTrace_4248154
  have hstable : (prefixWord ++ tailWord_4248154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248154).length < 2 ^ (prefixWord ++ tailWord_4248154).sum := by decide
  have hdescent : baseEnd_4248154 < baseStart_4248154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248161 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4248161 : Nat := 118140960795 + 4248161 * 2 ^ 59
def prefixEnd_4248161 : Nat := 4983230072969 + 3 ^ 40 * 4248161 * 2
def baseEnd_4248161 : Nat := 2181348490684858784250569

theorem tailTrace_4248161 : CollatzResearch.WordTrace tailWord_4248161 prefixEnd_4248161 2181348490684858784250569 := by
  unfold tailWord_4248161
  simp only [CollatzResearch.WordTrace]
  refine ⟨154943160762645699981664337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103295440508430466654442891 154943160762645699981664337)
  ·
    refine ⟨116207370571984274986248253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154943160762645699981664337 116207370571984274986248253)
    ·
      refine ⟨43577763964494103119843095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116207370571984274986248253 43577763964494103119843095)
      ·
        refine ⟨65366645946741154679764643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43577763964494103119843095 65366645946741154679764643)
        ·
          refine ⟨98049968920111732019646965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65366645946741154679764643 98049968920111732019646965)
          ·
            refine ⟨9192184586260474876841903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98049968920111732019646965 9192184586260474876841903)
            ·
              refine ⟨13788276879390712315262855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9192184586260474876841903 13788276879390712315262855)
              ·
                refine ⟨20682415319086068472894283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13788276879390712315262855 20682415319086068472894283)
                ·
                  refine ⟨31023622978629102709341425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20682415319086068472894283 31023622978629102709341425)
                  ·
                    refine ⟨23267717233971827032006069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31023622978629102709341425 23267717233971827032006069)
                    ·
                      refine ⟨2181348490684858784250569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23267717233971827032006069 2181348490684858784250569)
                      ·
                        rfl

theorem cell23_4248161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4248161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248161 prefixEnd_4248161 := by exact prefixLift 4248161
  have htrace : WordTrace (prefixWord ++ tailWord_4248161) baseStart_4248161 baseEnd_4248161 := by
    simpa [prefixWord, tailWord_4248161, baseEnd_4248161] using wordTrace_append hprefix tailTrace_4248161
  have hstable : (prefixWord ++ tailWord_4248161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248161).length < 2 ^ (prefixWord ++ tailWord_4248161).sum := by decide
  have hdescent : baseEnd_4248161 < baseStart_4248161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248215 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 1, 4]
def baseStart_4248215 : Nat := 118140960795 + 4248215 * 2 ^ 59
def prefixEnd_4248215 : Nat := 4983230072969 + 3 ^ 40 * 4248215 * 2
def baseEnd_4248215 : Nat := 727125406213400524325107

theorem tailTrace_4248215 : CollatzResearch.WordTrace tailWord_4248215 prefixEnd_4248215 727125406213400524325107 := by
  unfold tailWord_4248215
  simp only [CollatzResearch.WordTrace]
  refine ⟨154945130304450067204130099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103296753536300044802753399 154945130304450067204130099)
  ·
    refine ⟨232417695456675100806195149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154945130304450067204130099 232417695456675100806195149)
    ·
      refine ⟨87156635796253162802323181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232417695456675100806195149 87156635796253162802323181)
      ·
        refine ⟨32683738423594936050871193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87156635796253162802323181 32683738423594936050871193)
        ·
          refine ⟨24512803817696202038153395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32683738423594936050871193 24512803817696202038153395)
          ·
            refine ⟨36769205726544303057230093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24512803817696202038153395 36769205726544303057230093)
            ·
              refine ⟨13788452147454113646461285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36769205726544303057230093 13788452147454113646461285)
              ·
                refine ⟨2585334777647646308711491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13788452147454113646461285 2585334777647646308711491)
                ·
                  refine ⟨3878002166471469463067237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585334777647646308711491 3878002166471469463067237)
                  ·
                    refine ⟨727125406213400524325107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878002166471469463067237 727125406213400524325107)
                    ·
                      rfl

theorem cell23_4248215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_4248215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248215 prefixEnd_4248215 := by exact prefixLift 4248215
  have htrace : WordTrace (prefixWord ++ tailWord_4248215) baseStart_4248215 baseEnd_4248215 := by
    simpa [prefixWord, tailWord_4248215, baseEnd_4248215] using wordTrace_append hprefix tailTrace_4248215
  have hstable : (prefixWord ++ tailWord_4248215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248215).length < 2 ^ (prefixWord ++ tailWord_4248215).sum := by decide
  have hdescent : baseEnd_4248215 < baseStart_4248215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248262 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4248262 : Nat := 118140960795 + 4248262 * 2 ^ 59
def prefixEnd_4248262 : Nat := 4983230072969 + 3 ^ 40 * 4248262 * 2
def baseEnd_4248262 : Nat := 242377816914551432120845

theorem tailTrace_4248262 : CollatzResearch.WordTrace tailWord_4248262 prefixEnd_4248262 242377816914551432120845 := by
  unfold tailWord_4248262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842088891727493569721595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103297896356853196154060693 4842088891727493569721595)
  ·
    refine ⟨7263133337591240354582393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842088891727493569721595 7263133337591240354582393)
    ·
      refine ⟨5447350003193430265936795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7263133337591240354582393 5447350003193430265936795)
      ·
        refine ⟨8171025004790145398905193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447350003193430265936795 8171025004790145398905193)
        ·
          refine ⟨6128268753592609049178895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8171025004790145398905193 6128268753592609049178895)
          ·
            refine ⟨9192403130388913573768343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128268753592609049178895 9192403130388913573768343)
            ·
              refine ⟨13788604695583370360652515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9192403130388913573768343 13788604695583370360652515)
              ·
                refine ⟨20682907043375055540978773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13788604695583370360652515 20682907043375055540978773)
                ·
                  refine ⟨242377816914551432120845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20682907043375055540978773 242377816914551432120845)
                  ·
                    rfl

theorem cell23_4248262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4248262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248262 prefixEnd_4248262 := by exact prefixLift 4248262
  have htrace : WordTrace (prefixWord ++ tailWord_4248262) baseStart_4248262 baseEnd_4248262 := by
    simpa [prefixWord, tailWord_4248262, baseEnd_4248262] using wordTrace_append hprefix tailTrace_4248262
  have hstable : (prefixWord ++ tailWord_4248262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248262).length < 2 ^ (prefixWord ++ tailWord_4248262).sum := by decide
  have hdescent : baseEnd_4248262 < baseStart_4248262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248318 : List Nat := [4, 2, 2, 1, 2, 1, 11]
def baseStart_4248318 : Nat := 118140960795 + 4248318 * 2 ^ 59
def prefixEnd_4248318 : Nat := 4983230072969 + 3 ^ 40 * 4248318 * 2
def baseEnd_4248318 : Nat := 26931223545032279876387

theorem tailTrace_4248318 : CollatzResearch.WordTrace tailWord_4248318 prefixEnd_4248318 26931223545032279876387 := by
  unfold tailWord_4248318
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368610877884614474391201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103299258015384610530086405 19368610877884614474391201)
  ·
    refine ⟨14526458158413460855793401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19368610877884614474391201 14526458158413460855793401)
    ·
      refine ⟨10894843618810095641845051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14526458158413460855793401 10894843618810095641845051)
      ·
        refine ⟨16342265428215143462767577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894843618810095641845051 16342265428215143462767577)
        ·
          refine ⟨12256699071161357597075683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16342265428215143462767577 12256699071161357597075683)
          ·
            refine ⟨18385048606742036395613525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12256699071161357597075683 18385048606742036395613525)
            ·
              refine ⟨26931223545032279876387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18385048606742036395613525 26931223545032279876387)
              ·
                rfl

theorem cell23_4248318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 11].length) (baseStart_4248318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248318 prefixEnd_4248318 := by exact prefixLift 4248318
  have htrace : WordTrace (prefixWord ++ tailWord_4248318) baseStart_4248318 baseEnd_4248318 := by
    simpa [prefixWord, tailWord_4248318, baseEnd_4248318] using wordTrace_append hprefix tailTrace_4248318
  have hstable : (prefixWord ++ tailWord_4248318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248318).length < 2 ^ (prefixWord ++ tailWord_4248318).sum := by decide
  have hdescent : baseEnd_4248318 < baseStart_4248318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248331 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 7]
def baseStart_4248331 : Nat := 118140960795 + 4248331 * 2 ^ 59
def prefixEnd_4248331 : Nat := 4983230072969 + 3 ^ 40 * 4248331 * 2
def baseEnd_4248331 : Nat := 727145260798707706374929

theorem tailTrace_4248331 : CollatzResearch.WordTrace tailWord_4248331 prefixEnd_4248331 727145260798707706374929 := by
  unfold tailWord_4248331
  simp only [CollatzResearch.WordTrace]
  refine ⟨154949361172029819015352847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103299574114686546010235231 154949361172029819015352847)
  ·
    refine ⟨232424041758044728523029271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154949361172029819015352847 232424041758044728523029271)
    ·
      refine ⟨348636062637067092784543907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232424041758044728523029271 348636062637067092784543907)
      ·
        refine ⟨522954093955600639176815861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348636062637067092784543907 522954093955600639176815861)
        ·
          refine ⟨49026946308337559922826487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 522954093955600639176815861 49026946308337559922826487)
          ·
            refine ⟨73540419462506339884239731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49026946308337559922826487 73540419462506339884239731)
            ·
              refine ⟨110310629193759509826359597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73540419462506339884239731 110310629193759509826359597)
              ·
                refine ⟨41366485947659816184884849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110310629193759509826359597 41366485947659816184884849)
                ·
                  refine ⟨31024864460744862138663637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41366485947659816184884849 31024864460744862138663637)
                  ·
                    refine ⟨727145260798707706374929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31024864460744862138663637 727145260798707706374929)
                    ·
                      rfl

theorem cell23_4248331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_4248331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248331 prefixEnd_4248331 := by exact prefixLift 4248331
  have htrace : WordTrace (prefixWord ++ tailWord_4248331) baseStart_4248331 baseEnd_4248331 := by
    simpa [prefixWord, tailWord_4248331, baseEnd_4248331] using wordTrace_append hprefix tailTrace_4248331
  have hstable : (prefixWord ++ tailWord_4248331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248331).length < 2 ^ (prefixWord ++ tailWord_4248331).sum := by decide
  have hdescent : baseEnd_4248331 < baseStart_4248331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248361 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_4248361 : Nat := 118140960795 + 4248361 * 2 ^ 59
def prefixEnd_4248361 : Nat := 4983230072969 + 3 ^ 40 * 4248361 * 2
def baseEnd_4248361 : Nat := 727150395605252667249883

theorem tailTrace_4248361 : CollatzResearch.WordTrace tailWord_4248361 prefixEnd_4248361 727150395605252667249883 := by
  unfold tailWord_4248361
  simp only [CollatzResearch.WordTrace]
  refine ⟨154950455361921134138944937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103300303574614089425963291 154950455361921134138944937)
  ·
    refine ⟨116212841521440850604208703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154950455361921134138944937 116212841521440850604208703)
    ·
      refine ⟨174319262282161275906313055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116212841521440850604208703 174319262282161275906313055)
      ·
        refine ⟨261478893423241913859469583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174319262282161275906313055 261478893423241913859469583)
        ·
          refine ⟨392218340134862870789204375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261478893423241913859469583 392218340134862870789204375)
          ·
            refine ⟨588327510202294306183806563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392218340134862870789204375 588327510202294306183806563)
            ·
              refine ⟨882491265303441459275709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588327510202294306183806563 882491265303441459275709845)
              ·
                refine ⟨41366778061098818403548899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 882491265303441459275709845 41366778061098818403548899)
                ·
                  refine ⟨62050167091648227605323349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41366778061098818403548899 62050167091648227605323349)
                  ·
                    refine ⟨727150395605252667249883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62050167091648227605323349 727150395605252667249883)
                    ·
                      rfl

theorem cell23_4248361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_4248361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248361 prefixEnd_4248361 := by exact prefixLift 4248361
  have htrace : WordTrace (prefixWord ++ tailWord_4248361) baseStart_4248361 baseEnd_4248361 := by
    simpa [prefixWord, tailWord_4248361, baseEnd_4248361] using wordTrace_append hprefix tailTrace_4248361
  have hstable : (prefixWord ++ tailWord_4248361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248361).length < 2 ^ (prefixWord ++ tailWord_4248361).sum := by decide
  have hdescent : baseEnd_4248361 < baseStart_4248361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248402 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_4248402 : Nat := 118140960795 + 4248402 * 2 ^ 59
def prefixEnd_4248402 : Nat := 4983230072969 + 3 ^ 40 * 4248402 * 2
def baseEnd_4248402 : Nat := 2181472239522592341336961

theorem tailTrace_4248402 : CollatzResearch.WordTrace tailWord_4248402 prefixEnd_4248402 2181472239522592341336961 := by
  unfold tailWord_4248402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38737987688693149535296865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103301300503181732094124973 38737987688693149535296865)
  ·
    refine ⟨29053490766519862151472649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38737987688693149535296865 29053490766519862151472649)
    ·
      refine ⟨21790118074889896613604487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29053490766519862151472649 21790118074889896613604487)
      ·
        refine ⟨32685177112334844920406731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21790118074889896613604487 32685177112334844920406731)
        ·
          refine ⟨49027765668502267380610097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32685177112334844920406731 49027765668502267380610097)
          ·
            refine ⟨36770824251376700535457573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49027765668502267380610097 36770824251376700535457573)
            ·
              refine ⟨6894529547133131350398295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36770824251376700535457573 6894529547133131350398295)
              ·
                refine ⟨10341794320699697025597443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6894529547133131350398295 10341794320699697025597443)
                ·
                  refine ⟨15512691481049545538396165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10341794320699697025597443 15512691481049545538396165)
                  ·
                    refine ⟨2908629652696789788449281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15512691481049545538396165 2908629652696789788449281)
                    ·
                      refine ⟨2181472239522592341336961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908629652696789788449281 2181472239522592341336961)
                      ·
                        rfl

theorem cell23_4248402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_4248402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248402 prefixEnd_4248402 := by exact prefixLift 4248402
  have htrace : WordTrace (prefixWord ++ tailWord_4248402) baseStart_4248402 baseEnd_4248402 := by
    simpa [prefixWord, tailWord_4248402, baseEnd_4248402] using wordTrace_append hprefix tailTrace_4248402
  have hstable : (prefixWord ++ tailWord_4248402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248402).length < 2 ^ (prefixWord ++ tailWord_4248402).sum := by decide
  have hdescent : baseEnd_4248402 < baseStart_4248402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248445 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_4248445 : Nat := 118140960795 + 4248445 * 2 ^ 59
def prefixEnd_4248445 : Nat := 4983230072969 + 3 ^ 40 * 4248445 * 2
def baseEnd_4248445 : Nat := 2181494319190735673099263

theorem tailTrace_4248445 : CollatzResearch.WordTrace tailWord_4248445 prefixEnd_4248445 2181494319190735673099263 := by
  unfold tailWord_4248445
  simp only [CollatzResearch.WordTrace]
  refine ⟨154953519093616816485002789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103302346062411210990001859 154953519093616816485002789)
  ·
    refine ⟨29053784830053153090938023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154953519093616816485002789 29053784830053153090938023)
    ·
      refine ⟨43580677245079729636407035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29053784830053153090938023 43580677245079729636407035)
      ·
        refine ⟨65371015867619594454610553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43580677245079729636407035 65371015867619594454610553)
        ·
          refine ⟨49028261900714695840957915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65371015867619594454610553 49028261900714695840957915)
          ·
            refine ⟨73542392851072043761436873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49028261900714695840957915 73542392851072043761436873)
            ·
              refine ⟨55156794638304032821077655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73542392851072043761436873 55156794638304032821077655)
              ·
                refine ⟨82735191957456049231616483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55156794638304032821077655 82735191957456049231616483)
                ·
                  refine ⟨124102787936184073847424725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82735191957456049231616483 124102787936184073847424725)
                  ·
                    refine ⟨2908659092254314230799017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 124102787936184073847424725 2908659092254314230799017)
                    ·
                      refine ⟨2181494319190735673099263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908659092254314230799017 2181494319190735673099263)
                      ·
                        rfl

theorem cell23_4248445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_4248445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248445 prefixEnd_4248445 := by exact prefixLift 4248445
  have htrace : WordTrace (prefixWord ++ tailWord_4248445) baseStart_4248445 baseEnd_4248445 := by
    simpa [prefixWord, tailWord_4248445, baseEnd_4248445] using wordTrace_append hprefix tailTrace_4248445
  have hstable : (prefixWord ++ tailWord_4248445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248445).length < 2 ^ (prefixWord ++ tailWord_4248445).sum := by decide
  have hdescent : baseEnd_4248445 < baseStart_4248445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248476 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 5]
def baseStart_4248476 : Nat := 118140960795 + 4248476 * 2 ^ 59
def prefixEnd_4248476 : Nat := 4983230072969 + 3 ^ 40 * 4248476 * 2
def baseEnd_4248476 : Nat := 242390026343447227979069

theorem tailTrace_4248476 : CollatzResearch.WordTrace tailWord_4248476 prefixEnd_4248476 242390026343447227979069 := by
  unfold tailWord_4248476
  simp only [CollatzResearch.WordTrace]
  refine ⟨77477324878252254389690641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103303099837669672519587521 77477324878252254389690641)
  ·
    refine ⟨58107993658689190792267981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77477324878252254389690641 58107993658689190792267981)
    ·
      refine ⟨21790497622008446547100493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58107993658689190792267981 21790497622008446547100493)
      ·
        refine ⟨8171436608253167455162685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21790497622008446547100493 8171436608253167455162685)
        ·
          refine ⟨3064288728094937795686007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8171436608253167455162685 3064288728094937795686007)
          ·
            refine ⟨4596433092142406693529011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064288728094937795686007 4596433092142406693529011)
            ·
              refine ⟨6894649638213610040293517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596433092142406693529011 6894649638213610040293517)
              ·
                refine ⟨2585493614330103765110069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6894649638213610040293517 2585493614330103765110069)
                ·
                  refine ⟨242390026343447227979069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585493614330103765110069 242390026343447227979069)
                  ·
                    rfl

theorem cell23_4248476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_4248476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248476 prefixEnd_4248476 := by exact prefixLift 4248476
  have htrace : WordTrace (prefixWord ++ tailWord_4248476) baseStart_4248476 baseEnd_4248476 := by
    simpa [prefixWord, tailWord_4248476, baseEnd_4248476] using wordTrace_append hprefix tailTrace_4248476
  have hstable : (prefixWord ++ tailWord_4248476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248476).length < 2 ^ (prefixWord ++ tailWord_4248476).sum := by decide
  have hdescent : baseEnd_4248476 < baseStart_4248476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248549 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 6]
def baseStart_4248549 : Nat := 118140960795 + 4248549 * 2 ^ 59
def prefixEnd_4248549 : Nat := 4983230072969 + 3 ^ 40 * 4248549 * 2
def baseEnd_4248549 : Nat := 242394191242089251799865

theorem tailTrace_4248549 : CollatzResearch.WordTrace tailWord_4248549 prefixEnd_4248549 242394191242089251799865 := by
  unfold tailWord_4248549
  simp only [CollatzResearch.WordTrace]
  refine ⟨154957312285240042246788701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103304874856826694831192467 154957312285240042246788701)
  ·
    refine ⟨58108992106965015842545763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154957312285240042246788701 58108992106965015842545763)
    ·
      refine ⟨87163488160447523763818645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58108992106965015842545763 87163488160447523763818645)
      ·
        refine ⟨4085788507520977676428999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87163488160447523763818645 4085788507520977676428999)
        ·
          refine ⟨6128682761281466514643499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085788507520977676428999 6128682761281466514643499)
          ·
            refine ⟨9193024141922199771965249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128682761281466514643499 9193024141922199771965249)
            ·
              refine ⟨6894768106441649828973937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9193024141922199771965249 6894768106441649828973937)
              ·
                refine ⟨5171076079831237371730453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6894768106441649828973937 5171076079831237371730453)
                ·
                  refine ⟨242394191242089251799865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5171076079831237371730453 242394191242089251799865)
                  ·
                    rfl

theorem cell23_4248549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_4248549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248549 prefixEnd_4248549 := by exact prefixLift 4248549
  have htrace : WordTrace (prefixWord ++ tailWord_4248549) baseStart_4248549 baseEnd_4248549 := by
    simpa [prefixWord, tailWord_4248549, baseEnd_4248549] using wordTrace_append hprefix tailTrace_4248549
  have hstable : (prefixWord ++ tailWord_4248549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248549).length < 2 ^ (prefixWord ++ tailWord_4248549).sum := by decide
  have hdescent : baseEnd_4248549 < baseStart_4248549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248575 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 8, 4]
def baseStart_4248575 : Nat := 118140960795 + 4248575 * 2 ^ 59
def prefixEnd_4248575 : Nat := 4983230072969 + 3 ^ 40 * 4248575 * 2
def baseEnd_4248575 : Nat := 727187023891940054824555

theorem tailTrace_4248575 : CollatzResearch.WordTrace tailWord_4248575 prefixEnd_4248575 727187023891940054824555 := by
  unfold tailWord_4248575
  simp only [CollatzResearch.WordTrace]
  refine ⟨154958260583145848687235179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103305507055430565791490119 154958260583145848687235179)
  ·
    refine ⟨232437390874718773030852769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154958260583145848687235179 232437390874718773030852769)
    ·
      refine ⟨174328043156039079773139577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232437390874718773030852769 174328043156039079773139577)
      ·
        refine ⟨130746032367029309829854683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174328043156039079773139577 130746032367029309829854683)
        ·
          refine ⟨196119048550543964744782025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130746032367029309829854683 196119048550543964744782025)
          ·
            refine ⟨147089286412907973558586519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196119048550543964744782025 147089286412907973558586519)
            ·
              refine ⟨220633929619361960337879779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147089286412907973558586519 220633929619361960337879779)
              ·
                refine ⟨330950894429042940506819669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220633929619361960337879779 330950894429042940506819669)
                ·
                  refine ⟨3878330794090346959064293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 330950894429042940506819669 3878330794090346959064293)
                  ·
                    refine ⟨727187023891940054824555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878330794090346959064293 727187023891940054824555)
                    ·
                      rfl

theorem cell23_4248575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_4248575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248575 prefixEnd_4248575 := by exact prefixLift 4248575
  have htrace : WordTrace (prefixWord ++ tailWord_4248575) baseStart_4248575 baseEnd_4248575 := by
    simpa [prefixWord, tailWord_4248575, baseEnd_4248575] using wordTrace_append hprefix tailTrace_4248575
  have hstable : (prefixWord ++ tailWord_4248575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248575).length < 2 ^ (prefixWord ++ tailWord_4248575).sum := by decide
  have hdescent : baseEnd_4248575 < baseStart_4248575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248586 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_4248586 : Nat := 118140960795 + 4248586 * 2 ^ 59
def prefixEnd_4248586 : Nat := 4983230072969 + 3 ^ 40 * 4248586 * 2
def baseEnd_4248586 : Nat := 2181566719963019621436115

theorem tailTrace_4248586 : CollatzResearch.WordTrace tailWord_4248586 prefixEnd_4248586 2181566719963019621436115 := by
  unfold tailWord_4248586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38739665446526499391471403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103305774524070665043923741 38739665446526499391471403)
  ·
    refine ⟨58109498169789749087207105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38739665446526499391471403 58109498169789749087207105)
    ·
      refine ⟨43582123627342311815405329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58109498169789749087207105 43582123627342311815405329)
      ·
        refine ⟨32686592720506733861553997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43582123627342311815405329 32686592720506733861553997)
        ·
          refine ⟨12257472270190025198082749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32686592720506733861553997 12257472270190025198082749)
          ·
            refine ⟨4596552101321259449281031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12257472270190025198082749 4596552101321259449281031)
            ·
              refine ⟨6894828151981889173921547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596552101321259449281031 6894828151981889173921547)
              ·
                refine ⟨10342242227972833760882321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6894828151981889173921547 10342242227972833760882321)
                ·
                  refine ⟨7756681670979625320661741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10342242227972833760882321 7756681670979625320661741)
                  ·
                    refine ⟨2908755626617359495248153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7756681670979625320661741 2908755626617359495248153)
                    ·
                      refine ⟨2181566719963019621436115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908755626617359495248153 2181566719963019621436115)
                      ·
                        rfl

theorem cell23_4248586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_4248586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248586 prefixEnd_4248586 := by exact prefixLift 4248586
  have htrace : WordTrace (prefixWord ++ tailWord_4248586) baseStart_4248586 baseEnd_4248586 := by
    simpa [prefixWord, tailWord_4248586, baseEnd_4248586] using wordTrace_append hprefix tailTrace_4248586
  have hstable : (prefixWord ++ tailWord_4248586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248586).length < 2 ^ (prefixWord ++ tailWord_4248586).sum := by decide
  have hdescent : baseEnd_4248586 < baseStart_4248586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248599 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4248599 : Nat := 118140960795 + 4248599 * 2 ^ 59
def prefixEnd_4248599 : Nat := 4983230072969 + 3 ^ 40 * 4248599 * 2
def baseEnd_4248599 : Nat := 2181573395211528070573555

theorem tailTrace_4248599 : CollatzResearch.WordTrace tailWord_4248599 prefixEnd_4248599 2181573395211528070573555 := by
  unfold tailWord_4248599
  simp only [CollatzResearch.WordTrace]
  refine ⟨154959135935058900786108851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103306090623372600524072567 154959135935058900786108851)
  ·
    refine ⟨232438703902588351179163277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154959135935058900786108851 232438703902588351179163277)
    ·
      refine ⟨87164513963470631692186229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232438703902588351179163277 87164513963470631692186229)
      ·
        refine ⟨8171673184075371721142459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87164513963470631692186229 8171673184075371721142459)
        ·
          refine ⟨12257509776113057581713689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171673184075371721142459 12257509776113057581713689)
          ·
            refine ⟨9193132332084793186285267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12257509776113057581713689 9193132332084793186285267)
            ·
              refine ⟨13789698498127189779427901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193132332084793186285267 13789698498127189779427901)
              ·
                refine ⟨5171136936797696167285463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13789698498127189779427901 5171136936797696167285463)
                ·
                  refine ⟨7756705405196544250928195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171136936797696167285463 7756705405196544250928195)
                  ·
                    refine ⟨11635058107794816376392293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7756705405196544250928195 11635058107794816376392293)
                    ·
                      refine ⟨2181573395211528070573555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11635058107794816376392293 2181573395211528070573555)
                      ·
                        rfl

theorem cell23_4248599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4248599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248599 prefixEnd_4248599 := by exact prefixLift 4248599
  have htrace : WordTrace (prefixWord ++ tailWord_4248599) baseStart_4248599 baseEnd_4248599 := by
    simpa [prefixWord, tailWord_4248599, baseEnd_4248599] using wordTrace_append hprefix tailTrace_4248599
  have hstable : (prefixWord ++ tailWord_4248599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248599).length < 2 ^ (prefixWord ++ tailWord_4248599).sum := by decide
  have hdescent : baseEnd_4248599 < baseStart_4248599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248609 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_4248609 : Nat := 118140960795 + 4248609 * 2 ^ 59
def prefixEnd_4248609 : Nat := 4983230072969 + 3 ^ 40 * 4248609 * 2
def baseEnd_4248609 : Nat := 727192843339357677149503

theorem tailTrace_4248609 : CollatzResearch.WordTrace tailWord_4248609 prefixEnd_4248609 727192843339357677149503 := by
  unfold tailWord_4248609
  simp only [CollatzResearch.WordTrace]
  refine ⟨154959500665022672493972881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103306333776681781662648587 154959500665022672493972881)
  ·
    refine ⟨116219625498767004370479661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154959500665022672493972881 116219625498767004370479661)
    ·
      refine ⟨43582359562037626638929873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116219625498767004370479661 43582359562037626638929873)
      ·
        refine ⟨32686769671528219979197405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43582359562037626638929873 32686769671528219979197405)
        ·
          refine ⟨12257538626823082492199027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32686769671528219979197405 12257538626823082492199027)
          ·
            refine ⟨18386307940234623738298541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257538626823082492199027 18386307940234623738298541)
            ·
              refine ⟨6894865477587983901861953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18386307940234623738298541 6894865477587983901861953)
              ·
                refine ⟨5171149108190987926396465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6894865477587983901861953 5171149108190987926396465)
                ·
                  refine ⟨3878361831143240944797349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171149108190987926396465 3878361831143240944797349)
                  ·
                    refine ⟨727192843339357677149503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878361831143240944797349 727192843339357677149503)
                    ·
                      rfl

theorem cell23_4248609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_4248609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248609 prefixEnd_4248609 := by exact prefixLift 4248609
  have htrace : WordTrace (prefixWord ++ tailWord_4248609) baseStart_4248609 baseEnd_4248609 := by
    simpa [prefixWord, tailWord_4248609, baseEnd_4248609] using wordTrace_append hprefix tailTrace_4248609
  have hstable : (prefixWord ++ tailWord_4248609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248609).length < 2 ^ (prefixWord ++ tailWord_4248609).sum := by decide
  have hdescent : baseEnd_4248609 < baseStart_4248609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248645 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4248645 : Nat := 118140960795 + 4248645 * 2 ^ 59
def prefixEnd_4248645 : Nat := 4983230072969 + 3 ^ 40 * 4248645 * 2
def baseEnd_4248645 : Nat := 2181597015321634890598343

theorem tailTrace_4248645 : CollatzResearch.WordTrace tailWord_4248645 prefixEnd_4248645 2181597015321634890598343 := by
  unfold tailWord_4248645
  simp only [CollatzResearch.WordTrace]
  refine ⟨154960813692892250642283389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103307209128594833761522259 154960813692892250642283389)
  ·
    refine ⟨58110305134834593990856271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154960813692892250642283389 58110305134834593990856271)
    ·
      refine ⟨87165457702251890986284407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58110305134834593990856271 87165457702251890986284407)
      ·
        refine ⟨130748186553377836479426611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87165457702251890986284407 130748186553377836479426611)
        ·
          refine ⟨196122279830066754719139917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130748186553377836479426611 196122279830066754719139917)
          ·
            refine ⟨73545854936275033019677469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196122279830066754719139917 73545854936275033019677469)
            ·
              refine ⟨27579695601103137382379051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73545854936275033019677469 27579695601103137382379051)
              ·
                refine ⟨41369543401654706073568577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27579695601103137382379051 41369543401654706073568577)
                ·
                  refine ⟨31027157551241029555176433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41369543401654706073568577 31027157551241029555176433)
                  ·
                    refine ⟨23270368163430772166382325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31027157551241029555176433 23270368163430772166382325)
                    ·
                      refine ⟨2181597015321634890598343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23270368163430772166382325 2181597015321634890598343)
                      ·
                        rfl

theorem cell23_4248645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4248645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248645 prefixEnd_4248645 := by exact prefixLift 4248645
  have htrace : WordTrace (prefixWord ++ tailWord_4248645) baseStart_4248645 baseEnd_4248645 := by
    simpa [prefixWord, tailWord_4248645, baseEnd_4248645] using wordTrace_append hprefix tailTrace_4248645
  have hstable : (prefixWord ++ tailWord_4248645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248645).length < 2 ^ (prefixWord ++ tailWord_4248645).sum := by decide
  have hdescent : baseEnd_4248645 < baseStart_4248645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248665 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_4248665 : Nat := 118140960795 + 4248665 * 2 ^ 59
def prefixEnd_4248665 : Nat := 4983230072969 + 3 ^ 40 * 4248665 * 2
def baseEnd_4248665 : Nat := 727202428311574937449417

theorem tailTrace_4248665 : CollatzResearch.WordTrace tailWord_4248665 prefixEnd_4248665 727202428311574937449417 := by
  unfold tailWord_4248665
  simp only [CollatzResearch.WordTrace]
  refine ⟨154961543152819794058011449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103307695435213196038674299 154961543152819794058011449)
  ·
    refine ⟨116221157364614845543508587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154961543152819794058011449 116221157364614845543508587)
    ·
      refine ⟨174331736046922268315262881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116221157364614845543508587 174331736046922268315262881)
      ·
        refine ⟨130748802035191701236447161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174331736046922268315262881 130748802035191701236447161)
        ·
          refine ⟨98061601526393775927335371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130748802035191701236447161 98061601526393775927335371)
          ·
            refine ⟨147092402289590663891003057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98061601526393775927335371 147092402289590663891003057)
            ·
              refine ⟨110319301717192997918252293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147092402289590663891003057 110319301717192997918252293)
              ·
                refine ⟨20684869071973687109672305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110319301717192997918252293 20684869071973687109672305)
                ·
                  refine ⟨15513651803980265332254229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20684869071973687109672305 15513651803980265332254229)
                  ·
                    refine ⟨727202428311574937449417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15513651803980265332254229 727202428311574937449417)
                    ·
                      rfl

theorem cell23_4248665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_4248665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248665 prefixEnd_4248665 := by exact prefixLift 4248665
  have htrace : WordTrace (prefixWord ++ tailWord_4248665) baseStart_4248665 baseEnd_4248665 := by
    simpa [prefixWord, tailWord_4248665, baseEnd_4248665] using wordTrace_append hprefix tailTrace_4248665
  have hstable : (prefixWord ++ tailWord_4248665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248665).length < 2 ^ (prefixWord ++ tailWord_4248665).sum := by decide
  have hdescent : baseEnd_4248665 < baseStart_4248665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248675 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4248675 : Nat := 118140960795 + 4248675 * 2 ^ 59
def prefixEnd_4248675 : Nat := 4983230072969 + 3 ^ 40 * 4248675 * 2
def baseEnd_4248675 : Nat := 2181612419741269773223205

theorem tailTrace_4248675 : CollatzResearch.WordTrace tailWord_4248675 prefixEnd_4248675 2181612419741269773223205 := by
  unfold tailWord_4248675
  simp only [CollatzResearch.WordTrace]
  refine ⟨154961907882783565765875479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103307938588522377177250319 154961907882783565765875479)
  ·
    refine ⟨232442861824175348648813219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154961907882783565765875479 232442861824175348648813219)
    ·
      refine ⟨348664292736263022973219829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232442861824175348648813219 348664292736263022973219829)
      ·
        refine ⟨32687277444024658403739359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 348664292736263022973219829 32687277444024658403739359)
        ·
          refine ⟨49030916166036987605609039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32687277444024658403739359 49030916166036987605609039)
          ·
            refine ⟨73546374249055481408413559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49030916166036987605609039 73546374249055481408413559)
            ·
              refine ⟨110319561373583222112620339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73546374249055481408413559 110319561373583222112620339)
              ·
                refine ⟨165479342060374833168930509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110319561373583222112620339 165479342060374833168930509)
                ·
                  refine ⟨62054753272640562438348941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165479342060374833168930509 62054753272640562438348941)
                  ·
                    refine ⟨23270532477240210914380853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62054753272640562438348941 23270532477240210914380853)
                    ·
                      refine ⟨2181612419741269773223205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23270532477240210914380853 2181612419741269773223205)
                      ·
                        rfl

theorem cell23_4248675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4248675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248675 prefixEnd_4248675 := by exact prefixLift 4248675
  have htrace : WordTrace (prefixWord ++ tailWord_4248675) baseStart_4248675 baseEnd_4248675 := by
    simpa [prefixWord, tailWord_4248675, baseEnd_4248675] using wordTrace_append hprefix tailTrace_4248675
  have hstable : (prefixWord ++ tailWord_4248675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248675).length < 2 ^ (prefixWord ++ tailWord_4248675).sum := by decide
  have hdescent : baseEnd_4248675 < baseStart_4248675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248689 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_4248689 : Nat := 118140960795 + 4248689 * 2 ^ 59
def prefixEnd_4248689 : Nat := 4983230072969 + 3 ^ 40 * 4248689 * 2
def baseEnd_4248689 : Nat := 2181619608470432718448141

theorem tailTrace_4248689 : CollatzResearch.WordTrace tailWord_4248689 prefixEnd_4248689 2181619608470432718448141 := by
  unfold tailWord_4248689
  simp only [CollatzResearch.WordTrace]
  refine ⟨154962418504732846156885121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103308279003155230771256747 154962418504732846156885121)
  ·
    refine ⟨116221813878549634617663841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154962418504732846156885121 116221813878549634617663841)
    ·
      refine ⟨87166360408912225963247881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116221813878549634617663841 87166360408912225963247881)
      ·
        refine ⟨65374770306684169472435911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87166360408912225963247881 65374770306684169472435911)
        ·
          refine ⟨98062155460026254208653867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65374770306684169472435911 98062155460026254208653867)
          ·
            refine ⟨147093233190039381312980801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98062155460026254208653867 147093233190039381312980801)
            ·
              refine ⟨110319924892529535984735601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147093233190039381312980801 110319924892529535984735601)
              ·
                refine ⟨82739943669397151988551701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110319924892529535984735601 82739943669397151988551701)
                ·
                  refine ⟨3878434859502991499463361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82739943669397151988551701 3878434859502991499463361)
                  ·
                    refine ⟨2908826144627243624597521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3878434859502991499463361 2908826144627243624597521)
                    ·
                      refine ⟨2181619608470432718448141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908826144627243624597521 2181619608470432718448141)
                      ·
                        rfl

theorem cell23_4248689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_4248689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248689 prefixEnd_4248689 := by exact prefixLift 4248689
  have htrace : WordTrace (prefixWord ++ tailWord_4248689) baseStart_4248689 baseEnd_4248689 := by
    simpa [prefixWord, tailWord_4248689, baseEnd_4248689] using wordTrace_append hprefix tailTrace_4248689
  have hstable : (prefixWord ++ tailWord_4248689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248689).length < 2 ^ (prefixWord ++ tailWord_4248689).sum := by decide
  have hdescent : baseEnd_4248689 < baseStart_4248689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248693 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4248693 : Nat := 118140960795 + 4248693 * 2 ^ 59
def prefixEnd_4248693 : Nat := 4983230072969 + 3 ^ 40 * 4248693 * 2
def baseEnd_4248693 : Nat := 2181621662393050702798123

theorem tailTrace_4248693 : CollatzResearch.WordTrace tailWord_4248693 prefixEnd_4248693 2181621662393050702798123 := by
  unfold tailWord_4248693
  simp only [CollatzResearch.WordTrace]
  refine ⟨154962564396718354840030733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103308376264478903226687155 154962564396718354840030733)
  ·
    refine ⟨58110961648769383065011525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154962564396718354840030733 58110961648769383065011525)
    ·
      refine ⟨10895805309144259324689661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58110961648769383065011525 10895805309144259324689661)
      ·
        refine ⟨4085926990929097246758623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10895805309144259324689661 4085926990929097246758623)
        ·
          refine ⟨6128890486393645870137935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085926990929097246758623 6128890486393645870137935)
          ·
            refine ⟨9193335729590468805206903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128890486393645870137935 9193335729590468805206903)
            ·
              refine ⟨13790003594385703207810355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193335729590468805206903 13790003594385703207810355)
              ·
                refine ⟨20685005391578554811715533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13790003594385703207810355 20685005391578554811715533)
                ·
                  refine ⟨7756877021841958054393325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20685005391578554811715533 7756877021841958054393325)
                  ·
                    refine ⟨2908828883190734270397497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7756877021841958054393325 2908828883190734270397497)
                    ·
                      refine ⟨2181621662393050702798123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2908828883190734270397497 2181621662393050702798123)
                      ·
                        rfl

theorem cell23_4248693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4248693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248693 prefixEnd_4248693 := by exact prefixLift 4248693
  have htrace : WordTrace (prefixWord ++ tailWord_4248693) baseStart_4248693 baseEnd_4248693 := by
    simpa [prefixWord, tailWord_4248693, baseEnd_4248693] using wordTrace_append hprefix tailTrace_4248693
  have hstable : (prefixWord ++ tailWord_4248693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248693).length < 2 ^ (prefixWord ++ tailWord_4248693).sum := by decide
  have hdescent : baseEnd_4248693 < baseStart_4248693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248695 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 9]
def baseStart_4248695 : Nat := 118140960795 + 4248695 * 2 ^ 59
def prefixEnd_4248695 : Nat := 4983230072969 + 3 ^ 40 * 4248695 * 2
def baseEnd_4248695 : Nat := 242402521039373299441457

theorem tailTrace_4248695 : CollatzResearch.WordTrace tailWord_4248695 prefixEnd_4248695 242402521039373299441457 := by
  unfold tailWord_4248695
  simp only [CollatzResearch.WordTrace]
  refine ⟨154962637342711109181603539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103308424895140739454402359 154962637342711109181603539)
  ·
    refine ⟨232443956014066663772405309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154962637342711109181603539 232443956014066663772405309)
    ·
      refine ⟨87166483505274998914651991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232443956014066663772405309 87166483505274998914651991)
      ·
        refine ⟨130749725257912498371977987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87166483505274998914651991 130749725257912498371977987)
        ·
          refine ⟨196124587886868747557966981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130749725257912498371977987 196124587886868747557966981)
          ·
            refine ⟨36773360228787890167118809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196124587886868747557966981 36773360228787890167118809)
            ·
              refine ⟨27580020171590917625339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36773360228787890167118809 27580020171590917625339107)
              ·
                refine ⟨41370030257386376438008661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27580020171590917625339107 41370030257386376438008661)
                ·
                  refine ⟨242402521039373299441457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41370030257386376438008661 242402521039373299441457)
                  ·
                    rfl

theorem cell23_4248695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 9].length) (baseStart_4248695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248695 prefixEnd_4248695 := by exact prefixLift 4248695
  have htrace : WordTrace (prefixWord ++ tailWord_4248695) baseStart_4248695 baseEnd_4248695 := by
    simpa [prefixWord, tailWord_4248695, baseEnd_4248695] using wordTrace_append hprefix tailTrace_4248695
  have hstable : (prefixWord ++ tailWord_4248695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248695).length < 2 ^ (prefixWord ++ tailWord_4248695).sum := by decide
  have hdescent : baseEnd_4248695 < baseStart_4248695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248832 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_4248832 : Nat := 118140960795 + 4248832 * 2 ^ 59
def prefixEnd_4248832 : Nat := 4983230072969 + 3 ^ 40 * 4248832 * 2
def baseEnd_4248832 : Nat := 727231012068008552986661

theorem tailTrace_4248832 : CollatzResearch.WordTrace tailWord_4248832 prefixEnd_4248832 727231012068008552986661 := by
  unfold tailWord_4248832
  simp only [CollatzResearch.WordTrace]
  refine ⟨77483817071607390789670375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103311756095476521052893833 77483817071607390789670375)
  ·
    refine ⟨116225725607411086184505563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77483817071607390789670375 116225725607411086184505563)
    ·
      refine ⟨174338588411116629276758345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116225725607411086184505563 174338588411116629276758345)
      ·
        refine ⟨130753941308337471957568759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174338588411116629276758345 130753941308337471957568759)
        ·
          refine ⟨196130911962506207936353139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130753941308337471957568759 196130911962506207936353139)
          ·
            refine ⟨294196367943759311904529709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196130911962506207936353139 294196367943759311904529709)
            ·
              refine ⟨110323637978909741964198641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294196367943759311904529709 110323637978909741964198641)
              ·
                refine ⟨82742728484182306473148981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110323637978909741964198641 82742728484182306473148981)
                ·
                  refine ⟨7757130795392091231857717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82742728484182306473148981 7757130795392091231857717)
                  ·
                    refine ⟨727231012068008552986661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7757130795392091231857717 727231012068008552986661)
                    ·
                      rfl

theorem cell23_4248832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_4248832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248832 prefixEnd_4248832 := by exact prefixLift 4248832
  have htrace : WordTrace (prefixWord ++ tailWord_4248832) baseStart_4248832 baseEnd_4248832 := by
    simpa [prefixWord, tailWord_4248832, baseEnd_4248832] using wordTrace_append hprefix tailTrace_4248832
  have hstable : (prefixWord ++ tailWord_4248832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248832).length < 2 ^ (prefixWord ++ tailWord_4248832).sum := by decide
  have hdescent : baseEnd_4248832 < baseStart_4248832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248840 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 1, 4]
def baseStart_4248840 : Nat := 118140960795 + 4248840 * 2 ^ 59
def prefixEnd_4248840 : Nat := 4983230072969 + 3 ^ 40 * 4248840 * 2
def baseEnd_4248840 : Nat := 727232381349753875886649

theorem tailTrace_4248840 : CollatzResearch.WordTrace tailWord_4248840 prefixEnd_4248840 727232381349753875886649 := by
  unfold tailWord_4248840
  simp only [CollatzResearch.WordTrace]
  refine ⟨77483962963592899472815987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103311950618123865963754649 77483962963592899472815987)
  ·
    refine ⟨116225944445389349209223981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77483962963592899472815987 116225944445389349209223981)
    ·
      refine ⟨43584729167021005953458993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116225944445389349209223981 43584729167021005953458993)
      ·
        refine ⟨32688546875265754465094245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43584729167021005953458993 32688546875265754465094245)
        ·
          refine ⟨6129102539112328962205171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32688546875265754465094245 6129102539112328962205171)
          ·
            refine ⟨9193653808668493443307757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6129102539112328962205171 9193653808668493443307757)
            ·
              refine ⟨3447620178250685041240409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9193653808668493443307757 3447620178250685041240409)
              ·
                refine ⟨2585715133688013780930307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447620178250685041240409 2585715133688013780930307)
                ·
                  refine ⟨3878572700532020671395461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585715133688013780930307 3878572700532020671395461)
                  ·
                    refine ⟨727232381349753875886649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878572700532020671395461 727232381349753875886649)
                    ·
                      rfl

theorem cell23_4248840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_4248840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248840 prefixEnd_4248840 := by exact prefixLift 4248840
  have htrace : WordTrace (prefixWord ++ tailWord_4248840) baseStart_4248840 baseEnd_4248840 := by
    simpa [prefixWord, tailWord_4248840, baseEnd_4248840] using wordTrace_append hprefix tailTrace_4248840
  have hstable : (prefixWord ++ tailWord_4248840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248840).length < 2 ^ (prefixWord ++ tailWord_4248840).sum := by decide
  have hdescent : baseEnd_4248840 < baseStart_4248840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248842 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4248842 : Nat := 118140960795 + 4248842 * 2 ^ 59
def prefixEnd_4248842 : Nat := 4983230072969 + 3 ^ 40 * 4248842 * 2
def baseEnd_4248842 : Nat := 2181698171010570619834937

theorem tailTrace_4248842 : CollatzResearch.WordTrace tailWord_4248842 prefixEnd_4248842 2181698171010570619834937 := by
  unfold tailWord_4248842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38741999718294638321801195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103311999248785702191469853 38741999718294638321801195)
  ·
    refine ⟨58112999577441957482701793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38741999718294638321801195 58112999577441957482701793)
    ·
      refine ⟨43584749683081468112026345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58112999577441957482701793 43584749683081468112026345)
      ·
        refine ⟨32688562262311101084019759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43584749683081468112026345 32688562262311101084019759)
        ·
          refine ⟨49032843393466651626029639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32688562262311101084019759 49032843393466651626029639)
          ·
            refine ⟨73549265090199977439044459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49032843393466651626029639 73549265090199977439044459)
            ·
              refine ⟨110323897635299966158566689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73549265090199977439044459 110323897635299966158566689)
              ·
                refine ⟨82742923226474974618925017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110323897635299966158566689 82742923226474974618925017)
                ·
                  refine ⟨62057192419856230964193763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82742923226474974618925017 62057192419856230964193763)
                  ·
                    refine ⟨93085788629784346446290645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62057192419856230964193763 93085788629784346446290645)
                    ·
                      refine ⟨2181698171010570619834937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93085788629784346446290645 2181698171010570619834937)
                      ·
                        rfl

theorem cell23_4248842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4248842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248842 prefixEnd_4248842 := by exact prefixLift 4248842
  have htrace : WordTrace (prefixWord ++ tailWord_4248842) baseStart_4248842 baseEnd_4248842 := by
    simpa [prefixWord, tailWord_4248842, baseEnd_4248842] using wordTrace_append hprefix tailTrace_4248842
  have hstable : (prefixWord ++ tailWord_4248842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248842).length < 2 ^ (prefixWord ++ tailWord_4248842).sum := by decide
  have hdescent : baseEnd_4248842 < baseStart_4248842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248866 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4248866 : Nat := 118140960795 + 4248866 * 2 ^ 59
def prefixEnd_4248866 : Nat := 4983230072969 + 3 ^ 40 * 4248866 * 2
def baseEnd_4248866 : Nat := 727236831515426175311609

theorem tailTrace_4248866 : CollatzResearch.WordTrace tailWord_4248866 prefixEnd_4248866 727236831515426175311609 := by
  unfold tailWord_4248866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38742218556272901346519613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103312582816727736924052301 38742218556272901346519613)
  ·
    refine ⟨14528331958602338004944855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38742218556272901346519613 14528331958602338004944855)
    ·
      refine ⟨21792497937903507007417283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14528331958602338004944855 21792497937903507007417283)
      ·
        refine ⟨32688746906855260511125925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21792497937903507007417283 32688746906855260511125925)
        ·
          refine ⟨6129140045035361345836111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32688746906855260511125925 6129140045035361345836111)
          ·
            refine ⟨9193710067553042018754167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6129140045035361345836111 9193710067553042018754167)
            ·
              refine ⟨13790565101329563028131251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193710067553042018754167 13790565101329563028131251)
              ·
                refine ⟨20685847651994344542196877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13790565101329563028131251 20685847651994344542196877)
                ·
                  refine ⟨7757192869497879203323829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20685847651994344542196877 7757192869497879203323829)
                  ·
                    refine ⟨727236831515426175311609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7757192869497879203323829 727236831515426175311609)
                    ·
                      rfl

theorem cell23_4248866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4248866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248866 prefixEnd_4248866 := by exact prefixLift 4248866
  have htrace : WordTrace (prefixWord ++ tailWord_4248866) baseStart_4248866 baseEnd_4248866 := by
    simpa [prefixWord, tailWord_4248866, baseEnd_4248866] using wordTrace_append hprefix tailTrace_4248866
  have hstable : (prefixWord ++ tailWord_4248866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248866).length < 2 ^ (prefixWord ++ tailWord_4248866).sum := by decide
  have hdescent : baseEnd_4248866 < baseStart_4248866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248892 : List Nat := [2, 2, 2, 2, 1, 14]
def baseStart_4248892 : Nat := 118140960795 + 4248892 * 2 ^ 59
def prefixEnd_4248892 : Nat := 4983230072969 + 3 ^ 40 * 4248892 * 2
def baseEnd_4248892 : Nat := 8978287428161709564649

theorem tailTrace_4248892 : CollatzResearch.WordTrace tailWord_4248892 prefixEnd_4248892 8978287428161709564649 := by
  unfold tailWord_4248892
  simp only [CollatzResearch.WordTrace]
  refine ⟨77484911261498705913262465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103313215015331607884349953 77484911261498705913262465)
  ·
    refine ⟨58113683446124029434946849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77484911261498705913262465 58113683446124029434946849)
    ·
      refine ⟨43585262584593022076210137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58113683446124029434946849 43585262584593022076210137)
      ·
        refine ⟨32688946938444766557157603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43585262584593022076210137 32688946938444766557157603)
        ·
          refine ⟨49033420407667149835736405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32688946938444766557157603 49033420407667149835736405)
          ·
            refine ⟨8978287428161709564649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 49033420407667149835736405 8978287428161709564649)
            ·
              rfl

theorem cell23_4248892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 14].length) (baseStart_4248892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248892 prefixEnd_4248892 := by exact prefixLift 4248892
  have htrace : WordTrace (prefixWord ++ tailWord_4248892) baseStart_4248892 baseEnd_4248892 := by
    simpa [prefixWord, tailWord_4248892, baseEnd_4248892] using wordTrace_append hprefix tailTrace_4248892
  have hstable : (prefixWord ++ tailWord_4248892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248892).length < 2 ^ (prefixWord ++ tailWord_4248892).sum := by decide
  have hdescent : baseEnd_4248892 < baseStart_4248892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248896 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_4248896 : Nat := 118140960795 + 4248896 * 2 ^ 59
def prefixEnd_4248896 : Nat := 4983230072969 + 3 ^ 40 * 4248896 * 2
def baseEnd_4248896 : Nat := 727241966321971136186563

theorem tailTrace_4248896 : CollatzResearch.WordTrace tailWord_4248896 prefixEnd_4248896 727241966321971136186563 := by
  unfold tailWord_4248896
  simp only [CollatzResearch.WordTrace]
  refine ⟨77484984207491460254835271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103313312276655280339780361 77484984207491460254835271)
  ·
    refine ⟨116227476311237190382252907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77484984207491460254835271 116227476311237190382252907)
    ·
      refine ⟨174341214466855785573379361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116227476311237190382252907 174341214466855785573379361)
      ·
        refine ⟨130755910850141839180034521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174341214466855785573379361 130755910850141839180034521)
        ·
          refine ⟨98066933137606379385025891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130755910850141839180034521 98066933137606379385025891)
          ·
            refine ⟨147100399706409569077538837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98066933137606379385025891 147100399706409569077538837)
            ·
              refine ⟨6895331236237948550509633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147100399706409569077538837 6895331236237948550509633)
              ·
                refine ⟨5171498427178461412882225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6895331236237948550509633 5171498427178461412882225)
                ·
                  refine ⟨3878623820383846059661669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171498427178461412882225 3878623820383846059661669)
                  ·
                    refine ⟨727241966321971136186563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878623820383846059661669 727241966321971136186563)
                    ·
                      rfl

theorem cell23_4248896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_4248896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248896 prefixEnd_4248896 := by exact prefixLift 4248896
  have htrace : WordTrace (prefixWord ++ tailWord_4248896) baseStart_4248896 baseEnd_4248896 := by
    simpa [prefixWord, tailWord_4248896, baseEnd_4248896] using wordTrace_append hprefix tailTrace_4248896
  have hstable : (prefixWord ++ tailWord_4248896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248896).length < 2 ^ (prefixWord ++ tailWord_4248896).sum := by decide
  have hdescent : baseEnd_4248896 < baseStart_4248896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248897 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4248897 : Nat := 118140960795 + 4248897 * 2 ^ 59
def prefixEnd_4248897 : Nat := 4983230072969 + 3 ^ 40 * 4248897 * 2
def baseEnd_4248897 : Nat := 2181726412446567904647185

theorem tailTrace_4248897 : CollatzResearch.WordTrace tailWord_4248897 prefixEnd_4248897 2181726412446567904647185 := by
  unfold tailWord_4248897
  simp only [CollatzResearch.WordTrace]
  refine ⟨154970004887979297680456945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103313336591986198453637963 154970004887979297680456945)
  ·
    refine ⟨116227503665984473260342709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154970004887979297680456945 116227503665984473260342709)
    ·
      refine ⟨10896328468686044368157129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116227503665984473260342709 10896328468686044368157129)
      ·
        refine ⟨8172246351514533276117847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10896328468686044368157129 8172246351514533276117847)
        ·
          refine ⟨12258369527271799914176771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8172246351514533276117847 12258369527271799914176771)
          ·
            refine ⟨18387554290907699871265157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12258369527271799914176771 18387554290907699871265157)
            ·
              refine ⟨3447666429545193725862217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18387554290907699871265157 3447666429545193725862217)
              ·
                refine ⟨2585749822158895294396663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447666429545193725862217 2585749822158895294396663)
                ·
                  refine ⟨3878624733238342941594995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585749822158895294396663 3878624733238342941594995)
                  ·
                    refine ⟨5817937099857514412392493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3878624733238342941594995 5817937099857514412392493)
                    ·
                      refine ⟨2181726412446567904647185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5817937099857514412392493 2181726412446567904647185)
                      ·
                        rfl

theorem cell23_4248897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4248897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248897 prefixEnd_4248897 := by exact prefixLift 4248897
  have htrace : WordTrace (prefixWord ++ tailWord_4248897) baseStart_4248897 baseEnd_4248897 := by
    simpa [prefixWord, tailWord_4248897, baseEnd_4248897] using wordTrace_append hprefix tailTrace_4248897
  have hstable : (prefixWord ++ tailWord_4248897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248897).length < 2 ^ (prefixWord ++ tailWord_4248897).sum := by decide
  have hdescent : baseEnd_4248897 < baseStart_4248897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248916 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_4248916 : Nat := 118140960795 + 4248916 * 2 ^ 59
def prefixEnd_4248916 : Nat := 4983230072969 + 3 ^ 40 * 4248916 * 2
def baseEnd_4248916 : Nat := 2181736168579003330309597

theorem tailTrace_4248916 : CollatzResearch.WordTrace tailWord_4248916 prefixEnd_4248916 2181736168579003330309597 := by
  unfold tailWord_4248916
  simp only [CollatzResearch.WordTrace]
  refine ⟨77485348937455231962699301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103313798583273642616932401 77485348937455231962699301)
  ·
    refine ⟨14528502925772855993006119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77485348937455231962699301 14528502925772855993006119)
    ·
      refine ⟨21792754388659283989509179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14528502925772855993006119 21792754388659283989509179)
      ·
        refine ⟨32689131582988925984263769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21792754388659283989509179 32689131582988925984263769)
        ·
          refine ⟨24516848687241694488197827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32689131582988925984263769 24516848687241694488197827)
          ·
            refine ⟨36775273030862541732296741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24516848687241694488197827 36775273030862541732296741)
            ·
              refine ⟨6895363693286726574805639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36775273030862541732296741 6895363693286726574805639)
              ·
                refine ⟨10343045539930089862208459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6895363693286726574805639 10343045539930089862208459)
                ·
                  refine ⟨15514568309895134793312689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10343045539930089862208459 15514568309895134793312689)
                  ·
                    refine ⟨11635926232421351094984517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15514568309895134793312689 11635926232421351094984517)
                    ·
                      refine ⟨2181736168579003330309597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11635926232421351094984517 2181736168579003330309597)
                      ·
                        rfl

theorem cell23_4248916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_4248916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248916 prefixEnd_4248916 := by exact prefixLift 4248916
  have htrace : WordTrace (prefixWord ++ tailWord_4248916) baseStart_4248916 baseEnd_4248916 := by
    simpa [prefixWord, tailWord_4248916, baseEnd_4248916] using wordTrace_append hprefix tailTrace_4248916
  have hstable : (prefixWord ++ tailWord_4248916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248916).length < 2 ^ (prefixWord ++ tailWord_4248916).sum := by decide
  have hdescent : baseEnd_4248916 < baseStart_4248916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248940 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_4248940 : Nat := 118140960795 + 4248940 * 2 ^ 59
def prefixEnd_4248940 : Nat := 4983230072969 + 3 ^ 40 * 4248940 * 2
def baseEnd_4248940 : Nat := 2181748492114711236409487

theorem tailTrace_4248940 : CollatzResearch.WordTrace tailWord_4248940 prefixEnd_4248940 2181748492114711236409487 := by
  unfold tailWord_4248940
  simp only [CollatzResearch.WordTrace]
  refine ⟨77485786613411758012136137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103314382151215677349514849 77485786613411758012136137)
  ·
    refine ⟨58114339960058818509102103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77485786613411758012136137 58114339960058818509102103)
    ·
      refine ⟨87171509940088227763653155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58114339960058818509102103 87171509940088227763653155)
      ·
        refine ⟨130757264910132341645479733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87171509940088227763653155 130757264910132341645479733)
        ·
          refine ⟨12258493585324907029263725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130757264910132341645479733 12258493585324907029263725)
          ·
            refine ⟨4596935094496840135973897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12258493585324907029263725 4596935094496840135973897)
            ·
              refine ⟨3447701320872630101980423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596935094496840135973897 3447701320872630101980423)
              ·
                refine ⟨5171551981308945152970635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447701320872630101980423 5171551981308945152970635)
                ·
                  refine ⟨7757327971963417729455953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171551981308945152970635 7757327971963417729455953)
                  ·
                    refine ⟨5817995978972563297091965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7757327971963417729455953 5817995978972563297091965)
                    ·
                      refine ⟨2181748492114711236409487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5817995978972563297091965 2181748492114711236409487)
                      ·
                        rfl

theorem cell23_4248940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_4248940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248940 prefixEnd_4248940 := by exact prefixLift 4248940
  have htrace : WordTrace (prefixWord ++ tailWord_4248940) baseStart_4248940 baseEnd_4248940 := by
    simpa [prefixWord, tailWord_4248940, baseEnd_4248940] using wordTrace_append hprefix tailTrace_4248940
  have hstable : (prefixWord ++ tailWord_4248940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248940).length < 2 ^ (prefixWord ++ tailWord_4248940).sum := by decide
  have hdescent : baseEnd_4248940 < baseStart_4248940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248953 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_4248953 : Nat := 118140960795 + 4248953 * 2 ^ 59
def prefixEnd_4248953 : Nat := 4983230072969 + 3 ^ 40 * 4248953 * 2
def baseEnd_4248953 : Nat := 2181755167363219685546927

theorem tailTrace_4248953 : CollatzResearch.WordTrace tailWord_4248953 prefixEnd_4248953 2181755167363219685546927 := by
  unfold tailWord_4248953
  simp only [CollatzResearch.WordTrace]
  refine ⟨154972047375776419244495513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103314698250517612829663675 154972047375776419244495513)
  ·
    refine ⟨116229035531832314433371635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154972047375776419244495513 116229035531832314433371635)
    ·
      refine ⟨174343553297748471650057453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116229035531832314433371635 174343553297748471650057453)
      ·
        refine ⟨65378832486655676868771545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174343553297748471650057453 65378832486655676868771545)
        ·
          refine ⟨49034124364991757651578659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65378832486655676868771545 49034124364991757651578659)
          ·
            refine ⟨73551186547487636477367989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49034124364991757651578659 73551186547487636477367989)
            ·
              refine ⟨6895423738826965919753249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73551186547487636477367989 6895423738826965919753249)
              ·
                refine ⟨5171567804120224439814937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6895423738826965919753249 5171567804120224439814937)
                ·
                  refine ⟨3878675853090168329861203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171567804120224439814937 3878675853090168329861203)
                  ·
                    refine ⟨5818013779635252494791805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3878675853090168329861203 5818013779635252494791805)
                    ·
                      refine ⟨2181755167363219685546927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5818013779635252494791805 2181755167363219685546927)
                      ·
                        rfl

theorem cell23_4248953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_4248953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248953 prefixEnd_4248953 := by exact prefixLift 4248953
  have htrace : WordTrace (prefixWord ++ tailWord_4248953) baseStart_4248953 baseEnd_4248953 := by
    simpa [prefixWord, tailWord_4248953, baseEnd_4248953] using wordTrace_append hprefix tailTrace_4248953
  have hstable : (prefixWord ++ tailWord_4248953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248953).length < 2 ^ (prefixWord ++ tailWord_4248953).sum := by decide
  have hdescent : baseEnd_4248953 < baseStart_4248953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4248980 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4248980 : Nat := 118140960795 + 4248980 * 2 ^ 59
def prefixEnd_4248980 : Nat := 4983230072969 + 3 ^ 40 * 4248980 * 2
def baseEnd_4248980 : Nat := 2181769031340891079909303

theorem tailTrace_4248980 : CollatzResearch.WordTrace tailWord_4248980 prefixEnd_4248980 2181769031340891079909303 := by
  unfold tailWord_4248980
  simp only [CollatzResearch.WordTrace]
  refine ⟨77486516073339301427864197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103315354764452401903818929 77486516073339301427864197)
  ·
    refine ⟨14528721763751119017724537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77486516073339301427864197 14528721763751119017724537)
    ·
      refine ⟨10896541322813339263293403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14528721763751119017724537 10896541322813339263293403)
      ·
        refine ⟨16344811984220008894940105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10896541322813339263293403 16344811984220008894940105)
        ·
          refine ⟨12258608988165006671205079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16344811984220008894940105 12258608988165006671205079)
          ·
            refine ⟨18387913482247510006807619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12258608988165006671205079 18387913482247510006807619)
            ·
              refine ⟨27581870223371265010211429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18387913482247510006807619 27581870223371265010211429)
              ·
                refine ⟨5171600666882112189414643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27581870223371265010211429 5171600666882112189414643)
                ·
                  refine ⟨7757401000323168284121965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171600666882112189414643 7757401000323168284121965)
                  ·
                    refine ⟨2909025375121188106545737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7757401000323168284121965 2909025375121188106545737)
                    ·
                      refine ⟨2181769031340891079909303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909025375121188106545737 2181769031340891079909303)
                      ·
                        rfl

theorem cell23_4248980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4248980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4248980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4248980 prefixEnd_4248980 := by exact prefixLift 4248980
  have htrace : WordTrace (prefixWord ++ tailWord_4248980) baseStart_4248980 baseEnd_4248980 := by
    simpa [prefixWord, tailWord_4248980, baseEnd_4248980] using wordTrace_append hprefix tailTrace_4248980
  have hstable : (prefixWord ++ tailWord_4248980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4248980).length < 2 ^ (prefixWord ++ tailWord_4248980).sum := by decide
  have hdescent : baseEnd_4248980 < baseStart_4248980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4248980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249009 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4249009 : Nat := 118140960795 + 4249009 * 2 ^ 59
def prefixEnd_4249009 : Nat := 4983230072969 + 3 ^ 40 * 4249009 * 2
def baseEnd_4249009 : Nat := 2181783922279871466446669

theorem tailTrace_4249009 : CollatzResearch.WordTrace tailWord_4249009 prefixEnd_4249009 2181783922279871466446669 := by
  unfold tailWord_4249009
  simp only [CollatzResearch.WordTrace]
  refine ⟨154974089863573540808534081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103316059909049027205689387 154974089863573540808534081)
  ·
    refine ⟨116230567397680155606400561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154974089863573540808534081 116230567397680155606400561)
    ·
      refine ⟨87172925548260116704800421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116230567397680155606400561 87172925548260116704800421)
      ·
        refine ⟨16344923540298771882150079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87172925548260116704800421 16344923540298771882150079)
        ·
          refine ⟨24517385310448157823225119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16344923540298771882150079 24517385310448157823225119)
          ·
            refine ⟨36776077965672236734837679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24517385310448157823225119 36776077965672236734837679)
            ·
              refine ⟨55164116948508355102256519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36776077965672236734837679 55164116948508355102256519)
              ·
                refine ⟨82746175422762532653384779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55164116948508355102256519 82746175422762532653384779)
                ·
                  refine ⟨124119263134143798980077169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82746175422762532653384779 124119263134143798980077169)
                  ·
                    refine ⟨93089447350607849235057877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124119263134143798980077169 93089447350607849235057877)
                    ·
                      refine ⟨2181783922279871466446669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93089447350607849235057877 2181783922279871466446669)
                      ·
                        rfl

theorem cell23_4249009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4249009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249009 prefixEnd_4249009 := by exact prefixLift 4249009
  have htrace : WordTrace (prefixWord ++ tailWord_4249009) baseStart_4249009 baseEnd_4249009 := by
    simpa [prefixWord, tailWord_4249009, baseEnd_4249009] using wordTrace_append hprefix tailTrace_4249009
  have hstable : (prefixWord ++ tailWord_4249009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249009).length < 2 ^ (prefixWord ++ tailWord_4249009).sum := by decide
  have hdescent : baseEnd_4249009 < baseStart_4249009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249016 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 5]
def baseStart_4249016 : Nat := 118140960795 + 4249016 * 2 ^ 59
def prefixEnd_4249016 : Nat := 4983230072969 + 3 ^ 40 * 4249016 * 2
def baseEnd_4249016 : Nat := 242420835182716993228793

theorem tailTrace_4249016 : CollatzResearch.WordTrace tailWord_4249016 prefixEnd_4249016 242420835182716993228793 := by
  unfold tailWord_4249016
  simp only [CollatzResearch.WordTrace]
  refine ⟨77487172587274090502019451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103316230116365454002692601 77487172587274090502019451)
  ·
    refine ⟨116230758880911135753029177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77487172587274090502019451 116230758880911135753029177)
    ·
      refine ⟨87173069160683351814771883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116230758880911135753029177 87173069160683351814771883)
      ·
        refine ⟨130759603741025027722157825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87173069160683351814771883 130759603741025027722157825)
        ·
          refine ⟨98069702805768770791618369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130759603741025027722157825 98069702805768770791618369)
          ·
            refine ⟨73552277104326578093713777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98069702805768770791618369 73552277104326578093713777)
            ·
              refine ⟨55164207828244933570285333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73552277104326578093713777 55164207828244933570285333)
              ·
                refine ⟨2585822241948981261107125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55164207828244933570285333 2585822241948981261107125)
                ·
                  refine ⟨242420835182716993228793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2585822241948981261107125 242420835182716993228793)
                  ·
                    rfl

theorem cell23_4249016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 5].length) (baseStart_4249016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249016 prefixEnd_4249016 := by exact prefixLift 4249016
  have htrace : WordTrace (prefixWord ++ tailWord_4249016) baseStart_4249016 baseEnd_4249016 := by
    simpa [prefixWord, tailWord_4249016, baseEnd_4249016] using wordTrace_append hprefix tailTrace_4249016
  have hstable : (prefixWord ++ tailWord_4249016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249016).length < 2 ^ (prefixWord ++ tailWord_4249016).sum := by decide
  have hdescent : baseEnd_4249016 < baseStart_4249016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249079 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_4249079 : Nat := 118140960795 + 4249079 * 2 ^ 59
def prefixEnd_4249079 : Nat := 4983230072969 + 3 ^ 40 * 4249079 * 2
def baseEnd_4249079 : Nat := 2181819865925686192571347

theorem tailTrace_4249079 : CollatzResearch.WordTrace tailWord_4249079 prefixEnd_4249079 2181819865925686192571347 := by
  unfold tailWord_4249079
  simp only [CollatzResearch.WordTrace]
  refine ⟨154976642973319942763582291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103317761982213295175721527 154976642973319942763582291)
  ·
    refine ⟨232464964459979914145373437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154976642973319942763582291 232464964459979914145373437)
    ·
      refine ⟨87174361672492467804515039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232464964459979914145373437 87174361672492467804515039)
      ·
        refine ⟨130761542508738701706772559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87174361672492467804515039 130761542508738701706772559)
        ·
          refine ⟨196142313763108052560158839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130761542508738701706772559 196142313763108052560158839)
          ·
            refine ⟨294213470644662078840238259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196142313763108052560158839 294213470644662078840238259)
            ·
              refine ⟨441320205966993118260357389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294213470644662078840238259 441320205966993118260357389)
              ·
                refine ⟨165495077237622419347634021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441320205966993118260357389 165495077237622419347634021)
                ·
                  refine ⟨31030326982054203627681379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165495077237622419347634021 31030326982054203627681379)
                  ·
                    refine ⟨46545490473081305441522069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31030326982054203627681379 46545490473081305441522069)
                    ·
                      refine ⟨2181819865925686192571347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46545490473081305441522069 2181819865925686192571347)
                      ·
                        rfl

theorem cell23_4249079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_4249079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249079 prefixEnd_4249079 := by exact prefixLift 4249079
  have htrace : WordTrace (prefixWord ++ tailWord_4249079) baseStart_4249079 baseEnd_4249079 := by
    simpa [prefixWord, tailWord_4249079, baseEnd_4249079] using wordTrace_append hprefix tailTrace_4249079
  have hstable : (prefixWord ++ tailWord_4249079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249079).length < 2 ^ (prefixWord ++ tailWord_4249079).sum := by decide
  have hdescent : baseEnd_4249079 < baseStart_4249079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249100 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4249100 : Nat := 118140960795 + 4249100 * 2 ^ 59
def prefixEnd_4249100 : Nat := 4983230072969 + 3 ^ 40 * 4249100 * 2
def baseEnd_4249100 : Nat := 2181830649019430610408751

theorem tailTrace_4249100 : CollatzResearch.WordTrace tailWord_4249100 prefixEnd_4249100 2181830649019430610408751 := by
  unfold tailWord_4249100
  simp only [CollatzResearch.WordTrace]
  refine ⟨77488704453121931675048377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103318272604162575566731169 77488704453121931675048377)
  ·
    refine ⟨58116528339841448756286283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77488704453121931675048377 58116528339841448756286283)
    ·
      refine ⟨87174792509762173134429425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58116528339841448756286283 87174792509762173134429425)
      ·
        refine ⟨65381094382321629850822069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87174792509762173134429425 65381094382321629850822069)
        ·
          refine ⟨6129477598342652798514569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65381094382321629850822069 6129477598342652798514569)
          ·
            refine ⟨4597108198756989598885927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129477598342652798514569 4597108198756989598885927)
            ·
              refine ⟨6895662298135484398328891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597108198756989598885927 6895662298135484398328891)
              ·
                refine ⟨10343493447203226597493337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6895662298135484398328891 10343493447203226597493337)
                ·
                  refine ⟨7757620085402419948120003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10343493447203226597493337 7757620085402419948120003)
                  ·
                    refine ⟨11636430128103629922180005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7757620085402419948120003 11636430128103629922180005)
                    ·
                      refine ⟨2181830649019430610408751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11636430128103629922180005 2181830649019430610408751)
                      ·
                        rfl

theorem cell23_4249100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4249100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249100 prefixEnd_4249100 := by exact prefixLift 4249100
  have htrace : WordTrace (prefixWord ++ tailWord_4249100) baseStart_4249100 baseEnd_4249100 := by
    simpa [prefixWord, tailWord_4249100, baseEnd_4249100] using wordTrace_append hprefix tailTrace_4249100
  have hstable : (prefixWord ++ tailWord_4249100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249100).length < 2 ^ (prefixWord ++ tailWord_4249100).sum := by decide
  have hdescent : baseEnd_4249100 < baseStart_4249100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249143 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_4249143 : Nat := 118140960795 + 4249143 * 2 ^ 59
def prefixEnd_4249143 : Nat := 4983230072969 + 3 ^ 40 * 4249143 * 2
def baseEnd_4249143 : Nat := 2181852728687573942171053

theorem tailTrace_4249143 : CollatzResearch.WordTrace tailWord_4249143 prefixEnd_4249143 2181852728687573942171053 := by
  unfold tailWord_4249143
  simp only [CollatzResearch.WordTrace]
  refine ⟨154978977245088081693912083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103319318163392054462608055 154978977245088081693912083)
  ·
    refine ⟨232468465867632122540868125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154978977245088081693912083 232468465867632122540868125)
    ·
      refine ⟨87175674700362045952825547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232468465867632122540868125 87175674700362045952825547)
      ·
        refine ⟨130763512050543068929238321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87175674700362045952825547 130763512050543068929238321)
        ·
          refine ⟨98072634037907301696928741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130763512050543068929238321 98072634037907301696928741)
          ·
            refine ⟨18388618882107619068174139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98072634037907301696928741 18388618882107619068174139)
            ·
              refine ⟨27582928323161428602261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18388618882107619068174139 27582928323161428602261209)
              ·
                refine ⟨20687196242371071451695907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27582928323161428602261209 20687196242371071451695907)
                ·
                  refine ⟨31030794363556607177543861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20687196242371071451695907 31030794363556607177543861)
                  ·
                    refine ⟨2909136971583431922894737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31030794363556607177543861 2909136971583431922894737)
                    ·
                      refine ⟨2181852728687573942171053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909136971583431922894737 2181852728687573942171053)
                      ·
                        rfl

theorem cell23_4249143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_4249143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249143 prefixEnd_4249143 := by exact prefixLift 4249143
  have htrace : WordTrace (prefixWord ++ tailWord_4249143) baseStart_4249143 baseEnd_4249143 := by
    simpa [prefixWord, tailWord_4249143, baseEnd_4249143] using wordTrace_append hprefix tailTrace_4249143
  have hstable : (prefixWord ++ tailWord_4249143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249143).length < 2 ^ (prefixWord ++ tailWord_4249143).sum := by decide
  have hdescent : baseEnd_4249143 < baseStart_4249143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249166 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_4249166 : Nat := 118140960795 + 4249166 * 2 ^ 59
def prefixEnd_4249166 : Nat := 4983230072969 + 3 ^ 40 * 4249166 * 2
def baseEnd_4249166 : Nat := 727288179580875784061149

theorem tailTrace_4249166 : CollatzResearch.WordTrace tailWord_4249166 prefixEnd_4249166 727288179580875784061149 := by
  unfold tailWord_4249166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19372477015500594577749919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103319877416003171081332901 19372477015500594577749919)
  ·
    refine ⟨29058715523250891866624879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19372477015500594577749919 29058715523250891866624879)
    ·
      refine ⟨43588073284876337799937319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29058715523250891866624879 43588073284876337799937319)
      ·
        refine ⟨65382109927314506699905979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43588073284876337799937319 65382109927314506699905979)
        ·
          refine ⟨98073164890971760049858969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65382109927314506699905979 98073164890971760049858969)
          ·
            refine ⟨73554873668228820037394227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98073164890971760049858969 73554873668228820037394227)
            ·
              refine ⟨110332310502343230056091341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73554873668228820037394227 110332310502343230056091341)
              ·
                refine ⟨41374616438378711271034253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110332310502343230056091341 41374616438378711271034253)
                ·
                  refine ⟨15515481164392016726637845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41374616438378711271034253 15515481164392016726637845)
                  ·
                    refine ⟨727288179580875784061149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15515481164392016726637845 727288179580875784061149)
                    ·
                      rfl

theorem cell23_4249166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_4249166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249166 prefixEnd_4249166 := by exact prefixLift 4249166
  have htrace : WordTrace (prefixWord ++ tailWord_4249166) baseStart_4249166 baseEnd_4249166 := by
    simpa [prefixWord, tailWord_4249166, baseEnd_4249166] using wordTrace_append hprefix tailTrace_4249166
  have hstable : (prefixWord ++ tailWord_4249166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249166).length < 2 ^ (prefixWord ++ tailWord_4249166).sum := by decide
  have hdescent : baseEnd_4249166 < baseStart_4249166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249200 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_4249200 : Nat := 118140960795 + 4249200 * 2 ^ 59
def prefixEnd_4249200 : Nat := 4983230072969 + 3 ^ 40 * 4249200 * 2
def baseEnd_4249200 : Nat := 727293999028293406386097

theorem tailTrace_4249200 : CollatzResearch.WordTrace tailWord_4249200 prefixEnd_4249200 727293999028293406386097 := by
  unfold tailWord_4249200
  simp only [CollatzResearch.WordTrace]
  refine ⟨77490528102940790214368527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103320704137254386952491369 77490528102940790214368527)
  ·
    refine ⟨116235792154411185321552791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77490528102940790214368527 116235792154411185321552791)
    ·
      refine ⟨174353688231616777982329187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116235792154411185321552791 174353688231616777982329187)
      ·
        refine ⟨261530532347425166973493781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174353688231616777982329187 261530532347425166973493781)
        ·
          refine ⟨12259243703785554701882521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 261530532347425166973493781 12259243703785554701882521)
          ·
            refine ⟨9194432777839166026411891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12259243703785554701882521 9194432777839166026411891)
            ·
              refine ⟨13791649166758749039617837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9194432777839166026411891 13791649166758749039617837)
              ·
                refine ⟨5171868437534530889856689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13791649166758749039617837 5171868437534530889856689)
                ·
                  refine ⟨3878901328150898167392517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171868437534530889856689 3878901328150898167392517)
                  ·
                    refine ⟨727293999028293406386097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878901328150898167392517 727293999028293406386097)
                    ·
                      rfl

theorem cell23_4249200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_4249200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249200 prefixEnd_4249200 := by exact prefixLift 4249200
  have htrace : WordTrace (prefixWord ++ tailWord_4249200) baseStart_4249200 baseEnd_4249200 := by
    simpa [prefixWord, tailWord_4249200, baseEnd_4249200] using wordTrace_append hprefix tailTrace_4249200
  have hstable : (prefixWord ++ tailWord_4249200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249200).length < 2 ^ (prefixWord ++ tailWord_4249200).sum := by decide
  have hdescent : baseEnd_4249200 < baseStart_4249200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249220 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_4249220 : Nat := 118140960795 + 4249220 * 2 ^ 59
def prefixEnd_4249220 : Nat := 4983230072969 + 3 ^ 40 * 4249220 * 2
def baseEnd_4249220 : Nat := 2181892266697970140908199

theorem tailTrace_4249220 : CollatzResearch.WordTrace tailWord_4249220 prefixEnd_4249220 2181892266697970140908199 := by
  unfold tailWord_4249220
  simp only [CollatzResearch.WordTrace]
  refine ⟨77490892832904561922232557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103321190443872749229643409 77490892832904561922232557)
  ·
    refine ⟨29059084812339210720837209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77490892832904561922232557 29059084812339210720837209)
    ·
      refine ⟨21794313609254408040627907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29059084812339210720837209 21794313609254408040627907)
      ·
        refine ⟨32691470413881612060941861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21794313609254408040627907 32691470413881612060941861)
        ·
          refine ⟨6129650702602802261426599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32691470413881612060941861 6129650702602802261426599)
          ·
            refine ⟨9194476053904203392139899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6129650702602802261426599 9194476053904203392139899)
            ·
              refine ⟨13791714080856305088209849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9194476053904203392139899 13791714080856305088209849)
              ·
                refine ⟨10343785560642228816157387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13791714080856305088209849 10343785560642228816157387)
                ·
                  refine ⟨15515678340963343224236081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10343785560642228816157387 15515678340963343224236081)
                  ·
                    refine ⟨11636758755722507418177061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15515678340963343224236081 11636758755722507418177061)
                    ·
                      refine ⟨2181892266697970140908199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11636758755722507418177061 2181892266697970140908199)
                      ·
                        rfl

theorem cell23_4249220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_4249220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249220 prefixEnd_4249220 := by exact prefixLift 4249220
  have htrace : WordTrace (prefixWord ++ tailWord_4249220) baseStart_4249220 baseEnd_4249220 := by
    simpa [prefixWord, tailWord_4249220, baseEnd_4249220] using wordTrace_append hprefix tailTrace_4249220
  have hstable : (prefixWord ++ tailWord_4249220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249220).length < 2 ^ (prefixWord ++ tailWord_4249220).sum := by decide
  have hdescent : baseEnd_4249220 < baseStart_4249220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249223 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_4249223 : Nat := 118140960795 + 4249223 * 2 ^ 59
def prefixEnd_4249223 : Nat := 4983230072969 + 3 ^ 40 * 4249223 * 2
def baseEnd_4249223 : Nat := 2181893807139933629170685

theorem tailTrace_4249223 : CollatzResearch.WordTrace tailWord_4249223 prefixEnd_4249223 2181893807139933629170685 := by
  unfold tailWord_4249223
  simp only [CollatzResearch.WordTrace]
  refine ⟨154981895084798255356824323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103321263389865503571216215 154981895084798255356824323)
  ·
    refine ⟨232472842627197383035236485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154981895084798255356824323 232472842627197383035236485)
    ·
      refine ⟨43588657992599509319106841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232472842627197383035236485 43588657992599509319106841)
      ·
        refine ⟨32691493494449631989330131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43588657992599509319106841 32691493494449631989330131)
        ·
          refine ⟨49037240241674447983995197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32691493494449631989330131 49037240241674447983995197)
          ·
            refine ⟨18388965090627917993998199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49037240241674447983995197 18388965090627917993998199)
            ·
              refine ⟨27583447635941876990997299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18388965090627917993998199 27583447635941876990997299)
              ·
                refine ⟨41375171453912815486495949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27583447635941876990997299 41375171453912815486495949)
                ·
                  refine ⟨15515689295217305807435981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41375171453912815486495949 15515689295217305807435981)
                  ·
                    refine ⟨5818383485706489677788493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15515689295217305807435981 5818383485706489677788493)
                    ·
                      refine ⟨2181893807139933629170685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5818383485706489677788493 2181893807139933629170685)
                      ·
                        rfl

theorem cell23_4249223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_4249223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249223 prefixEnd_4249223 := by exact prefixLift 4249223
  have htrace : WordTrace (prefixWord ++ tailWord_4249223) baseStart_4249223 baseEnd_4249223 := by
    simpa [prefixWord, tailWord_4249223, baseEnd_4249223] using wordTrace_append hprefix tailTrace_4249223
  have hstable : (prefixWord ++ tailWord_4249223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249223).length < 2 ^ (prefixWord ++ tailWord_4249223).sum := by decide
  have hdescent : baseEnd_4249223 < baseStart_4249223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249224 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4249224 : Nat := 118140960795 + 4249224 * 2 ^ 59
def prefixEnd_4249224 : Nat := 4983230072969 + 3 ^ 40 * 4249224 * 2
def baseEnd_4249224 : Nat := 2181894320620588125258181

theorem tailTrace_4249224 : CollatzResearch.WordTrace tailWord_4249224 prefixEnd_4249224 2181894320620588125258181 := by
  unfold tailWord_4249224
  simp only [CollatzResearch.WordTrace]
  refine ⟨77490965778897316263805363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103321287705196421685073817 77490965778897316263805363)
  ·
    refine ⟨116236448668345974395708045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77490965778897316263805363 116236448668345974395708045)
    ·
      refine ⟨43588668250629740398390517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116236448668345974395708045 43588668250629740398390517)
      ·
        refine ⟨4086437648496538162349111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43588668250629740398390517 4086437648496538162349111)
        ·
          refine ⟨6129656472744807243523667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086437648496538162349111 6129656472744807243523667)
          ·
            refine ⟨9194484709117210865285501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6129656472744807243523667 9194484709117210865285501)
            ·
              refine ⟨3447931765918954074482063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9194484709117210865285501 3447931765918954074482063)
              ·
                refine ⟨5171897648878431111723095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447931765918954074482063 5171897648878431111723095)
                ·
                  refine ⟨7757846473317646667584643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171897648878431111723095 7757846473317646667584643)
                  ·
                    refine ⟨11636769709976470001376965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7757846473317646667584643 11636769709976470001376965)
                    ·
                      refine ⟨2181894320620588125258181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11636769709976470001376965 2181894320620588125258181)
                      ·
                        rfl

theorem cell23_4249224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4249224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249224 prefixEnd_4249224 := by exact prefixLift 4249224
  have htrace : WordTrace (prefixWord ++ tailWord_4249224) baseStart_4249224 baseEnd_4249224 := by
    simpa [prefixWord, tailWord_4249224, baseEnd_4249224] using wordTrace_append hprefix tailTrace_4249224
  have hstable : (prefixWord ++ tailWord_4249224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249224).length < 2 ^ (prefixWord ++ tailWord_4249224).sum := by decide
  have hdescent : baseEnd_4249224 < baseStart_4249224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249247 : List Nat := [1, 1, 2, 7, 2, 1, 1, 8]
def baseStart_4249247 : Nat := 118140960795 + 4249247 * 2 ^ 59
def prefixEnd_4249247 : Nat := 4983230072969 + 3 ^ 40 * 4249247 * 2
def baseEnd_4249247 : Nat := 80811338173171908713725

theorem tailTrace_4249247 : CollatzResearch.WordTrace tailWord_4249247 prefixEnd_4249247 80811338173171908713725 := by
  unfold tailWord_4249247
  simp only [CollatzResearch.WordTrace]
  refine ⟨154982770436711307455697995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103321846957807538303798663 154982770436711307455697995)
  ·
    refine ⟨232474155655066961183546993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154982770436711307455697995 232474155655066961183546993)
    ·
      refine ⟨174355616741300220887660245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232474155655066961183546993 174355616741300220887660245)
      ·
        refine ⟨4086459767374223927054537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 174355616741300220887660245 4086459767374223927054537)
        ·
          refine ⟨3064844825530667945290903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4086459767374223927054537 3064844825530667945290903)
          ·
            refine ⟨4597267238296001917936355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064844825530667945290903 4597267238296001917936355)
            ·
              refine ⟨6895900857444002876904533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597267238296001917936355 6895900857444002876904533)
              ·
                refine ⟨80811338173171908713725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6895900857444002876904533 80811338173171908713725)
                ·
                  rfl

theorem cell23_4249247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 8].length) (baseStart_4249247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249247 prefixEnd_4249247 := by exact prefixLift 4249247
  have htrace : WordTrace (prefixWord ++ tailWord_4249247) baseStart_4249247 baseEnd_4249247 := by
    simpa [prefixWord, tailWord_4249247, baseEnd_4249247] using wordTrace_append hprefix tailTrace_4249247
  have hstable : (prefixWord ++ tailWord_4249247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249247).length < 2 ^ (prefixWord ++ tailWord_4249247).sum := by decide
  have hdescent : baseEnd_4249247 < baseStart_4249247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249280 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2]
def baseStart_4249280 : Nat := 118140960795 + 4249280 * 2 ^ 59
def prefixEnd_4249280 : Nat := 4983230072969 + 3 ^ 40 * 4249280 * 2
def baseEnd_4249280 : Nat := 2181923075537239906157923

theorem tailTrace_4249280 : CollatzResearch.WordTrace tailWord_4249280 prefixEnd_4249280 2181923075537239906157923 := by
  unfold tailWord_4249280
  simp only [CollatzResearch.WordTrace]
  refine ⟨77491987022795877045824647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103322649363727836061099529 77491987022795877045824647)
  ·
    refine ⟨116237980534193815568736971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77491987022795877045824647 116237980534193815568736971)
    ·
      refine ⟨174356970801290723353105457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116237980534193815568736971 174356970801290723353105457)
      ·
        refine ⟨130767728100968042514829093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174356970801290723353105457 130767728100968042514829093)
        ·
          refine ⟨24518949018931507971530455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130767728100968042514829093 24518949018931507971530455)
          ·
            refine ⟨36778423528397261957295683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24518949018931507971530455 36778423528397261957295683)
            ·
              refine ⟨55167635292595892935943525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36778423528397261957295683 55167635292595892935943525)
              ·
                refine ⟨10343931617361729925489411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55167635292595892935943525 10343931617361729925489411)
                ·
                  refine ⟨15515897426042594888234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10343931617361729925489411 15515897426042594888234117)
                  ·
                    refine ⟨2909230767382986541543897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15515897426042594888234117 2909230767382986541543897)
                    ·
                      refine ⟨2181923075537239906157923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909230767382986541543897 2181923075537239906157923)
                      ·
                        rfl

theorem cell23_4249280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_4249280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249280 prefixEnd_4249280 := by exact prefixLift 4249280
  have htrace : WordTrace (prefixWord ++ tailWord_4249280) baseStart_4249280 baseEnd_4249280 := by
    simpa [prefixWord, tailWord_4249280, baseEnd_4249280] using wordTrace_append hprefix tailTrace_4249280
  have hstable : (prefixWord ++ tailWord_4249280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249280).length < 2 ^ (prefixWord ++ tailWord_4249280).sum := by decide
  have hdescent : baseEnd_4249280 < baseStart_4249280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249296 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_4249296 : Nat := 118140960795 + 4249296 * 2 ^ 59
def prefixEnd_4249296 : Nat := 4983230072969 + 3 ^ 40 * 4249296 * 2
def baseEnd_4249296 : Nat := 2181931291227711843557849

theorem tailTrace_4249296 : CollatzResearch.WordTrace tailWord_4249296 prefixEnd_4249296 2181931291227711843557849 := by
  unfold tailWord_4249296
  simp only [CollatzResearch.WordTrace]
  refine ⟨77492278806766894412115871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103323038409022525882821161 77492278806766894412115871)
  ·
    refine ⟨116238418210150341618173807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77492278806766894412115871 116238418210150341618173807)
    ·
      refine ⟨174357627315225512427260711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116238418210150341618173807 174357627315225512427260711)
      ·
        refine ⟨261536440972838268640891067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174357627315225512427260711 261536440972838268640891067)
        ·
          refine ⟨392304661459257402961336601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261536440972838268640891067 392304661459257402961336601)
          ·
            refine ⟨294228496094443052221002451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392304661459257402961336601 294228496094443052221002451)
            ·
              refine ⟨441342744141664578331503677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294228496094443052221002451 441342744141664578331503677)
              ·
                refine ⟨165503529053124216874313879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441342744141664578331503677 165503529053124216874313879)
                ·
                  refine ⟨248255293579686325311470819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165503529053124216874313879 248255293579686325311470819)
                  ·
                    refine ⟨372382940369529487967206229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 248255293579686325311470819 372382940369529487967206229)
                    ·
                      refine ⟨2181931291227711843557849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 372382940369529487967206229 2181931291227711843557849)
                      ·
                        rfl

theorem cell23_4249296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_4249296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249296 prefixEnd_4249296 := by exact prefixLift 4249296
  have htrace : WordTrace (prefixWord ++ tailWord_4249296) baseStart_4249296 baseEnd_4249296 := by
    simpa [prefixWord, tailWord_4249296, baseEnd_4249296] using wordTrace_append hprefix tailTrace_4249296
  have hstable : (prefixWord ++ tailWord_4249296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249296).length < 2 ^ (prefixWord ++ tailWord_4249296).sum := by decide
  have hdescent : baseEnd_4249296 < baseStart_4249296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249297 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_4249297 : Nat := 118140960795 + 4249297 * 2 ^ 59
def prefixEnd_4249297 : Nat := 4983230072969 + 3 ^ 40 * 4249297 * 2
def baseEnd_4249297 : Nat := 2181931804708366339645345

theorem tailTrace_4249297 : CollatzResearch.WordTrace tailWord_4249297 prefixEnd_4249297 2181931804708366339645345 := by
  unfold tailWord_4249297
  simp only [CollatzResearch.WordTrace]
  refine ⟨154984594086530165995018145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103323062724353443996678763 154984594086530165995018145)
  ·
    refine ⟨116238445564897624496263609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154984594086530165995018145 116238445564897624496263609)
    ·
      refine ⟨87178834173673218372197707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116238445564897624496263609 87178834173673218372197707)
      ·
        refine ⟨130768251260509827558296561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87178834173673218372197707 130768251260509827558296561)
        ·
          refine ⟨98076188445382370668722421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130768251260509827558296561 98076188445382370668722421)
          ·
            refine ⟨9194642666754597250192727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98076188445382370668722421 9194642666754597250192727)
            ·
              refine ⟨13791964000131895875289091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9194642666754597250192727 13791964000131895875289091)
              ·
                refine ⟨20687946000197843812933637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13791964000131895875289091 20687946000197843812933637)
                ·
                  refine ⟨3878989875037095714925057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20687946000197843812933637 3878989875037095714925057)
                  ·
                    refine ⟨2909242406277821786193793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3878989875037095714925057 2909242406277821786193793)
                    ·
                      refine ⟨2181931804708366339645345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909242406277821786193793 2181931804708366339645345)
                      ·
                        rfl

theorem cell23_4249297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_4249297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249297 prefixEnd_4249297 := by exact prefixLift 4249297
  have htrace : WordTrace (prefixWord ++ tailWord_4249297) baseStart_4249297 baseEnd_4249297 := by
    simpa [prefixWord, tailWord_4249297, baseEnd_4249297] using wordTrace_append hprefix tailTrace_4249297
  have hstable : (prefixWord ++ tailWord_4249297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249297).length < 2 ^ (prefixWord ++ tailWord_4249297).sum := by decide
  have hdescent : baseEnd_4249297 < baseStart_4249297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249303 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 7]
def baseStart_4249303 : Nat := 118140960795 + 4249303 * 2 ^ 59
def prefixEnd_4249303 : Nat := 4983230072969 + 3 ^ 40 * 4249303 * 2
def baseEnd_4249303 : Nat := 242437209510254812907813

theorem tailTrace_4249303 : CollatzResearch.WordTrace tailWord_4249303 prefixEnd_4249303 242437209510254812907813 := by
  unfold tailWord_4249303
  simp only [CollatzResearch.WordTrace]
  refine ⟨154984812924508429019736563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103323208616338952679824375 154984812924508429019736563)
  ·
    refine ⟨232477219386762643529604845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154984812924508429019736563 232477219386762643529604845)
    ·
      refine ⟨87178957270035991323601817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232477219386762643529604845 87178957270035991323601817)
      ·
        refine ⟨65384217952526993492701363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87178957270035991323601817 65384217952526993492701363)
        ·
          refine ⟨98076326928790490239052045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65384217952526993492701363 98076326928790490239052045)
          ·
            refine ⟨36778622598296433839644517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98076326928790490239052045 36778622598296433839644517)
            ·
              refine ⟨6895991737180581344933347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36778622598296433839644517 6895991737180581344933347)
              ·
                refine ⟨10343987605770872017400021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6895991737180581344933347 10343987605770872017400021)
                ·
                  refine ⟨242437209510254812907813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10343987605770872017400021 242437209510254812907813)
                  ·
                    rfl

theorem cell23_4249303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 7].length) (baseStart_4249303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249303 prefixEnd_4249303 := by exact prefixLift 4249303
  have htrace : WordTrace (prefixWord ++ tailWord_4249303) baseStart_4249303 baseEnd_4249303 := by
    simpa [prefixWord, tailWord_4249303, baseEnd_4249303] using wordTrace_append hprefix tailTrace_4249303
  have hstable : (prefixWord ++ tailWord_4249303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249303).length < 2 ^ (prefixWord ++ tailWord_4249303).sum := by decide
  have hdescent : baseEnd_4249303 < baseStart_4249303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249413 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4249413 : Nat := 118140960795 + 4249413 * 2 ^ 59
def prefixEnd_4249413 : Nat := 4983230072969 + 3 ^ 40 * 4249413 * 2
def baseEnd_4249413 : Nat := 2181991368464287885794811

theorem tailTrace_4249413 : CollatzResearch.WordTrace tailWord_4249413 prefixEnd_4249413 2181991368464287885794811 := by
  unfold tailWord_4249413
  simp only [CollatzResearch.WordTrace]
  refine ⟨154988824954109917806240893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103325883302739945204160595 154988824954109917806240893)
  ·
    refine ⟨58120809357791219177340335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154988824954109917806240893 58120809357791219177340335)
    ·
      refine ⟨87181214036686828766010503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58120809357791219177340335 87181214036686828766010503)
      ·
        refine ⟨130771821055030243149015755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87181214036686828766010503 130771821055030243149015755)
        ·
          refine ⟨196157731582545364723523633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130771821055030243149015755 196157731582545364723523633)
          ·
            refine ⟨147118298686909023542642725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196157731582545364723523633 147118298686909023542642725)
            ·
              refine ⟨27584681003795441914245511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147118298686909023542642725 27584681003795441914245511)
              ·
                refine ⟨41377021505693162871368267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27584681003795441914245511 41377021505693162871368267)
                ·
                  refine ⟨62065532258539744307052401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41377021505693162871368267 62065532258539744307052401)
                  ·
                    refine ⟨46549149193904808230289301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62065532258539744307052401 46549149193904808230289301)
                    ·
                      refine ⟨2181991368464287885794811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46549149193904808230289301 2181991368464287885794811)
                      ·
                        rfl

theorem cell23_4249413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4249413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249413 prefixEnd_4249413 := by exact prefixLift 4249413
  have htrace : WordTrace (prefixWord ++ tailWord_4249413) baseStart_4249413 baseEnd_4249413 := by
    simpa [prefixWord, tailWord_4249413, baseEnd_4249413] using wordTrace_append hprefix tailTrace_4249413
  have hstable : (prefixWord ++ tailWord_4249413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249413).length < 2 ^ (prefixWord ++ tailWord_4249413).sum := by decide
  have hdescent : baseEnd_4249413 < baseStart_4249413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249433 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_4249433 : Nat := 118140960795 + 4249433 * 2 ^ 59
def prefixEnd_4249433 : Nat := 4983230072969 + 3 ^ 40 * 4249433 * 2
def baseEnd_4249433 : Nat := 2182001638077377807544719

theorem tailTrace_4249433 : CollatzResearch.WordTrace tailWord_4249433 prefixEnd_4249433 2182001638077377807544719 := by
  unfold tailWord_4249433
  simp only [CollatzResearch.WordTrace]
  refine ⟨154989554414037461221968953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103326369609358307481312635 154989554414037461221968953)
  ·
    refine ⟨116242165810528095916476715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154989554414037461221968953 116242165810528095916476715)
    ·
      refine ⟨174363248715792143874715073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116242165810528095916476715 174363248715792143874715073)
      ·
        refine ⟨130772436536844107906036305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174363248715792143874715073 130772436536844107906036305)
        ·
          refine ⟨98079327402633080929527229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130772436536844107906036305 98079327402633080929527229)
          ·
            refine ⟨36779747775987405348572711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98079327402633080929527229 36779747775987405348572711)
            ·
              refine ⟨55169621663981108022859067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36779747775987405348572711 55169621663981108022859067)
              ·
                refine ⟨82754432495971662034288601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55169621663981108022859067 82754432495971662034288601)
                ·
                  refine ⟨62065824371978746525716451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82754432495971662034288601 62065824371978746525716451)
                  ·
                    refine ⟨93098736557968119788574677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62065824371978746525716451 93098736557968119788574677)
                    ·
                      refine ⟨2182001638077377807544719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93098736557968119788574677 2182001638077377807544719)
                      ·
                        rfl

theorem cell23_4249433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_4249433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249433 prefixEnd_4249433 := by exact prefixLift 4249433
  have htrace : WordTrace (prefixWord ++ tailWord_4249433) baseStart_4249433 baseEnd_4249433 := by
    simpa [prefixWord, tailWord_4249433, baseEnd_4249433] using wordTrace_append hprefix tailTrace_4249433
  have hstable : (prefixWord ++ tailWord_4249433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249433).length < 2 ^ (prefixWord ++ tailWord_4249433).sum := by decide
  have hdescent : baseEnd_4249433 < baseStart_4249433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249440 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_4249440 : Nat := 118140960795 + 4249440 * 2 ^ 59
def prefixEnd_4249440 : Nat := 4983230072969 + 3 ^ 40 * 4249440 * 2
def baseEnd_4249440 : Nat := 727335077480653093385729

theorem tailTrace_4249440 : CollatzResearch.WordTrace tailWord_4249440 prefixEnd_4249440 727335077480653093385729 := by
  unfold tailWord_4249440
  simp only [CollatzResearch.WordTrace]
  refine ⟨77494904862506050708736887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103326539816674734278315849 77494904862506050708736887)
  ·
    refine ⟨116242357293759076063105331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77494904862506050708736887 116242357293759076063105331)
    ·
      refine ⟨174363535940638614094657997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116242357293759076063105331 174363535940638614094657997)
      ·
        refine ⟨65386325977739480285496749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174363535940638614094657997 65386325977739480285496749)
        ·
          refine ⟨24519872241652305107061281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65386325977739480285496749 24519872241652305107061281)
          ·
            refine ⟨18389904181239228830295961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24519872241652305107061281 18389904181239228830295961)
            ·
              refine ⟨13792428135929421622721971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18389904181239228830295961 13792428135929421622721971)
              ·
                refine ⟨20688642203894132434082957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13792428135929421622721971 20688642203894132434082957)
                ·
                  refine ⟨7758240826460299662781109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20688642203894132434082957 7758240826460299662781109)
                  ·
                    refine ⟨727335077480653093385729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7758240826460299662781109 727335077480653093385729)
                    ·
                      rfl

theorem cell23_4249440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_4249440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249440 prefixEnd_4249440 := by exact prefixLift 4249440
  have htrace : WordTrace (prefixWord ++ tailWord_4249440) baseStart_4249440 baseEnd_4249440 := by
    simpa [prefixWord, tailWord_4249440, baseEnd_4249440] using wordTrace_append hprefix tailTrace_4249440
  have hstable : (prefixWord ++ tailWord_4249440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249440).length < 2 ^ (prefixWord ++ tailWord_4249440).sum := by decide
  have hdescent : baseEnd_4249440 < baseStart_4249440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249447 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_4249447 : Nat := 118140960795 + 4249447 * 2 ^ 59
def prefixEnd_4249447 : Nat := 4983230072969 + 3 ^ 40 * 4249447 * 2
def baseEnd_4249447 : Nat := 2182008826806540752769655

theorem tailTrace_4249447 : CollatzResearch.WordTrace tailWord_4249447 prefixEnd_4249447 2182008826806540752769655 := by
  unfold tailWord_4249447
  simp only [CollatzResearch.WordTrace]
  refine ⟨154990065035986741612978595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103326710023991161075319063 154990065035986741612978595)
  ·
    refine ⟨232485097553980112419467893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154990065035986741612978595 232485097553980112419467893)
    ·
      refine ⟨21795477895685635539325115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232485097553980112419467893 21795477895685635539325115)
      ·
        refine ⟨32693216843528453308987673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21795477895685635539325115 32693216843528453308987673)
        ·
          refine ⟨24519912632646339981740755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32693216843528453308987673 24519912632646339981740755)
          ·
            refine ⟨36779868948969509972611133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24519912632646339981740755 36779868948969509972611133)
            ·
              refine ⟨13792450855863566239729175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36779868948969509972611133 13792450855863566239729175)
              ·
                refine ⟨20688676283795349359593763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13792450855863566239729175 20688676283795349359593763)
                ·
                  refine ⟨31033014425693024039390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20688676283795349359593763 31033014425693024039390645)
                  ·
                    refine ⟨2909345102408721003692873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31033014425693024039390645 2909345102408721003692873)
                    ·
                      refine ⟨2182008826806540752769655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909345102408721003692873 2182008826806540752769655)
                      ·
                        rfl

theorem cell23_4249447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_4249447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249447 prefixEnd_4249447 := by exact prefixLift 4249447
  have htrace : WordTrace (prefixWord ++ tailWord_4249447) baseStart_4249447 baseEnd_4249447 := by
    simpa [prefixWord, tailWord_4249447, baseEnd_4249447] using wordTrace_append hprefix tailTrace_4249447
  have hstable : (prefixWord ++ tailWord_4249447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249447).length < 2 ^ (prefixWord ++ tailWord_4249447).sum := by decide
  have hdescent : baseEnd_4249447 < baseStart_4249447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249483 : List Nat := [1, 1, 1, 1, 4, 2, 1, 12]
def baseStart_4249483 : Nat := 118140960795 + 4249483 * 2 ^ 59
def prefixEnd_4249483 : Nat := 4983230072969 + 3 ^ 40 * 4249483 * 2
def baseEnd_4249483 : Nat := 80815826374448244885907

theorem tailTrace_4249483 : CollatzResearch.WordTrace tailWord_4249483 prefixEnd_4249483 80815826374448244885907 := by
  unfold tailWord_4249483
  simp only [CollatzResearch.WordTrace]
  refine ⟨154991378063856319761289103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103327585375904213174192735 154991378063856319761289103)
  ·
    refine ⟨232487067095784479641933655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154991378063856319761289103 232487067095784479641933655)
    ·
      refine ⟨348730600643676719462900483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232487067095784479641933655 348730600643676719462900483)
      ·
        refine ⟨523095900965515079194350725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348730600643676719462900483 523095900965515079194350725)
        ·
          refine ⟨98080481431034077348940761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 523095900965515079194350725 98080481431034077348940761)
          ·
            refine ⟨73560361073275558011705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98080481431034077348940761 73560361073275558011705571)
            ·
              refine ⟨110340541609913337017558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73560361073275558011705571 110340541609913337017558357)
              ·
                refine ⟨80815826374448244885907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 110340541609913337017558357 80815826374448244885907)
                ·
                  rfl

theorem cell23_4249483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 12].length) (baseStart_4249483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249483 prefixEnd_4249483 := by exact prefixLift 4249483
  have htrace : WordTrace (prefixWord ++ tailWord_4249483) baseStart_4249483 baseEnd_4249483 := by
    simpa [prefixWord, tailWord_4249483, baseEnd_4249483] using wordTrace_append hprefix tailTrace_4249483
  have hstable : (prefixWord ++ tailWord_4249483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249483).length < 2 ^ (prefixWord ++ tailWord_4249483).sum := by decide
  have hdescent : baseEnd_4249483 < baseStart_4249483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249497 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_4249497 : Nat := 118140960795 + 4249497 * 2 ^ 59
def prefixEnd_4249497 : Nat := 4983230072969 + 3 ^ 40 * 4249497 * 2
def baseEnd_4249497 : Nat := 2182034500839265557144425

theorem tailTrace_4249497 : CollatzResearch.WordTrace tailWord_4249497 prefixEnd_4249497 2182034500839265557144425 := by
  unfold tailWord_4249497
  simp only [CollatzResearch.WordTrace]
  refine ⟨154991888685805600152298745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103327925790537066768199163 154991888685805600152298745)
  ·
    refine ⟨116243916514354200114224059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154991888685805600152298745 116243916514354200114224059)
    ·
      refine ⟨174365874771531300171336089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116243916514354200114224059 174365874771531300171336089)
      ·
        refine ⟨130774406078648475128502067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174365874771531300171336089 130774406078648475128502067)
        ·
          refine ⟨196161609117972712692753101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130774406078648475128502067 196161609117972712692753101)
          ·
            refine ⟨73560603419239767259782413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196161609117972712692753101 73560603419239767259782413)
            ·
              refine ⟨27585226282214912722418405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73560603419239767259782413 27585226282214912722418405)
              ·
                refine ⟨5172229927915296135453451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27585226282214912722418405 5172229927915296135453451)
                ·
                  refine ⟨7758344891872944203180177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5172229927915296135453451 7758344891872944203180177)
                  ·
                    refine ⟨5818758668904708152385133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7758344891872944203180177 5818758668904708152385133)
                    ·
                      refine ⟨2182034500839265557144425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5818758668904708152385133 2182034500839265557144425)
                      ·
                        rfl

theorem cell23_4249497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_4249497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249497 prefixEnd_4249497 := by exact prefixLift 4249497
  have htrace : WordTrace (prefixWord ++ tailWord_4249497) baseStart_4249497 baseEnd_4249497 := by
    simpa [prefixWord, tailWord_4249497, baseEnd_4249497] using wordTrace_append hprefix tailTrace_4249497
  have hstable : (prefixWord ++ tailWord_4249497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249497).length < 2 ^ (prefixWord ++ tailWord_4249497).sum := by decide
  have hdescent : baseEnd_4249497 < baseStart_4249497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249505 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4249505 : Nat := 118140960795 + 4249505 * 2 ^ 59
def prefixEnd_4249505 : Nat := 4983230072969 + 3 ^ 40 * 4249505 * 2
def baseEnd_4249505 : Nat := 2182038608684501525844389

theorem tailTrace_4249505 : CollatzResearch.WordTrace tailWord_4249505 prefixEnd_4249505 2182038608684501525844389 := by
  unfold tailWord_4249505
  simp only [CollatzResearch.WordTrace]
  refine ⟨154992180469776617518589969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103328120313184411679059979 154992180469776617518589969)
  ·
    refine ⟨116244135352332463138942477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154992180469776617518589969 116244135352332463138942477)
    ·
      refine ⟨43591550757124673677103429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116244135352332463138942477 43591550757124673677103429)
      ·
        refine ⟨8173415766960876314456893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43591550757124673677103429 8173415766960876314456893)
        ·
          refine ⟨3065030912610328617921335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8173415766960876314456893 3065030912610328617921335)
          ·
            refine ⟨4597546368915492926882003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065030912610328617921335 4597546368915492926882003)
            ·
              refine ⟨6896319553373239390323005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597546368915492926882003 6896319553373239390323005)
              ·
                refine ⟨2586119832514964771371127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6896319553373239390323005 2586119832514964771371127)
                ·
                  refine ⟨3879179748772447157056691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586119832514964771371127 3879179748772447157056691)
                  ·
                    refine ⟨5818769623158670735585037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879179748772447157056691 5818769623158670735585037)
                    ·
                      refine ⟨2182038608684501525844389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5818769623158670735585037 2182038608684501525844389)
                      ·
                        rfl

theorem cell23_4249505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4249505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249505 prefixEnd_4249505 := by exact prefixLift 4249505
  have htrace : WordTrace (prefixWord ++ tailWord_4249505) baseStart_4249505 baseEnd_4249505 := by
    simpa [prefixWord, tailWord_4249505, baseEnd_4249505] using wordTrace_append hprefix tailTrace_4249505
  have hstable : (prefixWord ++ tailWord_4249505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249505).length < 2 ^ (prefixWord ++ tailWord_4249505).sum := by decide
  have hdescent : baseEnd_4249505 < baseStart_4249505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249528 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_4249528 : Nat := 118140960795 + 4249528 * 2 ^ 59
def prefixEnd_4249528 : Nat := 4983230072969 + 3 ^ 40 * 4249528 * 2
def baseEnd_4249528 : Nat := 2182050418739554935856783

theorem tailTrace_4249528 : CollatzResearch.WordTrace tailWord_4249528 prefixEnd_4249528 2182050418739554935856783 := by
  unfold tailWord_4249528
  simp only [CollatzResearch.WordTrace]
  refine ⟨77496509674346646223338619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103328679565795528297784825 77496509674346646223338619)
  ·
    refine ⟨116244764511519969335007929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77496509674346646223338619 116244764511519969335007929)
    ·
      refine ⟨87183573383639977001255947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116244764511519969335007929 87183573383639977001255947)
      ·
        refine ⟨130775360075459965501883921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87183573383639977001255947 130775360075459965501883921)
        ·
          refine ⟨98081520056594974126412941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130775360075459965501883921 98081520056594974126412941)
          ·
            refine ⟨36780570021223115297404853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98081520056594974126412941 36780570021223115297404853)
            ·
              refine ⟨3448178439489667059131705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36780570021223115297404853 3448178439489667059131705)
              ·
                refine ⟨2586133829617250294348779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448178439489667059131705 2586133829617250294348779)
                ·
                  refine ⟨3879200744425875441523169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586133829617250294348779 3879200744425875441523169)
                  ·
                    refine ⟨2909400558319406581142377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879200744425875441523169 2909400558319406581142377)
                    ·
                      refine ⟨2182050418739554935856783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909400558319406581142377 2182050418739554935856783)
                      ·
                        rfl

theorem cell23_4249528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_4249528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249528 prefixEnd_4249528 := by exact prefixLift 4249528
  have htrace : WordTrace (prefixWord ++ tailWord_4249528) baseStart_4249528 baseEnd_4249528 := by
    simpa [prefixWord, tailWord_4249528, baseEnd_4249528] using wordTrace_append hprefix tailTrace_4249528
  have hstable : (prefixWord ++ tailWord_4249528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249528).length < 2 ^ (prefixWord ++ tailWord_4249528).sum := by decide
  have hdescent : baseEnd_4249528 < baseStart_4249528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249580 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_4249580 : Nat := 118140960795 + 4249580 * 2 ^ 59
def prefixEnd_4249580 : Nat := 4983230072969 + 3 ^ 40 * 4249580 * 2
def baseEnd_4249580 : Nat := 2182077119733588732406543

theorem tailTrace_4249580 : CollatzResearch.WordTrace tailWord_4249580 prefixEnd_4249580 2182077119733588732406543 := by
  unfold tailWord_4249580
  simp only [CollatzResearch.WordTrace]
  refine ⟨77497457972252452663785097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103329943963003270218380129 77497457972252452663785097)
  ·
    refine ⟨58123093479189339497838823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77497457972252452663785097 58123093479189339497838823)
    ·
      refine ⟨87184640218784009246758235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58123093479189339497838823 87184640218784009246758235)
      ·
        refine ⟨130776960328176013870137353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87184640218784009246758235 130776960328176013870137353)
        ·
          refine ⟨98082720246132010402603015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130776960328176013870137353 98082720246132010402603015)
          ·
            refine ⟨147124080369198015603904523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98082720246132010402603015 147124080369198015603904523)
            ·
              refine ⟨220686120553797023405856785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147124080369198015603904523 220686120553797023405856785)
              ·
                refine ⟨165514590415347767554392589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220686120553797023405856785 165514590415347767554392589)
                ·
                  refine ⟨62067971405755412832897221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165514590415347767554392589 62067971405755412832897221)
                  ·
                    refine ⟨11637744638579139906168229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62067971405755412832897221 11637744638579139906168229)
                    ·
                      refine ⟨2182077119733588732406543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11637744638579139906168229 2182077119733588732406543)
                      ·
                        rfl

theorem cell23_4249580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_4249580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249580 prefixEnd_4249580 := by exact prefixLift 4249580
  have htrace : WordTrace (prefixWord ++ tailWord_4249580) baseStart_4249580 baseEnd_4249580 := by
    simpa [prefixWord, tailWord_4249580, baseEnd_4249580] using wordTrace_append hprefix tailTrace_4249580
  have hstable : (prefixWord ++ tailWord_4249580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249580).length < 2 ^ (prefixWord ++ tailWord_4249580).sum := by decide
  have hdescent : baseEnd_4249580 < baseStart_4249580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249584 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2]
def baseStart_4249584 : Nat := 118140960795 + 4249584 * 2 ^ 59
def prefixEnd_4249584 : Nat := 4983230072969 + 3 ^ 40 * 4249584 * 2
def baseEnd_4249584 : Nat := 2182079173656206716756525

theorem tailTrace_4249584 : CollatzResearch.WordTrace tailWord_4249584 prefixEnd_4249584 2182079173656206716756525 := by
  unfold tailWord_4249584
  simp only [CollatzResearch.WordTrace]
  refine ⟨77497530918245207005357903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103330041224326942673810537 77497530918245207005357903)
  ·
    refine ⟨116246296377367810508036855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77497530918245207005357903 116246296377367810508036855)
    ·
      refine ⟨174369444566051715762055283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116246296377367810508036855 174369444566051715762055283)
      ·
        refine ⟨261554166849077573643082925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174369444566051715762055283 261554166849077573643082925)
        ·
          refine ⟨98082812568404090116156097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261554166849077573643082925 98082812568404090116156097)
          ·
            refine ⟨73562109426303067587117073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98082812568404090116156097 73562109426303067587117073)
            ·
              refine ⟨55171582069727300690337805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73562109426303067587117073 55171582069727300690337805)
              ·
                refine ⟨20689343276147737758876677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55171582069727300690337805 20689343276147737758876677)
                ·
                  refine ⟨3879251864277700829789377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20689343276147737758876677 3879251864277700829789377)
                  ·
                    refine ⟨2909438898208275622342033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879251864277700829789377 2909438898208275622342033)
                    ·
                      refine ⟨2182079173656206716756525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909438898208275622342033 2182079173656206716756525)
                      ·
                        rfl

theorem cell23_4249584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2].length) (baseStart_4249584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249584 prefixEnd_4249584 := by exact prefixLift 4249584
  have htrace : WordTrace (prefixWord ++ tailWord_4249584) baseStart_4249584 baseEnd_4249584 := by
    simpa [prefixWord, tailWord_4249584, baseEnd_4249584] using wordTrace_append hprefix tailTrace_4249584
  have hstable : (prefixWord ++ tailWord_4249584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249584).length < 2 ^ (prefixWord ++ tailWord_4249584).sum := by decide
  have hdescent : baseEnd_4249584 < baseStart_4249584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249601 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_4249601 : Nat := 118140960795 + 4249601 * 2 ^ 59
def prefixEnd_4249601 : Nat := 4983230072969 + 3 ^ 40 * 4249601 * 2
def baseEnd_4249601 : Nat := 2182087902827333150243947

theorem tailTrace_4249601 : CollatzResearch.WordTrace tailWord_4249601 prefixEnd_4249601 2182087902827333150243947 := by
  unfold tailWord_4249601
  simp only [CollatzResearch.WordTrace]
  refine ⟨154995681877428825914084657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103330454584952550609389771 154995681877428825914084657)
  ·
    refine ⟨116246761408071619435563493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154995681877428825914084657 116246761408071619435563493)
    ·
      refine ⟨21796267764013428644168155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116246761408071619435563493 21796267764013428644168155)
      ·
        refine ⟨32694401646020142966252233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21796267764013428644168155 32694401646020142966252233)
        ·
          refine ⟨24520801234515107224689175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32694401646020142966252233 24520801234515107224689175)
          ·
            refine ⟨36781201851772660837033763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24520801234515107224689175 36781201851772660837033763)
            ·
              refine ⟨55171802777658991255550645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36781201851772660837033763 55171802777658991255550645)
              ·
                refine ⟨5172356510405530430207873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55171802777658991255550645 5172356510405530430207873)
                ·
                  refine ⟨3879267382804147822655905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5172356510405530430207873 3879267382804147822655905)
                  ·
                    refine ⟨2909450537103110866991929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879267382804147822655905 2909450537103110866991929)
                    ·
                      refine ⟨2182087902827333150243947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909450537103110866991929 2182087902827333150243947)
                      ·
                        rfl

theorem cell23_4249601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_4249601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249601 prefixEnd_4249601 := by exact prefixLift 4249601
  have htrace : WordTrace (prefixWord ++ tailWord_4249601) baseStart_4249601 baseEnd_4249601 := by
    simpa [prefixWord, tailWord_4249601, baseEnd_4249601] using wordTrace_append hprefix tailTrace_4249601
  have hstable : (prefixWord ++ tailWord_4249601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249601).length < 2 ^ (prefixWord ++ tailWord_4249601).sum := by decide
  have hdescent : baseEnd_4249601 < baseStart_4249601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249607 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 7]
def baseStart_4249607 : Nat := 118140960795 + 4249607 * 2 ^ 59
def prefixEnd_4249607 : Nat := 4983230072969 + 3 ^ 40 * 4249607 * 2
def baseEnd_4249607 : Nat := 242454553745695569640991

theorem tailTrace_4249607 : CollatzResearch.WordTrace tailWord_4249607 prefixEnd_4249607 242454553745695569640991 := by
  unfold tailWord_4249607
  simp only [CollatzResearch.WordTrace]
  refine ⟨154995900715407088938803075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103330600476938059292535383 154995900715407088938803075)
  ·
    refine ⟨232493851073110633408204613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154995900715407088938803075 232493851073110633408204613)
    ·
      refine ⟨43592597076208243764038365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232493851073110633408204613 43592597076208243764038365)
      ·
        refine ⟨16347223903578091411514387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43592597076208243764038365 16347223903578091411514387)
        ·
          refine ⟨24520835855367137117271581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347223903578091411514387 24520835855367137117271581)
          ·
            refine ⟨9195313445762676418976843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24520835855367137117271581 9195313445762676418976843)
            ·
              refine ⟨13792970168644014628465265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9195313445762676418976843 13792970168644014628465265)
              ·
                refine ⟨10344727626483010971348949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13792970168644014628465265 10344727626483010971348949)
                ·
                  refine ⟨242454553745695569640991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10344727626483010971348949 242454553745695569640991)
                  ·
                    rfl

theorem cell23_4249607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 7].length) (baseStart_4249607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249607 prefixEnd_4249607 := by exact prefixLift 4249607
  have htrace : WordTrace (prefixWord ++ tailWord_4249607) baseStart_4249607 baseEnd_4249607 := by
    simpa [prefixWord, tailWord_4249607, baseEnd_4249607] using wordTrace_append hprefix tailTrace_4249607
  have hstable : (prefixWord ++ tailWord_4249607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249607).length < 2 ^ (prefixWord ++ tailWord_4249607).sum := by decide
  have hdescent : baseEnd_4249607 < baseStart_4249607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249624 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 5]
def baseStart_4249624 : Nat := 118140960795 + 4249624 * 2 ^ 59
def prefixEnd_4249624 : Nat := 4983230072969 + 3 ^ 40 * 4249624 * 2
def baseEnd_4249624 : Nat := 242455523653598506695149

theorem tailTrace_4249624 : CollatzResearch.WordTrace tailWord_4249624 prefixEnd_4249624 242455523653598506695149 := by
  unfold tailWord_4249624
  simp only [CollatzResearch.WordTrace]
  refine ⟨77498260378172750421085963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103331013837563667228114617 77498260378172750421085963)
  ·
    refine ⟨116247390567259125631628945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77498260378172750421085963 116247390567259125631628945)
    ·
      refine ⟨87185542925444344223721709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116247390567259125631628945 87185542925444344223721709)
      ·
        refine ⟨32694578597041629083895641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87185542925444344223721709 32694578597041629083895641)
        ·
          refine ⟨24520933947781221812921731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32694578597041629083895641 24520933947781221812921731)
          ·
            refine ⟨36781400921671832719382597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24520933947781221812921731 36781400921671832719382597)
            ·
              refine ⟨6896512672813468634884237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36781400921671832719382597 6896512672813468634884237)
              ·
                refine ⟨2586192252305050738081589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6896512672813468634884237 2586192252305050738081589)
                ·
                  refine ⟨242455523653598506695149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586192252305050738081589 242455523653598506695149)
                  ·
                    rfl

theorem cell23_4249624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 5].length) (baseStart_4249624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249624 prefixEnd_4249624 := by exact prefixLift 4249624
  have htrace : WordTrace (prefixWord ++ tailWord_4249624) baseStart_4249624 baseEnd_4249624 := by
    simpa [prefixWord, tailWord_4249624, baseEnd_4249624] using wordTrace_append hprefix tailTrace_4249624
  have hstable : (prefixWord ++ tailWord_4249624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249624).length < 2 ^ (prefixWord ++ tailWord_4249624).sum := by decide
  have hdescent : baseEnd_4249624 < baseStart_4249624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249627 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 7, 2]
def baseStart_4249627 : Nat := 118140960795 + 4249627 * 2 ^ 59
def prefixEnd_4249627 : Nat := 4983230072969 + 3 ^ 40 * 4249627 * 2
def baseEnd_4249627 : Nat := 2182101253324350048518827

theorem tailTrace_4249627 : CollatzResearch.WordTrace tailWord_4249627 prefixEnd_4249627 2182101253324350048518827 := by
  unfold tailWord_4249627
  simp only [CollatzResearch.WordTrace]
  refine ⟨154996630175334632354531135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103331086783556421569687423 154996630175334632354531135)
  ·
    refine ⟨232494945263001948531796703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154996630175334632354531135 232494945263001948531796703)
    ·
      refine ⟨348742417894502922797695055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232494945263001948531796703 348742417894502922797695055)
      ·
        refine ⟨523113626841754384196542583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348742417894502922797695055 523113626841754384196542583)
        ·
          refine ⟨784670440262631576294813875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523113626841754384196542583 784670440262631576294813875)
          ·
            refine ⟨1177005660393947364442220813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784670440262631576294813875 1177005660393947364442220813)
            ·
              refine ⟨441377122647730261665832805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177005660393947364442220813 441377122647730261665832805)
              ·
                refine ⟨82758210496449424062343651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441377122647730261665832805 82758210496449424062343651)
                ·
                  refine ⟨124137315744674136093515477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82758210496449424062343651 124137315744674136093515477)
                  ·
                    refine ⟨2909468337765800064691769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 124137315744674136093515477 2909468337765800064691769)
                    ·
                      refine ⟨2182101253324350048518827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909468337765800064691769 2182101253324350048518827)
                      ·
                        rfl

theorem cell23_4249627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7, 2].length) (baseStart_4249627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249627 prefixEnd_4249627 := by exact prefixLift 4249627
  have htrace : WordTrace (prefixWord ++ tailWord_4249627) baseStart_4249627 baseEnd_4249627 := by
    simpa [prefixWord, tailWord_4249627, baseEnd_4249627] using wordTrace_append hprefix tailTrace_4249627
  have hstable : (prefixWord ++ tailWord_4249627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249627).length < 2 ^ (prefixWord ++ tailWord_4249627).sum := by decide
  have hdescent : baseEnd_4249627 < baseStart_4249627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249652 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4249652 : Nat := 118140960795 + 4249652 * 2 ^ 59
def prefixEnd_4249652 : Nat := 4983230072969 + 3 ^ 40 * 4249652 * 2
def baseEnd_4249652 : Nat := 2182114090340712450706213

theorem tailTrace_4249652 : CollatzResearch.WordTrace tailWord_4249652 prefixEnd_4249652 2182114090340712450706213 := by
  unfold tailWord_4249652
  simp only [CollatzResearch.WordTrace]
  refine ⟨77498771000122030812095605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103331694666829374416127473 77498771000122030812095605)
  ·
    refine ⟨7265509781261440388633963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77498771000122030812095605 7265509781261440388633963)
    ·
      refine ⟨10898264671892160582950945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7265509781261440388633963 10898264671892160582950945)
      ·
        refine ⟨8173698503919120437213209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10898264671892160582950945 8173698503919120437213209)
        ·
          refine ⟨6130273877939340327909907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8173698503919120437213209 6130273877939340327909907)
          ·
            refine ⟨9195410816909010491864861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130273877939340327909907 9195410816909010491864861)
            ·
              refine ⟨3448279056340878934449323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9195410816909010491864861 3448279056340878934449323)
              ·
                refine ⟨5172418584511318401673985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448279056340878934449323 5172418584511318401673985)
                ·
                  refine ⟨3879313938383488801255489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5172418584511318401673985 3879313938383488801255489)
                  ·
                    refine ⟨2909485453787616600941617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879313938383488801255489 2909485453787616600941617)
                    ·
                      refine ⟨2182114090340712450706213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909485453787616600941617 2182114090340712450706213)
                      ·
                        rfl

theorem cell23_4249652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4249652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249652 prefixEnd_4249652 := by exact prefixLift 4249652
  have htrace : WordTrace (prefixWord ++ tailWord_4249652) baseStart_4249652 baseEnd_4249652 := by
    simpa [prefixWord, tailWord_4249652, baseEnd_4249652] using wordTrace_append hprefix tailTrace_4249652
  have hstable : (prefixWord ++ tailWord_4249652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249652).length < 2 ^ (prefixWord ++ tailWord_4249652).sum := by decide
  have hdescent : baseEnd_4249652 < baseStart_4249652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249667 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 5, 4]
def baseStart_4249667 : Nat := 118140960795 + 4249667 * 2 ^ 59
def prefixEnd_4249667 : Nat := 4983230072969 + 3 ^ 40 * 4249667 * 2
def baseEnd_4249667 : Nat := 727373930850176630672881

theorem tailTrace_4249667 : CollatzResearch.WordTrace tailWord_4249667 prefixEnd_4249667 727373930850176630672881 := by
  unfold tailWord_4249667
  simp only [CollatzResearch.WordTrace]
  refine ⟨154998089095189719185987255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103332059396793146123991503 154998089095189719185987255)
  ·
    refine ⟨232497133642784578778980883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154998089095189719185987255 232497133642784578778980883)
    ·
      refine ⟨348745700464176868168471325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232497133642784578778980883 348745700464176868168471325)
      ·
        refine ⟨130779637674066325563176747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348745700464176868168471325 130779637674066325563176747)
        ·
          refine ⟨196169456511099488344765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130779637674066325563176747 196169456511099488344765121)
          ·
            refine ⟨147127092383324616258573841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196169456511099488344765121 147127092383324616258573841)
            ·
              refine ⟨110345319287493462193930381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147127092383324616258573841 110345319287493462193930381)
              ·
                refine ⟨41379494732810048322723893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110345319287493462193930381 41379494732810048322723893)
                ·
                  refine ⟨3879327631200942030255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41379494732810048322723893 3879327631200942030255365)
                  ·
                    refine ⟨727373930850176630672881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879327631200942030255365 727373930850176630672881)
                    ·
                      rfl

theorem cell23_4249667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 4].length) (baseStart_4249667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249667 prefixEnd_4249667 := by exact prefixLift 4249667
  have htrace : WordTrace (prefixWord ++ tailWord_4249667) baseStart_4249667 baseEnd_4249667 := by
    simpa [prefixWord, tailWord_4249667, baseEnd_4249667] using wordTrace_append hprefix tailTrace_4249667
  have hstable : (prefixWord ++ tailWord_4249667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249667).length < 2 ^ (prefixWord ++ tailWord_4249667).sum := by decide
  have hdescent : baseEnd_4249667 < baseStart_4249667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249697 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 6]
def baseStart_4249697 : Nat := 118140960795 + 4249697 * 2 ^ 59
def prefixEnd_4249697 : Nat := 4983230072969 + 3 ^ 40 * 4249697 * 2
def baseEnd_4249697 : Nat := 242459688552240530515945

theorem tailTrace_4249697 : CollatzResearch.WordTrace tailWord_4249697 prefixEnd_4249697 242459688552240530515945 := by
  unfold tailWord_4249697
  simp only [CollatzResearch.WordTrace]
  refine ⟨154999183285081034309579345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103332788856720689539719563 154999183285081034309579345)
  ·
    refine ⟨116249387463810775732184509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154999183285081034309579345 116249387463810775732184509)
    ·
      refine ⟨43593520298929040899569191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116249387463810775732184509 43593520298929040899569191)
      ·
        refine ⟨65390280448393561349353787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43593520298929040899569191 65390280448393561349353787)
        ·
          refine ⟨98085420672590342024030681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65390280448393561349353787 98085420672590342024030681)
          ·
            refine ⟨73564065504442756518023011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98085420672590342024030681 73564065504442756518023011)
            ·
              refine ⟨110346098256664134777034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73564065504442756518023011 110346098256664134777034517)
              ·
                refine ⟨5172473355781131317673493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110346098256664134777034517 5172473355781131317673493)
                ·
                  refine ⟨242459688552240530515945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5172473355781131317673493 242459688552240530515945)
                  ·
                    rfl

theorem cell23_4249697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_4249697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249697 prefixEnd_4249697 := by exact prefixLift 4249697
  have htrace : WordTrace (prefixWord ++ tailWord_4249697) baseStart_4249697 baseEnd_4249697 := by
    simpa [prefixWord, tailWord_4249697, baseEnd_4249697] using wordTrace_append hprefix tailTrace_4249697
  have hstable : (prefixWord ++ tailWord_4249697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249697).length < 2 ^ (prefixWord ++ tailWord_4249697).sum := by decide
  have hdescent : baseEnd_4249697 < baseStart_4249697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249701 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_4249701 : Nat := 118140960795 + 4249701 * 2 ^ 59
def prefixEnd_4249701 : Nat := 4983230072969 + 3 ^ 40 * 4249701 * 2
def baseEnd_4249701 : Nat := 727379750297594252997829

theorem tailTrace_4249701 : CollatzResearch.WordTrace tailWord_4249701 prefixEnd_4249701 727379750297594252997829 := by
  unfold tailWord_4249701
  simp only [CollatzResearch.WordTrace]
  refine ⟨154999329177066542992724957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103332886118044361995149971 154999329177066542992724957)
  ·
    refine ⟨58124748441399953622271859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154999329177066542992724957 58124748441399953622271859)
    ·
      refine ⟨87187122662099930433407789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58124748441399953622271859 87187122662099930433407789)
      ·
        refine ⟨32695170998287473912527921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87187122662099930433407789 32695170998287473912527921)
        ·
          refine ⟨24521378248715605434395941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32695170998287473912527921 24521378248715605434395941)
          ·
            refine ⟨4597758421634176018949239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24521378248715605434395941 4597758421634176018949239)
            ·
              refine ⟨6896637632451264028423859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597758421634176018949239 6896637632451264028423859)
              ·
                refine ⟨10344956448676896042635789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6896637632451264028423859 10344956448676896042635789)
                ·
                  refine ⟨3879358668253836015988421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10344956448676896042635789 3879358668253836015988421)
                  ·
                    refine ⟨727379750297594252997829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879358668253836015988421 727379750297594252997829)
                    ·
                      rfl

theorem cell23_4249701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_4249701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249701 prefixEnd_4249701 := by exact prefixLift 4249701
  have htrace : WordTrace (prefixWord ++ tailWord_4249701) baseStart_4249701 baseEnd_4249701 := by
    simpa [prefixWord, tailWord_4249701, baseEnd_4249701] using wordTrace_append hprefix tailTrace_4249701
  have hstable : (prefixWord ++ tailWord_4249701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249701).length < 2 ^ (prefixWord ++ tailWord_4249701).sum := by decide
  have hdescent : baseEnd_4249701 < baseStart_4249701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249714 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_4249714 : Nat := 118140960795 + 4249714 * 2 ^ 59
def prefixEnd_4249714 : Nat := 4983230072969 + 3 ^ 40 * 4249714 * 2
def baseEnd_4249714 : Nat := 242460658460143467570103

theorem tailTrace_4249714 : CollatzResearch.WordTrace tailWord_4249714 prefixEnd_4249714 242460658460143467570103 := by
  unfold tailWord_4249714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38749950831504861553237049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103333202217346297475298797 38749950831504861553237049)
  ·
    refine ⟨29062463123628646164927787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38749950831504861553237049 29062463123628646164927787)
    ·
      refine ⟨43593694685442969247391681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29062463123628646164927787 43593694685442969247391681)
      ·
        refine ⟨32695271014082226935543761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43593694685442969247391681 32695271014082226935543761)
        ·
          refine ⟨24521453260561670201657821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32695271014082226935543761 24521453260561670201657821)
          ·
            refine ⟨9195544972710626325621683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24521453260561670201657821 9195544972710626325621683)
            ·
              refine ⟨13793317459065939488432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9195544972710626325621683 13793317459065939488432525)
              ·
                refine ⟨5172494047149727308162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13793317459065939488432525 5172494047149727308162197)
                ·
                  refine ⟨242460658460143467570103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5172494047149727308162197 242460658460143467570103)
                  ·
                    rfl

theorem cell23_4249714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_4249714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249714 prefixEnd_4249714 := by exact prefixLift 4249714
  have htrace : WordTrace (prefixWord ++ tailWord_4249714) baseStart_4249714 baseEnd_4249714 := by
    simpa [prefixWord, tailWord_4249714, baseEnd_4249714] using wordTrace_append hprefix tailTrace_4249714
  have hstable : (prefixWord ++ tailWord_4249714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249714).length < 2 ^ (prefixWord ++ tailWord_4249714).sum := by decide
  have hdescent : baseEnd_4249714 < baseStart_4249714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249748 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 6]
def baseStart_4249748 : Nat := 118140960795 + 4249748 * 2 ^ 59
def prefixEnd_4249748 : Nat := 4983230072969 + 3 ^ 40 * 4249748 * 2
def baseEnd_4249748 : Nat := 242462598275949341678419

theorem tailTrace_4249748 : CollatzResearch.WordTrace tailWord_4249748 prefixEnd_4249748 242462598275949341678419 := by
  unfold tailWord_4249748
  simp only [CollatzResearch.WordTrace]
  refine ⟨77500521703948135009842949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103334028938597513346457265 77500521703948135009842949)
  ·
    refine ⟨14531347819490275314345553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77500521703948135009842949 14531347819490275314345553)
    ·
      refine ⟨10898510864617706485759165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14531347819490275314345553 10898510864617706485759165)
      ·
        refine ⟨4086941574231639932159687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10898510864617706485759165 4086941574231639932159687)
        ·
          refine ⟨6130412361347459898239531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086941574231639932159687 6130412361347459898239531)
          ·
            refine ⟨9195618542021189847359297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130412361347459898239531 9195618542021189847359297)
            ·
              refine ⟨6896713906515892385519473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9195618542021189847359297 6896713906515892385519473)
              ·
                refine ⟨5172535429886919289139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6896713906515892385519473 5172535429886919289139605)
                ·
                  refine ⟨242462598275949341678419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5172535429886919289139605 242462598275949341678419)
                  ·
                    rfl

theorem cell23_4249748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_4249748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249748 prefixEnd_4249748 := by exact prefixLift 4249748
  have htrace : WordTrace (prefixWord ++ tailWord_4249748) baseStart_4249748 baseEnd_4249748 := by
    simpa [prefixWord, tailWord_4249748, baseEnd_4249748] using wordTrace_append hprefix tailTrace_4249748
  have hstable : (prefixWord ++ tailWord_4249748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249748).length < 2 ^ (prefixWord ++ tailWord_4249748).sum := by decide
  have hdescent : baseEnd_4249748 < baseStart_4249748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249752 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 1, 4]
def baseStart_4249752 : Nat := 118140960795 + 4249752 * 2 ^ 59
def prefixEnd_4249752 : Nat := 4983230072969 + 3 ^ 40 * 4249752 * 2
def baseEnd_4249752 : Nat := 727388479468720686485251

theorem tailTrace_4249752 : CollatzResearch.WordTrace tailWord_4249752 prefixEnd_4249752 727388479468720686485251 := by
  unfold tailWord_4249752
  simp only [CollatzResearch.WordTrace]
  refine ⟨77500594649940889351415755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103334126199921185801887673 77500594649940889351415755)
  ·
    refine ⟨116250891974911334027123633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77500594649940889351415755 116250891974911334027123633)
    ·
      refine ⟨87188168981183500520342725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116250891974911334027123633 87188168981183500520342725)
      ·
        refine ⟨16347781683971906347564261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87188168981183500520342725 16347781683971906347564261)
        ·
          refine ⟨3065209065744732440168299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16347781683971906347564261 3065209065744732440168299)
          ·
            refine ⟨4597813598617098660252449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065209065744732440168299 4597813598617098660252449)
            ·
              refine ⟨3448360198962823995189337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597813598617098660252449 3448360198962823995189337)
              ·
                refine ⟨2586270149222117996392003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448360198962823995189337 2586270149222117996392003)
                ·
                  refine ⟨3879405223833176994588005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586270149222117996392003 3879405223833176994588005)
                  ·
                    refine ⟨727388479468720686485251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879405223833176994588005 727388479468720686485251)
                    ·
                      rfl

theorem cell23_4249752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_4249752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249752 prefixEnd_4249752 := by exact prefixLift 4249752
  have htrace : WordTrace (prefixWord ++ tailWord_4249752) baseStart_4249752 baseEnd_4249752 := by
    simpa [prefixWord, tailWord_4249752, baseEnd_4249752] using wordTrace_append hprefix tailTrace_4249752
  have hstable : (prefixWord ++ tailWord_4249752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249752).length < 2 ^ (prefixWord ++ tailWord_4249752).sum := by decide
  have hdescent : baseEnd_4249752 < baseStart_4249752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249784 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_4249784 : Nat := 118140960795 + 4249784 * 2 ^ 59
def prefixEnd_4249784 : Nat := 4983230072969 + 3 ^ 40 * 4249784 * 2
def baseEnd_4249784 : Nat := 2182181869787105934255605

theorem tailTrace_4249784 : CollatzResearch.WordTrace tailWord_4249784 prefixEnd_4249784 2182181869787105934255605 := by
  unfold tailWord_4249784
  simp only [CollatzResearch.WordTrace]
  refine ⟨77501178217882924083998203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103334904290510565445330937 77501178217882924083998203)
  ·
    refine ⟨116251767326824386125997305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77501178217882924083998203 116251767326824386125997305)
    ·
      refine ⟨87188825495118289594497979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116251767326824386125997305 87188825495118289594497979)
      ·
        refine ⟨130783238242677434391746969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87188825495118289594497979 130783238242677434391746969)
        ·
          refine ⟨98087428682008075793810227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130783238242677434391746969 98087428682008075793810227)
          ·
            refine ⟨147131143023012113690715341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98087428682008075793810227 147131143023012113690715341)
            ·
              refine ⟨55174178633629542634018253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147131143023012113690715341 55174178633629542634018253)
              ·
                refine ⟨20690316987611078487756845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55174178633629542634018253 20690316987611078487756845)
                ·
                  refine ⟨7758868870354154432908817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20690316987611078487756845 7758868870354154432908817)
                  ·
                    refine ⟨5819151652765615824681613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7758868870354154432908817 5819151652765615824681613)
                    ·
                      refine ⟨2182181869787105934255605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819151652765615824681613 2182181869787105934255605)
                      ·
                        rfl

theorem cell23_4249784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_4249784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249784 prefixEnd_4249784 := by exact prefixLift 4249784
  have htrace : WordTrace (prefixWord ++ tailWord_4249784) baseStart_4249784 baseEnd_4249784 := by
    simpa [prefixWord, tailWord_4249784, baseEnd_4249784] using wordTrace_append hprefix tailTrace_4249784
  have hstable : (prefixWord ++ tailWord_4249784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249784).length < 2 ^ (prefixWord ++ tailWord_4249784).sum := by decide
  have hdescent : baseEnd_4249784 < baseStart_4249784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249817 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_4249817 : Nat := 118140960795 + 4249817 * 2 ^ 59
def prefixEnd_4249817 : Nat := 4983230072969 + 3 ^ 40 * 4249817 * 2
def baseEnd_4249817 : Nat := 727399604882901435047651

theorem tailTrace_4249817 : CollatzResearch.WordTrace tailWord_4249817 prefixEnd_4249817 727399604882901435047651 := by
  unfold tailWord_4249817
  simp only [CollatzResearch.WordTrace]
  refine ⟨155003560044646294803947705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103335706696430863202631803 155003560044646294803947705)
  ·
    refine ⟨116252670033484721102960779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155003560044646294803947705 116252670033484721102960779)
    ·
      refine ⟨174379005050227081654441169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116252670033484721102960779 174379005050227081654441169)
      ·
        refine ⟨130784253787670311240830877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174379005050227081654441169 130784253787670311240830877)
        ·
          refine ⟨49044095170376366715311579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130784253787670311240830877 49044095170376366715311579)
          ·
            refine ⟨73566142755564550072967369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49044095170376366715311579 73566142755564550072967369)
            ·
              refine ⟨55174607066673412554725527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73566142755564550072967369 55174607066673412554725527)
              ·
                refine ⟨82761910600010118832088291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55174607066673412554725527 82761910600010118832088291)
                ·
                  refine ⟨124142865900015178248132437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82761910600010118832088291 124142865900015178248132437)
                  ·
                    refine ⟨727399604882901435047651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 124142865900015178248132437 727399604882901435047651)
                    ·
                      rfl

theorem cell23_4249817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_4249817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249817 prefixEnd_4249817 := by exact prefixLift 4249817
  have htrace : WordTrace (prefixWord ++ tailWord_4249817) baseStart_4249817 baseEnd_4249817 := by
    simpa [prefixWord, tailWord_4249817, baseEnd_4249817] using wordTrace_append hprefix tailTrace_4249817
  have hstable : (prefixWord ++ tailWord_4249817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249817).length < 2 ^ (prefixWord ++ tailWord_4249817).sum := by decide
  have hdescent : baseEnd_4249817 < baseStart_4249817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249841 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_4249841 : Nat := 118140960795 + 4249841 * 2 ^ 59
def prefixEnd_4249841 : Nat := 4983230072969 + 3 ^ 40 * 4249841 * 2
def baseEnd_4249841 : Nat := 2182211138184412211242843

theorem tailTrace_4249841 : CollatzResearch.WordTrace tailWord_4249841 prefixEnd_4249841 2182211138184412211242843 := by
  unfold tailWord_4249841
  simp only [CollatzResearch.WordTrace]
  refine ⟨155004435396559346902821377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103336290264372897935214251 155004435396559346902821377)
  ·
    refine ⟨116253326547419510177116033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155004435396559346902821377 116253326547419510177116033)
    ·
      refine ⟨87189994910564632632837025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116253326547419510177116033 87189994910564632632837025)
      ·
        refine ⟨65392496182923474474627769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87189994910564632632837025 65392496182923474474627769)
        ·
          refine ⟨49044372137192605855970827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65392496182923474474627769 49044372137192605855970827)
          ·
            refine ⟨73566558205788908783956241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49044372137192605855970827 73566558205788908783956241)
            ·
              refine ⟨55174918654341681587967181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73566558205788908783956241 55174918654341681587967181)
              ·
                refine ⟨20690594495378130595487693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55174918654341681587967181 20690594495378130595487693)
                ·
                  refine ⟨7758972935766798973307885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20690594495378130595487693 7758972935766798973307885)
                  ·
                    refine ⟨2909614850912549614990457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7758972935766798973307885 2909614850912549614990457)
                    ·
                      refine ⟨2182211138184412211242843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909614850912549614990457 2182211138184412211242843)
                      ·
                        rfl

theorem cell23_4249841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_4249841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249841 prefixEnd_4249841 := by exact prefixLift 4249841
  have htrace : WordTrace (prefixWord ++ tailWord_4249841) baseStart_4249841 baseEnd_4249841 := by
    simpa [prefixWord, tailWord_4249841, baseEnd_4249841] using wordTrace_append hprefix tailTrace_4249841
  have hstable : (prefixWord ++ tailWord_4249841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249841).length < 2 ^ (prefixWord ++ tailWord_4249841).sum := by decide
  have hdescent : baseEnd_4249841 < baseStart_4249841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249882 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_4249882 : Nat := 118140960795 + 4249882 * 2 ^ 59
def prefixEnd_4249882 : Nat := 4983230072969 + 3 ^ 40 * 4249882 * 2
def baseEnd_4249882 : Nat := 2182232190891246550830155

theorem tailTrace_4249882 : CollatzResearch.WordTrace tailWord_4249882 prefixEnd_4249882 2182232190891246550830155 := by
  unfold tailWord_4249882
  simp only [CollatzResearch.WordTrace]
  refine ⟨38751482697352702726265975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103337287192940540603375933 38751482697352702726265975)
  ·
    refine ⟨58127224046029054089398963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38751482697352702726265975 58127224046029054089398963)
    ·
      refine ⟨87190836069043581134098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58127224046029054089398963 87190836069043581134098445)
      ·
        refine ⟨32696563525891342925286917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87190836069043581134098445 32696563525891342925286917)
        ·
          refine ⟨6130605661104626798491297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32696563525891342925286917 6130605661104626798491297)
          ·
            refine ⟨4597954245828470098868473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6130605661104626798491297 4597954245828470098868473)
            ·
              refine ⟨3448465684371352574151355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597954245828470098868473 3448465684371352574151355)
              ·
                refine ⟨5172698526557028861227033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448465684371352574151355 5172698526557028861227033)
                ·
                  refine ⟨3879523894917771645920275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5172698526557028861227033 3879523894917771645920275)
                  ·
                    refine ⟨5819285842376657468880413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879523894917771645920275 5819285842376657468880413)
                    ·
                      refine ⟨2182232190891246550830155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819285842376657468880413 2182232190891246550830155)
                      ·
                        rfl

theorem cell23_4249882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_4249882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249882 prefixEnd_4249882 := by exact prefixLift 4249882
  have htrace : WordTrace (prefixWord ++ tailWord_4249882) baseStart_4249882 baseEnd_4249882 := by
    simpa [prefixWord, tailWord_4249882, baseEnd_4249882] using wordTrace_append hprefix tailTrace_4249882
  have hstable : (prefixWord ++ tailWord_4249882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249882).length < 2 ^ (prefixWord ++ tailWord_4249882).sum := by decide
  have hdescent : baseEnd_4249882 < baseStart_4249882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249884 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4249884 : Nat := 118140960795 + 4249884 * 2 ^ 59
def prefixEnd_4249884 : Nat := 4983230072969 + 3 ^ 40 * 4249884 * 2
def baseEnd_4249884 : Nat := 2182233217852555543005145

theorem tailTrace_4249884 : CollatzResearch.WordTrace tailWord_4249884 prefixEnd_4249884 2182233217852555543005145 := by
  unfold tailWord_4249884
  simp only [CollatzResearch.WordTrace]
  refine ⟨77503001867701782623318353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103337335823602376831091137 77503001867701782623318353)
  ·
    refine ⟨58127251400776336967488765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77503001867701782623318353 58127251400776336967488765)
    ·
      refine ⟨21797719275291126362808287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58127251400776336967488765 21797719275291126362808287)
      ·
        refine ⟨32696578912936689544212431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21797719275291126362808287 32696578912936689544212431)
        ·
          refine ⟨49044868369405034316318647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32696578912936689544212431 49044868369405034316318647)
          ·
            refine ⟨73567302554107551474477971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49044868369405034316318647 73567302554107551474477971)
            ·
              refine ⟨110350953831161327211716957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73567302554107551474477971 110350953831161327211716957)
              ·
                refine ⟨41381607686685497704393859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110350953831161327211716957 41381607686685497704393859)
                ·
                  refine ⟨62072411530028246556590789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41381607686685497704393859 62072411530028246556590789)
                  ·
                    refine ⟨11638577161880296229360773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62072411530028246556590789 11638577161880296229360773)
                    ·
                      refine ⟨2182233217852555543005145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11638577161880296229360773 2182233217852555543005145)
                      ·
                        rfl

theorem cell23_4249884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4249884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249884 prefixEnd_4249884 := by exact prefixLift 4249884
  have htrace : WordTrace (prefixWord ++ tailWord_4249884) baseStart_4249884 baseEnd_4249884 := by
    simpa [prefixWord, tailWord_4249884, baseEnd_4249884] using wordTrace_append hprefix tailTrace_4249884
  have hstable : (prefixWord ++ tailWord_4249884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249884).length < 2 ^ (prefixWord ++ tailWord_4249884).sum := by decide
  have hdescent : baseEnd_4249884 < baseStart_4249884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249904 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_4249904 : Nat := 118140960795 + 4249904 * 2 ^ 59
def prefixEnd_4249904 : Nat := 4983230072969 + 3 ^ 40 * 4249904 * 2
def baseEnd_4249904 : Nat := 2182243487465645464755053

theorem tailTrace_4249904 : CollatzResearch.WordTrace tailWord_4249904 prefixEnd_4249904 2182243487465645464755053 := by
  unfold tailWord_4249904
  simp only [CollatzResearch.WordTrace]
  refine ⟨77503366597665554331182383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103337822130220739108243177 77503366597665554331182383)
  ·
    refine ⟨116255049896498331496773575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77503366597665554331182383 116255049896498331496773575)
    ·
      refine ⟨174382574844747497245160363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116255049896498331496773575 174382574844747497245160363)
      ·
        refine ⟨261573862267121245867740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174382574844747497245160363 261573862267121245867740545)
        ·
          refine ⟨196180396700340934400805409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261573862267121245867740545 196180396700340934400805409)
          ·
            refine ⟨147135297525255700800604057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196180396700340934400805409 147135297525255700800604057)
            ·
              refine ⟨110351473143941775600453043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147135297525255700800604057 110351473143941775600453043)
              ·
                refine ⟨165527209715912663400679565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110351473143941775600453043 165527209715912663400679565)
                ·
                  refine ⟨62072703643467248775254837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165527209715912663400679565 62072703643467248775254837)
                  ·
                    refine ⟨5819315966575054572680141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62072703643467248775254837 5819315966575054572680141)
                    ·
                      refine ⟨2182243487465645464755053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819315966575054572680141 2182243487465645464755053)
                      ·
                        rfl

theorem cell23_4249904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_4249904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249904 prefixEnd_4249904 := by exact prefixLift 4249904
  have htrace : WordTrace (prefixWord ++ tailWord_4249904) baseStart_4249904 baseEnd_4249904 := by
    simpa [prefixWord, tailWord_4249904, baseEnd_4249904] using wordTrace_append hprefix tailTrace_4249904
  have hstable : (prefixWord ++ tailWord_4249904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249904).length < 2 ^ (prefixWord ++ tailWord_4249904).sum := by decide
  have hdescent : baseEnd_4249904 < baseStart_4249904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249928 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 5]
def baseStart_4249928 : Nat := 118140960795 + 4249928 * 2 ^ 59
def prefixEnd_4249928 : Nat := 4983230072969 + 3 ^ 40 * 4249928 * 2
def baseEnd_4249928 : Nat := 242472867889039263428327

theorem tailTrace_4249928 : CollatzResearch.WordTrace tailWord_4249928 prefixEnd_4249928 242472867889039263428327 := by
  unfold tailWord_4249928
  simp only [CollatzResearch.WordTrace]
  refine ⟨77503804273622080380619219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103338405698162773840825625 77503804273622080380619219)
  ·
    refine ⟨116255706410433120570928829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77503804273622080380619219 116255706410433120570928829)
    ·
      refine ⟨43595889903912420214098311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116255706410433120570928829 43595889903912420214098311)
      ·
        refine ⟨65393834855868630321147467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43595889903912420214098311 65393834855868630321147467)
        ·
          refine ⟨98090752283802945481721201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65393834855868630321147467 98090752283802945481721201)
          ·
            refine ⟨73568064212852209111290901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98090752283802945481721201 73568064212852209111290901)
            ·
              refine ⟨3448503009977447302091761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73568064212852209111290901 3448503009977447302091761)
              ·
                refine ⟨2586377257483085476568821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448503009977447302091761 2586377257483085476568821)
                ·
                  refine ⟨242472867889039263428327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586377257483085476568821 242472867889039263428327)
                  ·
                    rfl

theorem cell23_4249928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 5].length) (baseStart_4249928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249928 prefixEnd_4249928 := by exact prefixLift 4249928
  have htrace : WordTrace (prefixWord ++ tailWord_4249928) baseStart_4249928 baseEnd_4249928 := by
    simpa [prefixWord, tailWord_4249928, baseEnd_4249928] using wordTrace_append hprefix tailTrace_4249928
  have hstable : (prefixWord ++ tailWord_4249928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249928).length < 2 ^ (prefixWord ++ tailWord_4249928).sum := by decide
  have hdescent : baseEnd_4249928 < baseStart_4249928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249934 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4249934 : Nat := 118140960795 + 4249934 * 2 ^ 59
def prefixEnd_4249934 : Nat := 4983230072969 + 3 ^ 40 * 4249934 * 2
def baseEnd_4249934 : Nat := 2182258891885280347379915

theorem tailTrace_4249934 : CollatzResearch.WordTrace tailWord_4249934 prefixEnd_4249934 2182258891885280347379915 := by
  unfold tailWord_4249934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19375978423152802973244607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103338551590148282523971237 19375978423152802973244607)
  ·
    refine ⟨29063967634729204459866911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19375978423152802973244607 29063967634729204459866911)
    ·
      refine ⟨43595951452093806689800367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29063967634729204459866911 43595951452093806689800367)
      ·
        refine ⟨65393927178140710034700551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43595951452093806689800367 65393927178140710034700551)
        ·
          refine ⟨98090890767211065052050827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65393927178140710034700551 98090890767211065052050827)
          ·
            refine ⟨147136336150816597578076241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98090890767211065052050827 147136336150816597578076241)
            ·
              refine ⟨110352252113112448183557181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147136336150816597578076241 110352252113112448183557181)
              ·
                refine ⟨41382094542417168068833943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110352252113112448183557181 41382094542417168068833943)
                ·
                  refine ⟨62073141813625752103250915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41382094542417168068833943 62073141813625752103250915)
                  ·
                    refine ⟨93109712720438628154876373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62073141813625752103250915 93109712720438628154876373)
                    ·
                      refine ⟨2182258891885280347379915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93109712720438628154876373 2182258891885280347379915)
                      ·
                        rfl

theorem cell23_4249934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4249934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249934 prefixEnd_4249934 := by exact prefixLift 4249934
  have htrace : WordTrace (prefixWord ++ tailWord_4249934) baseStart_4249934 baseEnd_4249934 := by
    simpa [prefixWord, tailWord_4249934, baseEnd_4249934] using wordTrace_append hprefix tailTrace_4249934
  have hstable : (prefixWord ++ tailWord_4249934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249934).length < 2 ^ (prefixWord ++ tailWord_4249934).sum := by decide
  have hdescent : baseEnd_4249934 < baseStart_4249934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249961 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 6, 2]
def baseStart_4249961 : Nat := 118140960795 + 4249961 * 2 ^ 59
def prefixEnd_4249961 : Nat := 4983230072969 + 3 ^ 40 * 4249961 * 2
def baseEnd_4249961 : Nat := 2182272755862951741742291

theorem tailTrace_4249961 : CollatzResearch.WordTrace tailWord_4249961 prefixEnd_4249961 2182272755862951741742291 := by
  unfold tailWord_4249961
  simp only [CollatzResearch.WordTrace]
  refine ⟨155008812156124607397189737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103339208104083071598126491 155008812156124607397189737)
  ·
    refine ⟨116256609117093455547892303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155008812156124607397189737 116256609117093455547892303)
    ·
      refine ⟨174384913675640183321838455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116256609117093455547892303 174384913675640183321838455)
      ·
        refine ⟨261577370513460274982757683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174384913675640183321838455 261577370513460274982757683)
        ·
          refine ⟨392366055770190412474136525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261577370513460274982757683 392366055770190412474136525)
          ·
            refine ⟨147137270913821404677801197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392366055770190412474136525 147137270913821404677801197)
            ·
              refine ⟨55176476592683026754175449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147137270913821404677801197 55176476592683026754175449)
              ·
                refine ⟨41382357444512270065631587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55176476592683026754175449 41382357444512270065631587)
                ·
                  refine ⟨62073536166768405098447381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41382357444512270065631587 62073536166768405098447381)
                  ·
                    refine ⟨2909697007817268988989721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62073536166768405098447381 2909697007817268988989721)
                    ·
                      refine ⟨2182272755862951741742291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909697007817268988989721 2182272755862951741742291)
                      ·
                        rfl

theorem cell23_4249961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6, 2].length) (baseStart_4249961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249961 prefixEnd_4249961 := by exact prefixLift 4249961
  have htrace : WordTrace (prefixWord ++ tailWord_4249961) baseStart_4249961 baseEnd_4249961 := by
    simpa [prefixWord, tailWord_4249961, baseEnd_4249961] using wordTrace_append hprefix tailTrace_4249961
  have hstable : (prefixWord ++ tailWord_4249961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249961).length < 2 ^ (prefixWord ++ tailWord_4249961).sum := by decide
  have hdescent : baseEnd_4249961 < baseStart_4249961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249988 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_4249988 : Nat := 118140960795 + 4249988 * 2 ^ 59
def prefixEnd_4249988 : Nat := 4983230072969 + 3 ^ 40 * 4249988 * 2
def baseEnd_4249988 : Nat := 727428873280207712034889

theorem tailTrace_4249988 : CollatzResearch.WordTrace tailWord_4249988 prefixEnd_4249988 727428873280207712034889 := by
  unfold tailWord_4249988
  simp only [CollatzResearch.WordTrace]
  refine ⟨77504898463513395504211309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103339864618017860672281745 77504898463513395504211309)
  ·
    refine ⟨29064336923817523314079241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77504898463513395504211309 29064336923817523314079241)
    ·
      refine ⟨21798252692863142485559431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29064336923817523314079241 21798252692863142485559431)
      ·
        refine ⟨32697379039294713728339147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21798252692863142485559431 32697379039294713728339147)
        ·
          refine ⟨49046068558942070592508721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32697379039294713728339147 49046068558942070592508721)
          ·
            refine ⟨36784551419206552944381541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49046068558942070592508721 36784551419206552944381541)
            ·
              refine ⟨6897103391101228677071539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36784551419206552944381541 6897103391101228677071539)
              ·
                refine ⟨10345655086651843015607309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897103391101228677071539 10345655086651843015607309)
                ·
                  refine ⟨3879620657494441130852741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10345655086651843015607309 3879620657494441130852741)
                  ·
                    refine ⟨727428873280207712034889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879620657494441130852741 727428873280207712034889)
                    ·
                      rfl

theorem cell23_4249988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_4249988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249988 prefixEnd_4249988 := by exact prefixLift 4249988
  have htrace : WordTrace (prefixWord ++ tailWord_4249988) baseStart_4249988 baseEnd_4249988 := by
    simpa [prefixWord, tailWord_4249988, baseEnd_4249988] using wordTrace_append hprefix tailTrace_4249988
  have hstable : (prefixWord ++ tailWord_4249988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249988).length < 2 ^ (prefixWord ++ tailWord_4249988).sum := by decide
  have hdescent : baseEnd_4249988 < baseStart_4249988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4249998 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4249998 : Nat := 118140960795 + 4249998 * 2 ^ 59
def prefixEnd_4249998 : Nat := 4983230072969 + 3 ^ 40 * 4249998 * 2
def baseEnd_4249998 : Nat := 2182291754647168096979621

theorem tailTrace_4249998 : CollatzResearch.WordTrace tailWord_4249998 prefixEnd_4249998 2182291754647168096979621 := by
  unfold tailWord_4249998
  simp only [CollatzResearch.WordTrace]
  refine ⟨19376270207123820339535831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103340107771327041810857765 19376270207123820339535831)
  ·
    refine ⟨29064405310685730509303747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19376270207123820339535831 29064405310685730509303747)
    ·
      refine ⟨43596607966028595763955621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29064405310685730509303747 43596607966028595763955621)
      ·
        refine ⟨8174363993630361705741679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43596607966028595763955621 8174363993630361705741679)
        ·
          refine ⟨12261545990445542558612519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174363993630361705741679 12261545990445542558612519)
          ·
            refine ⟨18392318985668313837918779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12261545990445542558612519 18392318985668313837918779)
            ·
              refine ⟨27588478478502470756878169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18392318985668313837918779 27588478478502470756878169)
              ·
                refine ⟨20691358858876853067658627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27588478478502470756878169 20691358858876853067658627)
                ·
                  refine ⟨31037038288315279601487941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20691358858876853067658627 31037038288315279601487941)
                  ·
                    refine ⟨5819444679059114925278989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31037038288315279601487941 5819444679059114925278989)
                    ·
                      refine ⟨2182291754647168096979621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819444679059114925278989 2182291754647168096979621)
                      ·
                        rfl

theorem cell23_4249998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4249998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4249998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4249998 prefixEnd_4249998 := by exact prefixLift 4249998
  have htrace : WordTrace (prefixWord ++ tailWord_4249998) baseStart_4249998 baseEnd_4249998 := by
    simpa [prefixWord, tailWord_4249998, baseEnd_4249998] using wordTrace_append hprefix tailTrace_4249998
  have hstable : (prefixWord ++ tailWord_4249998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4249998).length < 2 ^ (prefixWord ++ tailWord_4249998).sum := by decide
  have hdescent : baseEnd_4249998 < baseStart_4249998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4249998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250045 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_4250045 : Nat := 118140960795 + 4250045 * 2 ^ 59
def prefixEnd_4250045 : Nat := 4983230072969 + 3 ^ 40 * 4250045 * 2
def baseEnd_4250045 : Nat := 2182315888237929413091905

theorem tailTrace_4250045 : CollatzResearch.WordTrace tailWord_4250045 prefixEnd_4250045 2182315888237929413091905 := by
  unfold tailWord_4250045
  simp only [CollatzResearch.WordTrace]
  refine ⟨155011875887820289743247589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103341250591880193162165059 155011875887820289743247589)
  ·
    refine ⟨29064726728966304326858923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155011875887820289743247589 29064726728966304326858923)
    ·
      refine ⟨43597090093449456490288385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29064726728966304326858923 43597090093449456490288385)
      ·
        refine ⟨32697817570087092367716289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43597090093449456490288385 32697817570087092367716289)
        ·
          refine ⟨24523363177565319275787217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32697817570087092367716289 24523363177565319275787217)
          ·
            refine ⟨18392522383173989456840413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24523363177565319275787217 18392522383173989456840413)
            ·
              refine ⟨6897195893690246046315155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18392522383173989456840413 6897195893690246046315155)
              ·
                refine ⟨10345793840535369069472733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897195893690246046315155 10345793840535369069472733)
                ·
                  refine ⟨3879672690200763401052275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10345793840535369069472733 3879672690200763401052275)
                  ·
                    refine ⟨5819509035301145101578413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879672690200763401052275 5819509035301145101578413)
                    ·
                      refine ⟨2182315888237929413091905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819509035301145101578413 2182315888237929413091905)
                      ·
                        rfl

theorem cell23_4250045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_4250045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250045 prefixEnd_4250045 := by exact prefixLift 4250045
  have htrace : WordTrace (prefixWord ++ tailWord_4250045) baseStart_4250045 baseEnd_4250045 := by
    simpa [prefixWord, tailWord_4250045, baseEnd_4250045] using wordTrace_append hprefix tailTrace_4250045
  have hstable : (prefixWord ++ tailWord_4250045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250045).length < 2 ^ (prefixWord ++ tailWord_4250045).sum := by decide
  have hdescent : baseEnd_4250045 < baseStart_4250045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250051 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4]
def baseStart_4250051 : Nat := 118140960795 + 4250051 * 2 ^ 59
def prefixEnd_4250051 : Nat := 4983230072969 + 3 ^ 40 * 4250051 * 2
def baseEnd_4250051 : Nat := 2182318969121856389616877

theorem tailTrace_4250051 : CollatzResearch.WordTrace tailWord_4250051 prefixEnd_4250051 2182318969121856389616877 := by
  unfold tailWord_4250051
  simp only [CollatzResearch.WordTrace]
  refine ⟨155012094725798552767966007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103341396483865701845310671 155012094725798552767966007)
  ·
    refine ⟨232518142088697829151949011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155012094725798552767966007 232518142088697829151949011)
    ·
      refine ⟨348777213133046743727923517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232518142088697829151949011 348777213133046743727923517)
      ·
        refine ⟨130791454924892528897971319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348777213133046743727923517 130791454924892528897971319)
        ·
          refine ⟨196187182387338793346956979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130791454924892528897971319 196187182387338793346956979)
          ·
            refine ⟨294280773581008190020435469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196187182387338793346956979 294280773581008190020435469)
            ·
              refine ⟨110355290092878071257663301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294280773581008190020435469 110355290092878071257663301)
              ·
                refine ⟨20691616892414638360811869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110355290092878071257663301 20691616892414638360811869)
                ·
                  refine ⟨7759356334655489385304451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20691616892414638360811869 7759356334655489385304451)
                  ·
                    refine ⟨11639034501983234077956677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7759356334655489385304451 11639034501983234077956677)
                    ·
                      refine ⟨2182318969121856389616877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11639034501983234077956677 2182318969121856389616877)
                      ·
                        rfl

theorem cell23_4250051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_4250051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250051 prefixEnd_4250051 := by exact prefixLift 4250051
  have htrace : WordTrace (prefixWord ++ tailWord_4250051) baseStart_4250051 baseEnd_4250051 := by
    simpa [prefixWord, tailWord_4250051, baseEnd_4250051] using wordTrace_append hprefix tailTrace_4250051
  have hstable : (prefixWord ++ tailWord_4250051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250051).length < 2 ^ (prefixWord ++ tailWord_4250051).sum := by decide
  have hdescent : baseEnd_4250051 < baseStart_4250051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250052 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 6]
def baseStart_4250052 : Nat := 118140960795 + 4250052 * 2 ^ 59
def prefixEnd_4250052 : Nat := 4983230072969 + 3 ^ 40 * 4250052 * 2
def baseEnd_4250052 : Nat := 242479942511390098411597

theorem tailTrace_4250052 : CollatzResearch.WordTrace tailWord_4250052 prefixEnd_4250052 242479942511390098411597 := by
  unfold tailWord_4250052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77506065599397464969376205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103341420799196619959168273 77506065599397464969376205)
  ·
    refine ⟨29064774599774049363516077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77506065599397464969376205 29064774599774049363516077)
    ·
      refine ⟨10899290474915268511318529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29064774599774049363516077 10899290474915268511318529)
      ·
        refine ⟨8174467856186451383488897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10899290474915268511318529 8174467856186451383488897)
        ·
          refine ⟨6130850892139838537616673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8174467856186451383488897 6130850892139838537616673)
          ·
            refine ⟨4598138169104878903212505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6130850892139838537616673 4598138169104878903212505)
            ·
              refine ⟨3448603626828659177409379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598138169104878903212505 3448603626828659177409379)
              ·
                refine ⟨5172905440242988766114069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448603626828659177409379 5172905440242988766114069)
                ·
                  refine ⟨242479942511390098411597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5172905440242988766114069 242479942511390098411597)
                  ·
                    rfl

theorem cell23_4250052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_4250052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250052 prefixEnd_4250052 := by exact prefixLift 4250052
  have htrace : WordTrace (prefixWord ++ tailWord_4250052) baseStart_4250052 baseEnd_4250052 := by
    simpa [prefixWord, tailWord_4250052, baseEnd_4250052] using wordTrace_append hprefix tailTrace_4250052
  have hstable : (prefixWord ++ tailWord_4250052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250052).length < 2 ^ (prefixWord ++ tailWord_4250052).sum := by decide
  have hdescent : baseEnd_4250052 < baseStart_4250052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250088 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4250088 : Nat := 118140960795 + 4250088 * 2 ^ 59
def prefixEnd_4250088 : Nat := 4983230072969 + 3 ^ 40 * 4250088 * 2
def baseEnd_4250088 : Nat := 2182337967906072744854207

theorem tailTrace_4250088 : CollatzResearch.WordTrace tailWord_4250088 prefixEnd_4250088 2182337967906072744854207 := by
  unfold tailWord_4250088
  simp only [CollatzResearch.WordTrace]
  refine ⟨77506722113332254043531459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103342296151109672058041945 77506722113332254043531459)
  ·
    refine ⟨116260083169998381065297189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77506722113332254043531459 116260083169998381065297189)
    ·
      refine ⟨21798765594374696449743223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116260083169998381065297189 21798765594374696449743223)
      ·
        refine ⟨32698148391562044674614835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21798765594374696449743223 32698148391562044674614835)
        ·
          refine ⟨49047222587343067011922253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32698148391562044674614835 49047222587343067011922253)
          ·
            refine ⟨18392708470253650129470845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49047222587343067011922253 18392708470253650129470845)
            ·
              refine ⟨6897265676345118798551567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18392708470253650129470845 6897265676345118798551567)
              ·
                refine ⟨10345898514517678197827351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897265676345118798551567 10345898514517678197827351)
                ·
                  refine ⟨15518847771776517296741027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10345898514517678197827351 15518847771776517296741027)
                  ·
                    refine ⟨23278271657664775945111541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15518847771776517296741027 23278271657664775945111541)
                    ·
                      refine ⟨2182337967906072744854207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23278271657664775945111541 2182337967906072744854207)
                      ·
                        rfl

theorem cell23_4250088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4250088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250088 prefixEnd_4250088 := by exact prefixLift 4250088
  have htrace : WordTrace (prefixWord ++ tailWord_4250088) baseStart_4250088 baseEnd_4250088 := by
    simpa [prefixWord, tailWord_4250088, baseEnd_4250088] using wordTrace_append hprefix tailTrace_4250088
  have hstable : (prefixWord ++ tailWord_4250088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250088).length < 2 ^ (prefixWord ++ tailWord_4250088).sum := by decide
  have hdescent : baseEnd_4250088 < baseStart_4250088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250102 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4250102 : Nat := 118140960795 + 4250102 * 2 ^ 59
def prefixEnd_4250102 : Nat := 4983230072969 + 3 ^ 40 * 4250102 * 2
def baseEnd_4250102 : Nat := 2182345156635235690079143

theorem tailTrace_4250102 : CollatzResearch.WordTrace tailWord_4250102 prefixEnd_4250102 2182345156635235690079143 := by
  unfold tailWord_4250102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688372178038361779879535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103342636565742525652048373 9688372178038361779879535)
  ·
    refine ⟨14532558267057542669819303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9688372178038361779879535 14532558267057542669819303)
    ·
      refine ⟨21798837400586314004728955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14532558267057542669819303 21798837400586314004728955)
      ·
        refine ⟨32698256100879471007093433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21798837400586314004728955 32698256100879471007093433)
        ·
          refine ⟨24523692075659603255320075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32698256100879471007093433 24523692075659603255320075)
          ·
            refine ⟨36785538113489404882980113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24523692075659603255320075 36785538113489404882980113)
            ·
              refine ⟨27589153585117053662235085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36785538113489404882980113 27589153585117053662235085)
              ·
                refine ⟨10345932594418895123338157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27589153585117053662235085 10345932594418895123338157)
                ·
                  refine ⟨3879724722907085671251809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10345932594418895123338157 3879724722907085671251809)
                  ·
                    refine ⟨2909793542180314253438857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879724722907085671251809 2909793542180314253438857)
                    ·
                      refine ⟨2182345156635235690079143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909793542180314253438857 2182345156635235690079143)
                      ·
                        rfl

theorem cell23_4250102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4250102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250102 prefixEnd_4250102 := by exact prefixLift 4250102
  have htrace : WordTrace (prefixWord ++ tailWord_4250102) baseStart_4250102 baseEnd_4250102 := by
    simpa [prefixWord, tailWord_4250102, baseEnd_4250102] using wordTrace_append hprefix tailTrace_4250102
  have hstable : (prefixWord ++ tailWord_4250102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250102).length < 2 ^ (prefixWord ++ tailWord_4250102).sum := by decide
  have hdescent : baseEnd_4250102 < baseStart_4250102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250131 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_4250131 : Nat := 118140960795 + 4250131 * 2 ^ 59
def prefixEnd_4250131 : Nat := 4983230072969 + 3 ^ 40 * 4250131 * 2
def baseEnd_4250131 : Nat := 2182360047574216076616509

theorem tailTrace_4250131 : CollatzResearch.WordTrace tailWord_4250131 prefixEnd_4250131 2182360047574216076616509 := by
  unfold tailWord_4250131
  simp only [CollatzResearch.WordTrace]
  refine ⟨155015012565508726430878247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103343341710339150953918831 155015012565508726430878247)
  ·
    refine ⟨232522518848263089646317371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155015012565508726430878247 232522518848263089646317371)
    ·
      refine ⟨348783778272394634469476057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232522518848263089646317371 348783778272394634469476057)
      ·
        refine ⟨261587833704295975852107043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348783778272394634469476057 261587833704295975852107043)
        ·
          refine ⟨392381750556443963778160565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261587833704295975852107043 392381750556443963778160565)
          ·
            refine ⟨36785789114666621604202553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 392381750556443963778160565 36785789114666621604202553)
            ·
              refine ⟨27589341835999966203151915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36785789114666621604202553 27589341835999966203151915)
              ·
                refine ⟨41384012753999949304727873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27589341835999966203151915 41384012753999949304727873)
                ·
                  refine ⟨31038009565499961978545905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41384012753999949304727873 31038009565499961978545905)
                  ·
                    refine ⟨23278507174124971483909429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31038009565499961978545905 23278507174124971483909429)
                    ·
                      refine ⟨2182360047574216076616509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23278507174124971483909429 2182360047574216076616509)
                      ·
                        rfl

theorem cell23_4250131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_4250131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250131 prefixEnd_4250131 := by exact prefixLift 4250131
  have htrace : WordTrace (prefixWord ++ tailWord_4250131) baseStart_4250131 baseEnd_4250131 := by
    simpa [prefixWord, tailWord_4250131, baseEnd_4250131] using wordTrace_append hprefix tailTrace_4250131
  have hstable : (prefixWord ++ tailWord_4250131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250131).length < 2 ^ (prefixWord ++ tailWord_4250131).sum := by decide
  have hdescent : baseEnd_4250131 < baseStart_4250131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250152 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4250152 : Nat := 118140960795 + 4250152 * 2 ^ 59
def prefixEnd_4250152 : Nat := 4983230072969 + 3 ^ 40 * 4250152 * 2
def baseEnd_4250152 : Nat := 2182370830667960494453913

theorem tailTrace_4250152 : CollatzResearch.WordTrace tailWord_4250152 prefixEnd_4250152 2182370830667960494453913 := by
  unfold tailWord_4250152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77507889249216323508696355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103343852332288431344928473 77507889249216323508696355)
  ·
    refine ⟨116261833873824485263044533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77507889249216323508696355 116261833873824485263044533)
    ·
      refine ⟨10899546925671045493410425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116261833873824485263044533 10899546925671045493410425)
      ·
        refine ⟨8174660194253284120057819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10899546925671045493410425 8174660194253284120057819)
        ·
          refine ⟨12261990291379926180086729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174660194253284120057819 12261990291379926180086729)
          ·
            refine ⟨9196492718534944635065047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12261990291379926180086729 9196492718534944635065047)
            ·
              refine ⟨13794739077802416952597571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9196492718534944635065047 13794739077802416952597571)
              ·
                refine ⟨20692108616703625428896357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13794739077802416952597571 20692108616703625428896357)
                ·
                  refine ⟨3879770365631929767918067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20692108616703625428896357 3879770365631929767918067)
                  ·
                    refine ⟨5819655548447894651877101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879770365631929767918067 5819655548447894651877101)
                    ·
                      refine ⟨2182370830667960494453913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819655548447894651877101 2182370830667960494453913)
                      ·
                        rfl

theorem cell23_4250152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4250152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250152 prefixEnd_4250152 := by exact prefixLift 4250152
  have htrace : WordTrace (prefixWord ++ tailWord_4250152) baseStart_4250152 baseEnd_4250152 := by
    simpa [prefixWord, tailWord_4250152, baseEnd_4250152] using wordTrace_append hprefix tailTrace_4250152
  have hstable : (prefixWord ++ tailWord_4250152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250152).length < 2 ^ (prefixWord ++ tailWord_4250152).sum := by decide
  have hdescent : baseEnd_4250152 < baseStart_4250152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250171 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_4250171 : Nat := 118140960795 + 4250171 * 2 ^ 59
def prefixEnd_4250171 : Nat := 4983230072969 + 3 ^ 40 * 4250171 * 2
def baseEnd_4250171 : Nat := 2182380586800395920116325

theorem tailTrace_4250171 : CollatzResearch.WordTrace tailWord_4250171 prefixEnd_4250171 2182380586800395920116325 := by
  unfold tailWord_4250171
  simp only [CollatzResearch.WordTrace]
  refine ⟨155016471485363813262334367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103344314323575875508222911 155016471485363813262334367)
  ·
    refine ⟨232524707228045719893501551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155016471485363813262334367 232524707228045719893501551)
    ·
      refine ⟨348787060842068579840252327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232524707228045719893501551 348787060842068579840252327)
      ·
        refine ⟨523180591263102869760378491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348787060842068579840252327 523180591263102869760378491)
        ·
          refine ⟨784770886894654304640567737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523180591263102869760378491 784770886894654304640567737)
          ·
            refine ⟨588578165170990728480425803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784770886894654304640567737 588578165170990728480425803)
            ·
              refine ⟨882867247756486092720638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588578165170990728480425803 882867247756486092720638705)
              ·
                refine ⟨662150435817364569540479029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882867247756486092720638705 662150435817364569540479029)
                ·
                  refine ⟨62076603357877928394419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662150435817364569540479029 62076603357877928394419909)
                  ·
                    refine ⟨11639363129602111573953733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62076603357877928394419909 11639363129602111573953733)
                    ·
                      refine ⟨2182380586800395920116325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11639363129602111573953733 2182380586800395920116325)
                      ·
                        rfl

theorem cell23_4250171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_4250171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250171 prefixEnd_4250171 := by exact prefixLift 4250171
  have htrace : WordTrace (prefixWord ++ tailWord_4250171) baseStart_4250171 baseEnd_4250171 := by
    simpa [prefixWord, tailWord_4250171, baseEnd_4250171] using wordTrace_append hprefix tailTrace_4250171
  have hstable : (prefixWord ++ tailWord_4250171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250171).length < 2 ^ (prefixWord ++ tailWord_4250171).sum := by decide
  have hdescent : baseEnd_4250171 < baseStart_4250171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_4250201 : Nat := 118140960795 + 4250201 * 2 ^ 59
def prefixEnd_4250201 : Nat := 4983230072969 + 3 ^ 40 * 4250201 * 2
def baseEnd_4250201 : Nat := 2182395991220030802741187

theorem tailTrace_4250201 : CollatzResearch.WordTrace tailWord_4250201 prefixEnd_4250201 2182395991220030802741187 := by
  unfold tailWord_4250201
  simp only [CollatzResearch.WordTrace]
  refine ⟨155017565675255128385926457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103345043783503418923950971 155017565675255128385926457)
  ·
    refine ⟨116263174256441346289444843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155017565675255128385926457 116263174256441346289444843)
    ·
      refine ⟨174394761384662019434167265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116263174256441346289444843 174394761384662019434167265)
      ·
        refine ⟨130796071038496514575625449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174394761384662019434167265 130796071038496514575625449)
        ·
          refine ⟨98097053278872385931719087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130796071038496514575625449 98097053278872385931719087)
          ·
            refine ⟨147145579918308578897578631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98097053278872385931719087 147145579918308578897578631)
            ·
              refine ⟨220718369877462868346367947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147145579918308578897578631 220718369877462868346367947)
              ·
                refine ⟨331077554816194302519551921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220718369877462868346367947 331077554816194302519551921)
                ·
                  refine ⟨248308166112145726889663941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331077554816194302519551921 248308166112145726889663941)
                  ·
                    refine ⟨46557781146027323791811989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248308166112145726889663941 46557781146027323791811989)
                    ·
                      refine ⟨2182395991220030802741187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46557781146027323791811989 2182395991220030802741187)
                      ·
                        rfl

theorem cell23_4250201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_4250201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250201 prefixEnd_4250201 := by exact prefixLift 4250201
  have htrace : WordTrace (prefixWord ++ tailWord_4250201) baseStart_4250201 baseEnd_4250201 := by
    simpa [prefixWord, tailWord_4250201, baseEnd_4250201] using wordTrace_append hprefix tailTrace_4250201
  have hstable : (prefixWord ++ tailWord_4250201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250201).length < 2 ^ (prefixWord ++ tailWord_4250201).sum := by decide
  have hdescent : baseEnd_4250201 < baseStart_4250201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250208 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_4250208 : Nat := 118140960795 + 4250208 * 2 ^ 59
def prefixEnd_4250208 : Nat := 4983230072969 + 3 ^ 40 * 4250208 * 2
def baseEnd_4250208 : Nat := 2182399585584612275353655

theorem tailTrace_4250208 : CollatzResearch.WordTrace tailWord_4250208 prefixEnd_4250208 2182399585584612275353655 := by
  unfold tailWord_4250208
  simp only [CollatzResearch.WordTrace]
  refine ⟨77508910493114884290715639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103345213990819845720954185 77508910493114884290715639)
  ·
    refine ⟨116263365739672326436073459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77508910493114884290715639 116263365739672326436073459)
    ·
      refine ⟨174395048609508489654110189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116263365739672326436073459 174395048609508489654110189)
      ·
        refine ⟨65398143228565683620291321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174395048609508489654110189 65398143228565683620291321)
        ·
          refine ⟨49048607421424262715218491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65398143228565683620291321 49048607421424262715218491)
          ·
            refine ⟨73572911132136394072827737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49048607421424262715218491 73572911132136394072827737)
            ·
              refine ⟨55179683349102295554620803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73572911132136394072827737 55179683349102295554620803)
              ·
                refine ⟨82769525023653443331931205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55179683349102295554620803 82769525023653443331931205)
                ·
                  refine ⟨15519285941935020624737101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82769525023653443331931205 15519285941935020624737101)
                  ·
                    refine ⟨5819732228225632734276413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15519285941935020624737101 5819732228225632734276413)
                    ·
                      refine ⟨2182399585584612275353655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5819732228225632734276413 2182399585584612275353655)
                      ·
                        rfl

theorem cell23_4250208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_4250208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250208 prefixEnd_4250208 := by exact prefixLift 4250208
  have htrace : WordTrace (prefixWord ++ tailWord_4250208) baseStart_4250208 baseEnd_4250208 := by
    simpa [prefixWord, tailWord_4250208, baseEnd_4250208] using wordTrace_append hprefix tailTrace_4250208
  have hstable : (prefixWord ++ tailWord_4250208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250208).length < 2 ^ (prefixWord ++ tailWord_4250208).sum := by decide
  have hdescent : baseEnd_4250208 < baseStart_4250208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250245 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_4250245 : Nat := 118140960795 + 4250245 * 2 ^ 59
def prefixEnd_4250245 : Nat := 4983230072969 + 3 ^ 40 * 4250245 * 2
def baseEnd_4250245 : Nat := 727472861456276210196995

theorem tailTrace_4250245 : CollatzResearch.WordTrace tailWord_4250245 prefixEnd_4250245 727472861456276210196995 := by
  unfold tailWord_4250245
  simp only [CollatzResearch.WordTrace]
  refine ⟨155019170487095723900528189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103346113658063815933685459 155019170487095723900528189)
  ·
    refine ⟨58132188932660896462698071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155019170487095723900528189 58132188932660896462698071)
    ·
      refine ⟨87198283398991344694047107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58132188932660896462698071 87198283398991344694047107)
      ·
        refine ⟨130797425098487017041070661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87198283398991344694047107 130797425098487017041070661)
        ·
          refine ⟨24524517205966315695200749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130797425098487017041070661 24524517205966315695200749)
          ·
            refine ⟨9196693952237368385700281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24524517205966315695200749 9196693952237368385700281)
            ·
              refine ⟨6897520464178026289275211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9196693952237368385700281 6897520464178026289275211)
              ·
                refine ⟨10346280696267039433912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897520464178026289275211 10346280696267039433912817)
                ·
                  refine ⟨7759710522200279575434613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10346280696267039433912817 7759710522200279575434613)
                  ·
                    refine ⟨727472861456276210196995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7759710522200279575434613 727472861456276210196995)
                    ·
                      rfl

theorem cell23_4250245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_4250245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250245 prefixEnd_4250245 := by exact prefixLift 4250245
  have htrace : WordTrace (prefixWord ++ tailWord_4250245) baseStart_4250245 baseEnd_4250245 := by
    simpa [prefixWord, tailWord_4250245, baseEnd_4250245] using wordTrace_append hprefix tailTrace_4250245
  have hstable : (prefixWord ++ tailWord_4250245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250245).length < 2 ^ (prefixWord ++ tailWord_4250245).sum := by decide
  have hdescent : baseEnd_4250245 < baseStart_4250245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250265 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 4, 2]
def baseStart_4250265 : Nat := 118140960795 + 4250265 * 2 ^ 59
def prefixEnd_4250265 : Nat := 4983230072969 + 3 ^ 40 * 4250265 * 2
def baseEnd_4250265 : Nat := 2182428853981918552340893

theorem tailTrace_4250265 : CollatzResearch.WordTrace tailWord_4250265 prefixEnd_4250265 2182428853981918552340893 := by
  unfold tailWord_4250265
  simp only [CollatzResearch.WordTrace]
  refine ⟨155019899947023267316256249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103346599964682178210837499 155019899947023267316256249)
  ·
    refine ⟨116264924960267450487192187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155019899947023267316256249 116264924960267450487192187)
    ·
      refine ⟨174397387440401175730788281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116264924960267450487192187 174397387440401175730788281)
      ·
        refine ⟨130798040580300881798091211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174397387440401175730788281 130798040580300881798091211)
        ·
          refine ⟨196197060870451322697136817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130798040580300881798091211 196197060870451322697136817)
          ·
            refine ⟨147147795652838492022852613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196197060870451322697136817 147147795652838492022852613)
            ·
              refine ⟨27590211684907217254284865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147147795652838492022852613 27590211684907217254284865)
              ·
                refine ⟨20692658763680412940713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27590211684907217254284865 20692658763680412940713649)
                ·
                  refine ⟨15519494072760309705535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20692658763680412940713649 15519494072760309705535237)
                  ·
                    refine ⟨2909905138642558069787857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15519494072760309705535237 2909905138642558069787857)
                    ·
                      refine ⟨2182428853981918552340893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909905138642558069787857 2182428853981918552340893)
                      ·
                        rfl

theorem cell23_4250265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_4250265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250265 prefixEnd_4250265 := by exact prefixLift 4250265
  have htrace : WordTrace (prefixWord ++ tailWord_4250265) baseStart_4250265 baseEnd_4250265 := by
    simpa [prefixWord, tailWord_4250265, baseEnd_4250265] using wordTrace_append hprefix tailTrace_4250265
  have hstable : (prefixWord ++ tailWord_4250265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250265).length < 2 ^ (prefixWord ++ tailWord_4250265).sum := by decide
  have hdescent : baseEnd_4250265 < baseStart_4250265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250266 : List Nat := [3, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_4250266 : Nat := 118140960795 + 4250266 * 2 ^ 59
def prefixEnd_4250266 : Nat := 4983230072969 + 3 ^ 40 * 4250266 * 2
def baseEnd_4250266 : Nat := 242492151940285894269821

theorem tailTrace_4250266 : CollatzResearch.WordTrace tailWord_4250266 prefixEnd_4250266 242492151940285894269821 := by
  unfold tailWord_4250266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38754984105004911121760663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103346624280013096324695101 38754984105004911121760663)
  ·
    refine ⟨58132476157507366682640995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38754984105004911121760663 58132476157507366682640995)
    ·
      refine ⟨87198714236261050023961493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58132476157507366682640995 87198714236261050023961493)
      ·
        refine ⟨4087439729824736719873195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87198714236261050023961493 4087439729824736719873195)
        ·
          refine ⟨6131159594737105079809793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087439729824736719873195 6131159594737105079809793)
          ·
            refine ⟨4598369696052828809857345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6131159594737105079809793 4598369696052828809857345)
            ·
              refine ⟨3448777272039621607393009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598369696052828809857345 3448777272039621607393009)
              ·
                refine ⟨2586582954029716205544757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448777272039621607393009 2586582954029716205544757)
                ·
                  refine ⟨242492151940285894269821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2586582954029716205544757 242492151940285894269821)
                  ·
                    rfl

theorem cell23_4250266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_4250266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250266 prefixEnd_4250266 := by exact prefixLift 4250266
  have htrace : WordTrace (prefixWord ++ tailWord_4250266) baseStart_4250266 baseEnd_4250266 := by
    simpa [prefixWord, tailWord_4250266, baseEnd_4250266] using wordTrace_append hprefix tailTrace_4250266
  have hstable : (prefixWord ++ tailWord_4250266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250266).length < 2 ^ (prefixWord ++ tailWord_4250266).sum := by decide
  have hdescent : baseEnd_4250266 < baseStart_4250266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250355 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 8, 2]
def baseStart_4250355 : Nat := 118140960795 + 4250355 * 2 ^ 59
def prefixEnd_4250355 : Nat := 4983230072969 + 3 ^ 40 * 4250355 * 2
def baseEnd_4250355 : Nat := 2182475067240823200215479

theorem tailTrace_4250355 : CollatzResearch.WordTrace tailWord_4250355 prefixEnd_4250355 2182475067240823200215479 := by
  unfold tailWord_4250355
  simp only [CollatzResearch.WordTrace]
  refine ⟨155023182516697212687032519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103348788344464808458021679 155023182516697212687032519)
  ·
    refine ⟨232534773775045819030548779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155023182516697212687032519 232534773775045819030548779)
    ·
      refine ⟨348802160662568728545823169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232534773775045819030548779 348802160662568728545823169)
      ·
        refine ⟨261601620496926546409367377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348802160662568728545823169 261601620496926546409367377)
        ·
          refine ⟨196201215372694909807025533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261601620496926546409367377 196201215372694909807025533)
          ·
            refine ⟨73575455764760591177634575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196201215372694909807025533 73575455764760591177634575)
            ·
              refine ⟨110363183647140886766451863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73575455764760591177634575 110363183647140886766451863)
              ·
                refine ⟨165544775470711330149677795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110363183647140886766451863 165544775470711330149677795)
                ·
                  refine ⟨248317163206066995224516693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165544775470711330149677795 248317163206066995224516693)
                  ·
                    refine ⟨2909966756321097600287305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 248317163206066995224516693 2909966756321097600287305)
                    ·
                      refine ⟨2182475067240823200215479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2909966756321097600287305 2182475067240823200215479)
                      ·
                        rfl

theorem cell23_4250355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 8, 2].length) (baseStart_4250355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250355 prefixEnd_4250355 := by exact prefixLift 4250355
  have htrace : WordTrace (prefixWord ++ tailWord_4250355) baseStart_4250355 baseEnd_4250355 := by
    simpa [prefixWord, tailWord_4250355, baseEnd_4250355] using wordTrace_append hprefix tailTrace_4250355
  have hstable : (prefixWord ++ tailWord_4250355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250355).length < 2 ^ (prefixWord ++ tailWord_4250355).sum := by decide
  have hdescent : baseEnd_4250355 < baseStart_4250355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250365 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_4250365 : Nat := 118140960795 + 4250365 * 2 ^ 59
def prefixEnd_4250365 : Nat := 4983230072969 + 3 ^ 40 * 4250365 * 2
def baseEnd_4250365 : Nat := 727493400682456053696811

theorem tailTrace_4250365 : CollatzResearch.WordTrace tailWord_4250365 prefixEnd_4250365 727493400682456053696811 := by
  unfold tailWord_4250365
  simp only [CollatzResearch.WordTrace]
  refine ⟨155023547246660984394896549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103349031497773989596597699 155023547246660984394896549)
  ·
    refine ⟨29066915108748934574043103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155023547246660984394896549 29066915108748934574043103)
    ·
      refine ⟨43600372663123401861064655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29066915108748934574043103 43600372663123401861064655)
      ·
        refine ⟨65400558994685102791596983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43600372663123401861064655 65400558994685102791596983)
        ·
          refine ⟨98100838492027654187395475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65400558994685102791596983 98100838492027654187395475)
          ·
            refine ⟨147151257738041481281093213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98100838492027654187395475 147151257738041481281093213)
            ·
              refine ⟨55181721651765555480409955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147151257738041481281093213 55181721651765555480409955)
              ·
                refine ⟨82772582477648333220614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55181721651765555480409955 82772582477648333220614933)
                ·
                  refine ⟨3879964803639765619716325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82772582477648333220614933 3879964803639765619716325)
                  ·
                    refine ⟨727493400682456053696811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879964803639765619716325 727493400682456053696811)
                    ·
                      rfl

theorem cell23_4250365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_4250365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250365 prefixEnd_4250365 := by exact prefixLift 4250365
  have htrace : WordTrace (prefixWord ++ tailWord_4250365) baseStart_4250365 baseEnd_4250365 := by
    simpa [prefixWord, tailWord_4250365, baseEnd_4250365] using wordTrace_append hprefix tailTrace_4250365
  have hstable : (prefixWord ++ tailWord_4250365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250365).length < 2 ^ (prefixWord ++ tailWord_4250365).sum := by decide
  have hdescent : baseEnd_4250365 < baseStart_4250365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250368 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_4250368 : Nat := 118140960795 + 4250368 * 2 ^ 59
def prefixEnd_4250368 : Nat := 4983230072969 + 3 ^ 40 * 4250368 * 2
def baseEnd_4250368 : Nat := 2182481742489331649352919

theorem tailTrace_4250368 : CollatzResearch.WordTrace tailWord_4250368 prefixEnd_4250368 2182481742489331649352919 := by
  unfold tailWord_4250368
  simp only [CollatzResearch.WordTrace]
  refine ⟨77511828332825057953627879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103349104443766743938170505 77511828332825057953627879)
  ·
    refine ⟨116267742499237586930441819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77511828332825057953627879 116267742499237586930441819)
    ·
      refine ⟨174401613748856380395662729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116267742499237586930441819 174401613748856380395662729)
      ·
        refine ⟨130801210311642285296747047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174401613748856380395662729 130801210311642285296747047)
        ·
          refine ⟨196201815467463427945120571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130801210311642285296747047 196201815467463427945120571)
          ·
            refine ⟨294302723201195141917680857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196201815467463427945120571 294302723201195141917680857)
            ·
              refine ⟨220727042400896356438260643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294302723201195141917680857 220727042400896356438260643)
              ·
                refine ⟨331090563601344534657390965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220727042400896356438260643 331090563601344534657390965)
                ·
                  refine ⟨31039740337626050124130403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331090563601344534657390965 31039740337626050124130403)
                  ·
                    refine ⟨46559610506439075186195605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31039740337626050124130403 46559610506439075186195605)
                    ·
                      refine ⟨2182481742489331649352919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46559610506439075186195605 2182481742489331649352919)
                      ·
                        rfl

theorem cell23_4250368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_4250368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250368 prefixEnd_4250368 := by exact prefixLift 4250368
  have htrace : WordTrace (prefixWord ++ tailWord_4250368) baseStart_4250368 baseEnd_4250368 := by
    simpa [prefixWord, tailWord_4250368, baseEnd_4250368] using wordTrace_append hprefix tailTrace_4250368
  have hstable : (prefixWord ++ tailWord_4250368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250368).length < 2 ^ (prefixWord ++ tailWord_4250368).sum := by decide
  have hdescent : baseEnd_4250368 < baseStart_4250368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250372 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_4250372 : Nat := 118140960795 + 4250372 * 2 ^ 59
def prefixEnd_4250372 : Nat := 4983230072969 + 3 ^ 40 * 4250372 * 2
def baseEnd_4250372 : Nat := 2182483796411949633702901

theorem tailTrace_4250372 : CollatzResearch.WordTrace tailWord_4250372 prefixEnd_4250372 2182483796411949633702901 := by
  unfold tailWord_4250372
  simp only [CollatzResearch.WordTrace]
  refine ⟨77511901278817812295200685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103349201705090416393600913 77511901278817812295200685)
  ·
    refine ⟨29066962979556679610700257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77511901278817812295200685 29066962979556679610700257)
    ·
      refine ⟨21800222234667509708025193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29066962979556679610700257 21800222234667509708025193)
      ·
        refine ⟨16350166676000632281018895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21800222234667509708025193 16350166676000632281018895)
        ·
          refine ⟨24525250014000948421528343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16350166676000632281018895 24525250014000948421528343)
          ·
            refine ⟨36787875021001422632292515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24525250014000948421528343 36787875021001422632292515)
            ·
              refine ⟨55181812531502133948438773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36787875021001422632292515 55181812531502133948438773)
              ·
                refine ⟨5173294924828325057666135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55181812531502133948438773 5173294924828325057666135)
                ·
                  refine ⟨7759942387242487586499203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173294924828325057666135 7759942387242487586499203)
                  ·
                    refine ⟨11639913580863731379748805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7759942387242487586499203 11639913580863731379748805)
                    ·
                      refine ⟨2182483796411949633702901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11639913580863731379748805 2182483796411949633702901)
                      ·
                        rfl

theorem cell23_4250372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_4250372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250372 prefixEnd_4250372 := by exact prefixLift 4250372
  have htrace : WordTrace (prefixWord ++ tailWord_4250372) baseStart_4250372 baseEnd_4250372 := by
    simpa [prefixWord, tailWord_4250372, baseEnd_4250372] using wordTrace_append hprefix tailTrace_4250372
  have hstable : (prefixWord ++ tailWord_4250372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250372).length < 2 ^ (prefixWord ++ tailWord_4250372).sum := by decide
  have hdescent : baseEnd_4250372 < baseStart_4250372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250382 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_4250382 : Nat := 118140960795 + 4250382 * 2 ^ 59
def prefixEnd_4250382 : Nat := 4983230072969 + 3 ^ 40 * 4250382 * 2
def baseEnd_4250382 : Nat := 727496310406164864859285

theorem tailTrace_4250382 : CollatzResearch.WordTrace tailWord_4250382 prefixEnd_4250382 727496310406164864859285 := by
  unfold tailWord_4250382
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378020910949924537283175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103349444858399597532176933 19378020910949924537283175)
  ·
    refine ⟨29067031366424886805924763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19378020910949924537283175 29067031366424886805924763)
    ·
      refine ⟨43600547049637330208887145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067031366424886805924763 43600547049637330208887145)
      ·
        refine ⟨32700410287227997656665359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43600547049637330208887145 32700410287227997656665359)
        ·
          refine ⟨49050615430841996484998039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32700410287227997656665359 49050615430841996484998039)
          ·
            refine ⟨73575923146262994727497059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49050615430841996484998039 73575923146262994727497059)
            ·
              refine ⟨110363884719394492091245589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73575923146262994727497059 110363884719394492091245589)
              ·
                refine ⟨5173307096221616816777137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110363884719394492091245589 5173307096221616816777137)
                ·
                  refine ⟨3879980322166212612582853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5173307096221616816777137 3879980322166212612582853)
                  ·
                    refine ⟨727496310406164864859285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879980322166212612582853 727496310406164864859285)
                    ·
                      rfl

theorem cell23_4250382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_4250382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250382 prefixEnd_4250382 := by exact prefixLift 4250382
  have htrace : WordTrace (prefixWord ++ tailWord_4250382) baseStart_4250382 baseEnd_4250382 := by
    simpa [prefixWord, tailWord_4250382, baseEnd_4250382] using wordTrace_append hprefix tailTrace_4250382
  have hstable : (prefixWord ++ tailWord_4250382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250382).length < 2 ^ (prefixWord ++ tailWord_4250382).sum := by decide
  have hdescent : baseEnd_4250382 < baseStart_4250382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250399 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 2, 4]
def baseStart_4250399 : Nat := 118140960795 + 4250399 * 2 ^ 59
def prefixEnd_4250399 : Nat := 4983230072969 + 3 ^ 40 * 4250399 * 2
def baseEnd_4250399 : Nat := 727499220129873676021759

theorem tailTrace_4250399 : CollatzResearch.WordTrace tailWord_4250399 prefixEnd_4250399 727499220129873676021759 := by
  unfold tailWord_4250399
  simp only [CollatzResearch.WordTrace]
  refine ⟨155024787328537808201634251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103349858219025205467756167 155024787328537808201634251)
  ·
    refine ⟨232537180992806712302451377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155024787328537808201634251 232537180992806712302451377)
    ·
      refine ⟨174402885744605034226838533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232537180992806712302451377 174402885744605034226838533)
      ·
        refine ⟨32700541077113443917532225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174402885744605034226838533 32700541077113443917532225)
        ·
          refine ⟨24525405807835082938149169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32700541077113443917532225 24525405807835082938149169)
          ·
            refine ⟨18394054355876312203611877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24525405807835082938149169 18394054355876312203611877)
            ·
              refine ⟨3448885191726808538177227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18394054355876312203611877 3448885191726808538177227)
              ·
                refine ⟨5173327787590212807265841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448885191726808538177227 5173327787590212807265841)
                ·
                  refine ⟨3879995840692659605449381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5173327787590212807265841 3879995840692659605449381)
                  ·
                    refine ⟨727499220129873676021759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3879995840692659605449381 727499220129873676021759)
                    ·
                      rfl

theorem cell23_4250399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_4250399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250399 prefixEnd_4250399 := by exact prefixLift 4250399
  have htrace : WordTrace (prefixWord ++ tailWord_4250399) baseStart_4250399 baseEnd_4250399 := by
    simpa [prefixWord, tailWord_4250399, baseEnd_4250399] using wordTrace_append hprefix tailTrace_4250399
  have hstable : (prefixWord ++ tailWord_4250399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250399).length < 2 ^ (prefixWord ++ tailWord_4250399).sum := by decide
  have hdescent : baseEnd_4250399 < baseStart_4250399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250426 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_4250426 : Nat := 118140960795 + 4250426 * 2 ^ 59
def prefixEnd_4250426 : Nat := 4983230072969 + 3 ^ 40 * 4250426 * 2
def baseEnd_4250426 : Nat := 2182511524367292422427653

theorem tailTrace_4250426 : CollatzResearch.WordTrace tailWord_4250426 prefixEnd_4250426 2182511524367292422427653 := by
  unfold tailWord_4250426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38756443024859997953216783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103350514732959994541911421 38756443024859997953216783)
  ·
    refine ⟨58134664537289996929825175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38756443024859997953216783 58134664537289996929825175)
    ·
      refine ⟨87201996805934995394737763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58134664537289996929825175 87201996805934995394737763)
      ·
        refine ⟨130802995208902493092106645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87201996805934995394737763 130802995208902493092106645)
        ·
          refine ⟨6131390400417304363692499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 130802995208902493092106645 6131390400417304363692499)
          ·
            refine ⟨9197085600625956545538749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131390400417304363692499 9197085600625956545538749)
            ·
              refine ⟨3448907100234733704577031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9197085600625956545538749 3448907100234733704577031)
              ·
                refine ⟨5173360650352100556865547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448907100234733704577031 5173360650352100556865547)
                ·
                  refine ⟨7760040975528150835298321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173360650352100556865547 7760040975528150835298321)
                  ·
                    refine ⟨5820030731646113126473741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7760040975528150835298321 5820030731646113126473741)
                    ·
                      refine ⟨2182511524367292422427653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820030731646113126473741 2182511524367292422427653)
                      ·
                        rfl

theorem cell23_4250426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_4250426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250426 prefixEnd_4250426 := by exact prefixLift 4250426
  have htrace : WordTrace (prefixWord ++ tailWord_4250426) baseStart_4250426 baseEnd_4250426 := by
    simpa [prefixWord, tailWord_4250426, baseEnd_4250426] using wordTrace_append hprefix tailTrace_4250426
  have hstable : (prefixWord ++ tailWord_4250426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250426).length < 2 ^ (prefixWord ++ tailWord_4250426).sum := by decide
  have hdescent : baseEnd_4250426 < baseStart_4250426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250455 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 8]
def baseStart_4250455 : Nat := 118140960795 + 4250455 * 2 ^ 59
def prefixEnd_4250455 : Nat := 4983230072969 + 3 ^ 40 * 4250455 * 2
def baseEnd_4250455 : Nat := 727508805102090936321673

theorem tailTrace_4250455 : CollatzResearch.WordTrace tailWord_4250455 prefixEnd_4250455 727508805102090936321673 := by
  unfold tailWord_4250455
  simp only [CollatzResearch.WordTrace]
  refine ⟨155026829816334929765672819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103351219877556619843781879 155026829816334929765672819)
  ·
    refine ⟨232540244724502394648509229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155026829816334929765672819 232540244724502394648509229)
    ·
      refine ⟨87202591771688397993190961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232540244724502394648509229 87202591771688397993190961)
      ·
        refine ⟨65401943828766298494893221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87202591771688397993190961 65401943828766298494893221)
        ·
          refine ⟨12262864467893680967792479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65401943828766298494893221 12262864467893680967792479)
          ·
            refine ⟨18394296701840521451688719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12262864467893680967792479 18394296701840521451688719)
            ·
              refine ⟨27591445052760782177533079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18394296701840521451688719 27591445052760782177533079)
              ·
                refine ⟨41387167579141173266299619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27591445052760782177533079 41387167579141173266299619)
                ·
                  refine ⟨62080751368711759899449429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41387167579141173266299619 62080751368711759899449429)
                  ·
                    refine ⟨727508805102090936321673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62080751368711759899449429 727508805102090936321673)
                    ·
                      rfl

theorem cell23_4250455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_4250455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250455 prefixEnd_4250455 := by exact prefixLift 4250455
  have htrace : WordTrace (prefixWord ++ tailWord_4250455) baseStart_4250455 baseEnd_4250455 := by
    simpa [prefixWord, tailWord_4250455, baseEnd_4250455] using wordTrace_append hprefix tailTrace_4250455
  have hstable : (prefixWord ++ tailWord_4250455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250455).length < 2 ^ (prefixWord ++ tailWord_4250455).sum := by decide
  have hdescent : baseEnd_4250455 < baseStart_4250455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250465 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4250465 : Nat := 118140960795 + 4250465 * 2 ^ 59
def prefixEnd_4250465 : Nat := 4983230072969 + 3 ^ 40 * 4250465 * 2
def baseEnd_4250465 : Nat := 2182531550112817769839973

theorem tailTrace_4250465 : CollatzResearch.WordTrace tailWord_4250465 prefixEnd_4250465 2182531550112817769839973 := by
  unfold tailWord_4250465
  simp only [CollatzResearch.WordTrace]
  refine ⟨155027194546298701473536849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103351463030865800982357899 155027194546298701473536849)
  ·
    refine ⟨116270395909724026105152637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155027194546298701473536849 116270395909724026105152637)
    ·
      refine ⟨43601398466146509789432239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116270395909724026105152637 43601398466146509789432239)
      ·
        refine ⟨65402097699219764684148359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43601398466146509789432239 65402097699219764684148359)
        ·
          refine ⟨98103146548829647026222539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65402097699219764684148359 98103146548829647026222539)
          ·
            refine ⟨147154719823244470539333809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98103146548829647026222539 147154719823244470539333809)
            ·
              refine ⟨110366039867433352904500357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147154719823244470539333809 110366039867433352904500357)
              ·
                refine ⟨20693632475143753669593817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110366039867433352904500357 20693632475143753669593817)
                ·
                  refine ⟨15520224356357815252195363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20693632475143753669593817 15520224356357815252195363)
                  ·
                    refine ⟨23280336534536722878293045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15520224356357815252195363 23280336534536722878293045)
                    ·
                      refine ⟨2182531550112817769839973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23280336534536722878293045 2182531550112817769839973)
                      ·
                        rfl

theorem cell23_4250465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4250465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250465 prefixEnd_4250465 := by exact prefixLift 4250465
  have htrace : WordTrace (prefixWord ++ tailWord_4250465) baseStart_4250465 baseEnd_4250465 := by
    simpa [prefixWord, tailWord_4250465, baseEnd_4250465] using wordTrace_append hprefix tailTrace_4250465
  have hstable : (prefixWord ++ tailWord_4250465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250465).length < 2 ^ (prefixWord ++ tailWord_4250465).sum := by decide
  have hdescent : baseEnd_4250465 < baseStart_4250465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250515 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 6, 5]
def baseStart_4250515 : Nat := 118140960795 + 4250515 * 2 ^ 59
def prefixEnd_4250515 : Nat := 4983230072969 + 3 ^ 40 * 4250515 * 2
def baseEnd_4250515 : Nat := 727519074715180858071581

theorem tailTrace_4250515 : CollatzResearch.WordTrace tailWord_4250515 prefixEnd_4250515 727519074715180858071581 := by
  unfold tailWord_4250515
  simp only [CollatzResearch.WordTrace]
  refine ⟨155029018196117560012856999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103352678797411706675237999 155029018196117560012856999)
  ·
    refine ⟨232543527294176340019285499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155029018196117560012856999 232543527294176340019285499)
    ·
      refine ⟨348815290941264510028928249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232543527294176340019285499 348815290941264510028928249)
      ·
        refine ⟨261611468205948382521696187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348815290941264510028928249 261611468205948382521696187)
        ·
          refine ⟨392417202308922573782544281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261611468205948382521696187 392417202308922573782544281)
          ·
            refine ⟨294312901731691930336908211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392417202308922573782544281 294312901731691930336908211)
            ·
              refine ⟨441469352597537895505362317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294312901731691930336908211 441469352597537895505362317)
              ·
                refine ⟨165551007224076710814510869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441469352597537895505362317 165551007224076710814510869)
                ·
                  refine ⟨7760203463628595819430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165551007224076710814510869 7760203463628595819430197)
                  ·
                    refine ⟨727519074715180858071581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7760203463628595819430197 727519074715180858071581)
                    ·
                      rfl

theorem cell23_4250515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 5].length) (baseStart_4250515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250515 prefixEnd_4250515 := by exact prefixLift 4250515
  have htrace : WordTrace (prefixWord ++ tailWord_4250515) baseStart_4250515 baseEnd_4250515 := by
    simpa [prefixWord, tailWord_4250515, baseEnd_4250515] using wordTrace_append hprefix tailTrace_4250515
  have hstable : (prefixWord ++ tailWord_4250515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250515).length < 2 ^ (prefixWord ++ tailWord_4250515).sum := by decide
  have hdescent : baseEnd_4250515 < baseStart_4250515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250532 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_4250532 : Nat := 118140960795 + 4250532 * 2 ^ 59
def prefixEnd_4250532 : Nat := 4983230072969 + 3 ^ 40 * 4250532 * 2
def baseEnd_4250532 : Nat := 727521984438889669234055

theorem tailTrace_4250532 : CollatzResearch.WordTrace tailWord_4250532 prefixEnd_4250532 727521984438889669234055 := by
  unfold tailWord_4250532
  simp only [CollatzResearch.WordTrace]
  refine ⟨77514819118527985958112925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103353092158037314610817233 77514819118527985958112925)
  ·
    refine ⟨29068057169447994734292347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77514819118527985958112925 29068057169447994734292347)
    ·
      refine ⟨43602085754171992101438521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29068057169447994734292347 43602085754171992101438521)
      ·
        refine ⟨32701564315628994076078891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43602085754171992101438521 32701564315628994076078891)
        ·
          refine ⟨49052346473443491114118337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32701564315628994076078891 49052346473443491114118337)
          ·
            refine ⟨36789259855082618335588753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49052346473443491114118337 36789259855082618335588753)
            ·
              refine ⟨27591944891311963751691565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36789259855082618335588753 27591944891311963751691565)
              ·
                refine ⟨10346979334241986406884337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27591944891311963751691565 10346979334241986406884337)
                ·
                  refine ⟨7760234500681489805163253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10346979334241986406884337 7760234500681489805163253)
                  ·
                    refine ⟨727521984438889669234055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7760234500681489805163253 727521984438889669234055)
                    ·
                      rfl

theorem cell23_4250532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_4250532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250532 prefixEnd_4250532 := by exact prefixLift 4250532
  have htrace : WordTrace (prefixWord ++ tailWord_4250532) baseStart_4250532 baseEnd_4250532 := by
    simpa [prefixWord, tailWord_4250532, baseEnd_4250532] using wordTrace_append hprefix tailTrace_4250532
  have hstable : (prefixWord ++ tailWord_4250532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250532).length < 2 ^ (prefixWord ++ tailWord_4250532).sum := by decide
  have hdescent : baseEnd_4250532 < baseStart_4250532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250552 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_4250552 : Nat := 118140960795 + 4250552 * 2 ^ 59
def prefixEnd_4250552 : Nat := 4983230072969 + 3 ^ 40 * 4250552 * 2
def baseEnd_4250552 : Nat := 2182576222929758929452073

theorem tailTrace_4250552 : CollatzResearch.WordTrace tailWord_4250552 prefixEnd_4250552 2182576222929758929452073 := by
  unfold tailWord_4250552
  simp only [CollatzResearch.WordTrace]
  refine ⟨77515183848491757665976955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103353578464655676887969273 77515183848491757665976955)
  ·
    refine ⟨116272775772737636498965433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77515183848491757665976955 116272775772737636498965433)
    ·
      refine ⟨87204581829553227374224075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116272775772737636498965433 87204581829553227374224075)
      ·
        refine ⟨130806872744329841061336113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87204581829553227374224075 130806872744329841061336113)
        ·
          refine ⟨98105154558247380796002085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130806872744329841061336113 98105154558247380796002085)
          ·
            refine ⟨18394716479671383899250391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98105154558247380796002085 18394716479671383899250391)
            ·
              refine ⟨27592074719507075848875587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18394716479671383899250391 27592074719507075848875587)
              ·
                refine ⟨41388112079260613773313381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27592074719507075848875587 41388112079260613773313381)
                ·
                  refine ⟨7760271014861365082496259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41388112079260613773313381 7760271014861365082496259)
                  ·
                    refine ⟨11640406522292047623744389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7760271014861365082496259 11640406522292047623744389)
                    ·
                      refine ⟨2182576222929758929452073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11640406522292047623744389 2182576222929758929452073)
                      ·
                        rfl

theorem cell23_4250552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_4250552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250552 prefixEnd_4250552 := by exact prefixLift 4250552
  have htrace : WordTrace (prefixWord ++ tailWord_4250552) baseStart_4250552 baseEnd_4250552 := by
    simpa [prefixWord, tailWord_4250552, baseEnd_4250552] using wordTrace_append hprefix tailTrace_4250552
  have hstable : (prefixWord ++ tailWord_4250552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250552).length < 2 ^ (prefixWord ++ tailWord_4250552).sum := by decide
  have hdescent : baseEnd_4250552 < baseStart_4250552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250564 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4250564 : Nat := 118140960795 + 4250564 * 2 ^ 59
def prefixEnd_4250564 : Nat := 4983230072969 + 3 ^ 40 * 4250564 * 2
def baseEnd_4250564 : Nat := 2182582384697612882502019

theorem tailTrace_4250564 : CollatzResearch.WordTrace tailWord_4250564 prefixEnd_4250564 2182582384697612882502019 := by
  unfold tailWord_4250564
  simp only [CollatzResearch.WordTrace]
  refine ⟨77515402686470020690695373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103353870248626694254260497 77515402686470020690695373)
  ·
    refine ⟨29068276007426257759010765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77515402686470020690695373 29068276007426257759010765)
    ·
      refine ⟨10900603502784846659629037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29068276007426257759010765 10900603502784846659629037)
      ·
        refine ⟨4087726313544317497360889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10900603502784846659629037 4087726313544317497360889)
        ·
          refine ⟨3065794735158238123020667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087726313544317497360889 3065794735158238123020667)
          ·
            refine ⟨4598692102737357184531001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065794735158238123020667 4598692102737357184531001)
            ·
              refine ⟨3449019077053017888398251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598692102737357184531001 3449019077053017888398251)
              ·
                refine ⟨5173528615579526832597377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449019077053017888398251 5173528615579526832597377)
                ·
                  refine ⟨3880146461684645124448033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5173528615579526832597377 3880146461684645124448033)
                  ·
                    refine ⟨2910109846263483843336025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880146461684645124448033 2910109846263483843336025)
                    ·
                      refine ⟨2182582384697612882502019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910109846263483843336025 2182582384697612882502019)
                      ·
                        rfl

theorem cell23_4250564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4250564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250564 prefixEnd_4250564 := by exact prefixLift 4250564
  have htrace : WordTrace (prefixWord ++ tailWord_4250564) baseStart_4250564 baseEnd_4250564 := by
    simpa [prefixWord, tailWord_4250564, baseEnd_4250564] using wordTrace_append hprefix tailTrace_4250564
  have hstable : (prefixWord ++ tailWord_4250564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250564).length < 2 ^ (prefixWord ++ tailWord_4250564).sum := by decide
  have hdescent : baseEnd_4250564 < baseStart_4250564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250565 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4250565 : Nat := 118140960795 + 4250565 * 2 ^ 59
def prefixEnd_4250565 : Nat := 4983230072969 + 3 ^ 40 * 4250565 * 2
def baseEnd_4250565 : Nat := 2182582898178267378589513

theorem tailTrace_4250565 : CollatzResearch.WordTrace tailWord_4250565 prefixEnd_4250565 2182582898178267378589513 := by
  unfold tailWord_4250565
  simp only [CollatzResearch.WordTrace]
  refine ⟨155030841845936418552177149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103353894563957612368118099 155030841845936418552177149)
  ·
    refine ⟨58136565692226156957066431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155030841845936418552177149 58136565692226156957066431)
    ·
      refine ⟨87204848538339235435599647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58136565692226156957066431 87204848538339235435599647)
      ·
        refine ⟨130807272807508853153399471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87204848538339235435599647 130807272807508853153399471)
        ·
          refine ⟨196210909211263279730099207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130807272807508853153399471 196210909211263279730099207)
          ·
            refine ⟨294316363816894919595148811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196210909211263279730099207 294316363816894919595148811)
            ·
              refine ⟨441474545725342379392723217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294316363816894919595148811 441474545725342379392723217)
              ·
                refine ⟨331105909294006784544542413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441474545725342379392723217 331105909294006784544542413)
                ·
                  refine ⟨124164715985252544204203405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331105909294006784544542413 124164715985252544204203405)
                  ·
                    refine ⟨46561768494469704076576277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124164715985252544204203405 46561768494469704076576277)
                    ·
                      refine ⟨2182582898178267378589513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46561768494469704076576277 2182582898178267378589513)
                      ·
                        rfl

theorem cell23_4250565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4250565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250565 prefixEnd_4250565 := by exact prefixLift 4250565
  have htrace : WordTrace (prefixWord ++ tailWord_4250565) baseStart_4250565 baseEnd_4250565 := by
    simpa [prefixWord, tailWord_4250565, baseEnd_4250565] using wordTrace_append hprefix tailTrace_4250565
  have hstable : (prefixWord ++ tailWord_4250565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250565).length < 2 ^ (prefixWord ++ tailWord_4250565).sum := by decide
  have hdescent : baseEnd_4250565 < baseStart_4250565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250609 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 6]
def baseStart_4250609 : Nat := 118140960795 + 4250609 * 2 ^ 59
def prefixEnd_4250609 : Nat := 4983230072969 + 3 ^ 40 * 4250609 * 2
def baseEnd_4250609 : Nat := 242511721258562800715479

theorem tailTrace_4250609 : CollatzResearch.WordTrace tailWord_4250609 prefixEnd_4250609 242511721258562800715479 := by
  unfold tailWord_4250609
  simp only [CollatzResearch.WordTrace]
  refine ⟨155032446657777014066778881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103354964438518009377852587 155032446657777014066778881)
  ·
    refine ⟨116274334993332760550084161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155032446657777014066778881 116274334993332760550084161)
    ·
      refine ⟨87205751244999570412563121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116274334993332760550084161 87205751244999570412563121)
      ·
        refine ⟨65404313433749677809422341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87205751244999570412563121 65404313433749677809422341)
        ·
          refine ⟨12263308768828064589266689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65404313433749677809422341 12263308768828064589266689)
          ·
            refine ⟨9197481576621048441950017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12263308768828064589266689 9197481576621048441950017)
            ·
              refine ⟨6898111182465786331462513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9197481576621048441950017 6898111182465786331462513)
              ·
                refine ⟨5173583386849339748596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6898111182465786331462513 5173583386849339748596885)
                ·
                  refine ⟨242511721258562800715479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5173583386849339748596885 242511721258562800715479)
                  ·
                    rfl

theorem cell23_4250609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_4250609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250609 prefixEnd_4250609 := by exact prefixLift 4250609
  have htrace : WordTrace (prefixWord ++ tailWord_4250609) baseStart_4250609 baseEnd_4250609 := by
    simpa [prefixWord, tailWord_4250609, baseEnd_4250609] using wordTrace_append hprefix tailTrace_4250609
  have hstable : (prefixWord ++ tailWord_4250609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250609).length < 2 ^ (prefixWord ++ tailWord_4250609).sum := by decide
  have hdescent : baseEnd_4250609 < baseStart_4250609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250619 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 3]
def baseStart_4250619 : Nat := 118140960795 + 4250619 * 2 ^ 59
def prefixEnd_4250619 : Nat := 4983230072969 + 3 ^ 40 * 4250619 * 2
def baseEnd_4250619 : Nat := 2182610626133610167314265

theorem tailTrace_4250619 : CollatzResearch.WordTrace tailWord_4250619 prefixEnd_4250619 2182610626133610167314265 := by
  unfold tailWord_4250619
  simp only [CollatzResearch.WordTrace]
  refine ⟨155032811387740785774642911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103355207591827190516428607 155032811387740785774642911)
  ·
    refine ⟨232549217081611178661964367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155032811387740785774642911 232549217081611178661964367)
    ·
      refine ⟨348823825622416767992946551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232549217081611178661964367 348823825622416767992946551)
      ·
        refine ⟨523235738433625151989419827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348823825622416767992946551 523235738433625151989419827)
        ·
          refine ⟨784853607650437727984129741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523235738433625151989419827 784853607650437727984129741)
          ·
            refine ⟨294320102868914147994048653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 784853607650437727984129741 294320102868914147994048653)
            ·
              refine ⟨110370038575842805497768245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294320102868914147994048653 110370038575842805497768245)
              ·
                refine ⟨10347191116485263015415773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110370038575842805497768245 10347191116485263015415773)
                ·
                  refine ⟨3880196668681973630780915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10347191116485263015415773 3880196668681973630780915)
                  ·
                    refine ⟨5820295003022960446171373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3880196668681973630780915 5820295003022960446171373)
                    ·
                      refine ⟨2182610626133610167314265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820295003022960446171373 2182610626133610167314265)
                      ·
                        rfl

theorem cell23_4250619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 3].length) (baseStart_4250619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250619 prefixEnd_4250619 := by exact prefixLift 4250619
  have htrace : WordTrace (prefixWord ++ tailWord_4250619) baseStart_4250619 baseEnd_4250619 := by
    simpa [prefixWord, tailWord_4250619, baseEnd_4250619] using wordTrace_append hprefix tailTrace_4250619
  have hstable : (prefixWord ++ tailWord_4250619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250619).length < 2 ^ (prefixWord ++ tailWord_4250619).sum := by decide
  have hdescent : baseEnd_4250619 < baseStart_4250619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250629 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_4250629 : Nat := 118140960795 + 4250629 * 2 ^ 59
def prefixEnd_4250629 : Nat := 4983230072969 + 3 ^ 40 * 4250629 * 2
def baseEnd_4250629 : Nat := 2182615760940155128189219

theorem tailTrace_4250629 : CollatzResearch.WordTrace tailWord_4250629 prefixEnd_4250629 2182615760940155128189219 := by
  unfold tailWord_4250629
  simp only [CollatzResearch.WordTrace]
  refine ⟨155033176117704557482506941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103355450745136371655004627 155033176117704557482506941)
  ·
    refine ⟨58137441044139209055940103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155033176117704557482506941 58137441044139209055940103)
    ·
      refine ⟨87206161566208813583910155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58137441044139209055940103 87206161566208813583910155)
      ·
        refine ⟨130809242349313220375865233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87206161566208813583910155 130809242349313220375865233)
        ·
          refine ⟨98106931761984915281898925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130809242349313220375865233 98106931761984915281898925)
          ·
            refine ⟨36790099410744343230712097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98106931761984915281898925 36790099410744343230712097)
            ·
              refine ⟨27592574558058257423034073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36790099410744343230712097 27592574558058257423034073)
              ·
                refine ⟨20694430918543693067275555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27592574558058257423034073 20694430918543693067275555)
                ·
                  refine ⟨31041646377815539600913333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20694430918543693067275555 31041646377815539600913333)
                  ·
                    refine ⟨2910154347920206837585625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31041646377815539600913333 2910154347920206837585625)
                    ·
                      refine ⟨2182615760940155128189219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910154347920206837585625 2182615760940155128189219)
                      ·
                        rfl

theorem cell23_4250629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_4250629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250629 prefixEnd_4250629 := by exact prefixLift 4250629
  have htrace : WordTrace (prefixWord ++ tailWord_4250629) baseStart_4250629 baseEnd_4250629 := by
    simpa [prefixWord, tailWord_4250629, baseEnd_4250629] using wordTrace_append hprefix tailTrace_4250629
  have hstable : (prefixWord ++ tailWord_4250629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250629).length < 2 ^ (prefixWord ++ tailWord_4250629).sum := by decide
  have hdescent : baseEnd_4250629 < baseStart_4250629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250636 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4250636 : Nat := 118140960795 + 4250636 * 2 ^ 59
def prefixEnd_4250636 : Nat := 4983230072969 + 3 ^ 40 * 4250636 * 2
def baseEnd_4250636 : Nat := 2182619355304736600801687

theorem tailTrace_4250636 : CollatzResearch.WordTrace tailWord_4250636 prefixEnd_4250636 2182619355304736600801687 := by
  unfold tailWord_4250636
  simp only [CollatzResearch.WordTrace]
  refine ⟨77516715714339598839005881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103355620952452798452007841 77516715714339598839005881)
  ·
    refine ⟨58137536785754699129254411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77516715714339598839005881 58137536785754699129254411)
    ·
      refine ⟨87206305178632048693881617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58137536785754699129254411 87206305178632048693881617)
      ·
        refine ⟨65404728883974036520411213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87206305178632048693881617 65404728883974036520411213)
        ·
          refine ⟨24526773331490263695154205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65404728883974036520411213 24526773331490263695154205)
          ·
            refine ⟨9197539999308848885682827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24526773331490263695154205 9197539999308848885682827)
            ·
              refine ⟨13796309998963273328524241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9197539999308848885682827 13796309998963273328524241)
              ·
                refine ⟨10347232499222454996393181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13796309998963273328524241 10347232499222454996393181)
                ·
                  refine ⟨3880212187208420623647443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10347232499222454996393181 3880212187208420623647443)
                  ·
                    refine ⟨5820318280812630935471165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3880212187208420623647443 5820318280812630935471165)
                    ·
                      refine ⟨2182619355304736600801687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820318280812630935471165 2182619355304736600801687)
                      ·
                        rfl

theorem cell23_4250636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4250636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250636 prefixEnd_4250636 := by exact prefixLift 4250636
  have htrace : WordTrace (prefixWord ++ tailWord_4250636) baseStart_4250636 baseEnd_4250636 := by
    simpa [prefixWord, tailWord_4250636, baseEnd_4250636] using wordTrace_append hprefix tailTrace_4250636
  have hstable : (prefixWord ++ tailWord_4250636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250636).length < 2 ^ (prefixWord ++ tailWord_4250636).sum := by decide
  have hdescent : baseEnd_4250636 < baseStart_4250636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250672 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_4250672 : Nat := 118140960795 + 4250672 * 2 ^ 59
def prefixEnd_4250672 : Nat := 4983230072969 + 3 ^ 40 * 4250672 * 2
def baseEnd_4250672 : Nat := 2182637840608298459951521

theorem tailTrace_4250672 : CollatzResearch.WordTrace tailWord_4250672 prefixEnd_4250672 2182637840608298459951521 := by
  unfold tailWord_4250672
  simp only [CollatzResearch.WordTrace]
  refine ⟨77517372228274387913161135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103356496304365850550881513 77517372228274387913161135)
  ·
    refine ⟨116276058342411581869741703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77517372228274387913161135 116276058342411581869741703)
    ·
      refine ⟨174414087513617372804612555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116276058342411581869741703 174414087513617372804612555)
      ·
        refine ⟨261621131270426059206918833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174414087513617372804612555 261621131270426059206918833)
        ·
          refine ⟨196215848452819544405189125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261621131270426059206918833 196215848452819544405189125)
          ·
            refine ⟨36790471584903664575972961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196215848452819544405189125 36790471584903664575972961)
            ·
              refine ⟨27592853688677748431979721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36790471584903664575972961 27592853688677748431979721)
              ·
                refine ⟨20694640266508311323984791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27592853688677748431979721 20694640266508311323984791)
                ·
                  refine ⟨31041960399762466985977187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20694640266508311323984791 31041960399762466985977187)
                  ·
                    refine ⟨46562940599643700478965781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31041960399762466985977187 46562940599643700478965781)
                    ·
                      refine ⟨2182637840608298459951521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46562940599643700478965781 2182637840608298459951521)
                      ·
                        rfl

theorem cell23_4250672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_4250672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250672 prefixEnd_4250672 := by exact prefixLift 4250672
  have htrace : WordTrace (prefixWord ++ tailWord_4250672) baseStart_4250672 baseEnd_4250672 := by
    simpa [prefixWord, tailWord_4250672, baseEnd_4250672] using wordTrace_append hprefix tailTrace_4250672
  have hstable : (prefixWord ++ tailWord_4250672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250672).length < 2 ^ (prefixWord ++ tailWord_4250672).sum := by decide
  have hdescent : baseEnd_4250672 < baseStart_4250672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250686 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_4250686 : Nat := 118140960795 + 4250686 * 2 ^ 59
def prefixEnd_4250686 : Nat := 4983230072969 + 3 ^ 40 * 4250686 * 2
def baseEnd_4250686 : Nat := 727548343112487135058819

theorem tailTrace_4250686 : CollatzResearch.WordTrace tailWord_4250686 prefixEnd_4250686 727548343112487135058819 := by
  unfold tailWord_4250686
  simp only [CollatzResearch.WordTrace]
  refine ⟨19379406884812257027166489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103356836718998704144887941 19379406884812257027166489)
  ·
    refine ⟨14534555163609192770374867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19379406884812257027166489 14534555163609192770374867)
    ·
      refine ⟨21801832745413789155562301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14534555163609192770374867 21801832745413789155562301)
      ·
        refine ⟨8175687279530170933335863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21801832745413789155562301 8175687279530170933335863)
        ·
          refine ⟨12263530919295256400003795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8175687279530170933335863 12263530919295256400003795)
          ·
            refine ⟨18395296378942884600005693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12263530919295256400003795 18395296378942884600005693)
            ·
              refine ⟨6898236142103581725002135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18395296378942884600005693 6898236142103581725002135)
              ·
                refine ⟨10347354213155372587503203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6898236142103581725002135 10347354213155372587503203)
                ·
                  refine ⟨15521031319733058881254805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10347354213155372587503203 15521031319733058881254805)
                  ·
                    refine ⟨727548343112487135058819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15521031319733058881254805 727548343112487135058819)
                    ·
                      rfl

theorem cell23_4250686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_4250686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250686 prefixEnd_4250686 := by exact prefixLift 4250686
  have htrace : WordTrace (prefixWord ++ tailWord_4250686) baseStart_4250686 baseEnd_4250686 := by
    simpa [prefixWord, tailWord_4250686, baseEnd_4250686] using wordTrace_append hprefix tailTrace_4250686
  have hstable : (prefixWord ++ tailWord_4250686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250686).length < 2 ^ (prefixWord ++ tailWord_4250686).sum := by decide
  have hdescent : baseEnd_4250686 < baseStart_4250686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250696 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_4250696 : Nat := 118140960795 + 4250696 * 2 ^ 59
def prefixEnd_4250696 : Nat := 4983230072969 + 3 ^ 40 * 4250696 * 2
def baseEnd_4250696 : Nat := 2182650164144006366051411

theorem tailTrace_4250696 : CollatzResearch.WordTrace tailWord_4250696 prefixEnd_4250696 2182650164144006366051411 := by
  unfold tailWord_4250696
  simp only [CollatzResearch.WordTrace]
  refine ⟨77517809904230913962597971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103357079872307885283463961 77517809904230913962597971)
  ·
    refine ⟨116276714856346370943896957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77517809904230913962597971 116276714856346370943896957)
    ·
      refine ⟨43603768071129889103961359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116276714856346370943896957 43603768071129889103961359)
      ·
        refine ⟨65405652106694833655942039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43603768071129889103961359 65405652106694833655942039)
        ·
          refine ⟨98108478160042250483913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65405652106694833655942039 98108478160042250483913059)
          ·
            refine ⟨147162717240063375725869589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98108478160042250483913059 147162717240063375725869589)
            ·
              refine ⟨6898252370627970737150137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147162717240063375725869589 6898252370627970737150137)
              ·
                refine ⟨5173689277970978052862603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6898252370627970737150137 5173689277970978052862603)
                ·
                  refine ⟨7760533916956467079293905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173689277970978052862603 7760533916956467079293905)
                  ·
                    refine ⟨5820400437717350309470429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7760533916956467079293905 5820400437717350309470429)
                    ·
                      refine ⟨2182650164144006366051411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820400437717350309470429 2182650164144006366051411)
                      ·
                        rfl

theorem cell23_4250696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_4250696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250696 prefixEnd_4250696 := by exact prefixLift 4250696
  have htrace : WordTrace (prefixWord ++ tailWord_4250696) baseStart_4250696 baseEnd_4250696 := by
    simpa [prefixWord, tailWord_4250696, baseEnd_4250696] using wordTrace_append hprefix tailTrace_4250696
  have hstable : (prefixWord ++ tailWord_4250696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250696).length < 2 ^ (prefixWord ++ tailWord_4250696).sum := by decide
  have hdescent : baseEnd_4250696 < baseStart_4250696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250709 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4250709 : Nat := 118140960795 + 4250709 * 2 ^ 59
def prefixEnd_4250709 : Nat := 4983230072969 + 3 ^ 40 * 4250709 * 2
def baseEnd_4250709 : Nat := 2182656839392514815188851

theorem tailTrace_4250709 : CollatzResearch.WordTrace tailWord_4250709 prefixEnd_4250709 2182656839392514815188851 := by
  unfold tailWord_4250709
  simp only [CollatzResearch.WordTrace]
  refine ⟨155036093957414731145419181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103357395971609820763612787 155036093957414731145419181)
  ·
    refine ⟨58138535234030524179532193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155036093957414731145419181 58138535234030524179532193)
    ·
      refine ⟨43603901425522893134649145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58138535234030524179532193 43603901425522893134649145)
      ·
        refine ⟨32702926069142169850986859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43603901425522893134649145 32702926069142169850986859)
        ·
          refine ⟨49054389103713254776480289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32702926069142169850986859 49054389103713254776480289)
          ·
            refine ⟨36790791827784941082360217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49054389103713254776480289 36790791827784941082360217)
            ·
              refine ⟨27593093870838705811770163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36790791827784941082360217 27593093870838705811770163)
              ·
                refine ⟨41389640806258058717655245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27593093870838705811770163 41389640806258058717655245)
                ·
                  refine ⟨15521115302346772019120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41389640806258058717655245 15521115302346772019120717)
                  ·
                    refine ⟨5820418238380039507170269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15521115302346772019120717 5820418238380039507170269)
                    ·
                      refine ⟨2182656839392514815188851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820418238380039507170269 2182656839392514815188851)
                      ·
                        rfl

theorem cell23_4250709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4250709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250709 prefixEnd_4250709 := by exact prefixLift 4250709
  have htrace : WordTrace (prefixWord ++ tailWord_4250709) baseStart_4250709 baseEnd_4250709 := by
    simpa [prefixWord, tailWord_4250709, baseEnd_4250709] using wordTrace_append hprefix tailTrace_4250709
  have hstable : (prefixWord ++ tailWord_4250709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250709).length < 2 ^ (prefixWord ++ tailWord_4250709).sum := by decide
  have hdescent : baseEnd_4250709 < baseStart_4250709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250727 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_4250727 : Nat := 118140960795 + 4250727 * 2 ^ 59
def prefixEnd_4250727 : Nat := 4983230072969 + 3 ^ 40 * 4250727 * 2
def baseEnd_4250727 : Nat := 2182666082044295744763769

theorem tailTrace_4250727 : CollatzResearch.WordTrace tailWord_4250727 prefixEnd_4250727 2182666082044295744763769 := by
  unfold tailWord_4250727
  simp only [CollatzResearch.WordTrace]
  refine ⟨155036750471349520219574435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103357833647566346813049623 155036750471349520219574435)
  ·
    refine ⟨232555125707024280329361653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155036750471349520219574435 232555125707024280329361653)
    ·
      refine ⟨21802043035033526280877655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232555125707024280329361653 21802043035033526280877655)
      ·
        refine ⟨32703064552550289421316483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21802043035033526280877655 32703064552550289421316483)
        ·
          refine ⟨49054596828825434131974725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32703064552550289421316483 49054596828825434131974725)
          ·
            refine ⟨9197736905404768899745261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49054596828825434131974725 9197736905404768899745261)
            ·
              refine ⟨3449151339526788337404473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9197736905404768899745261 3449151339526788337404473)
              ·
                refine ⟨2586863504645091253053355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3449151339526788337404473 2586863504645091253053355)
                ·
                  refine ⟨3880295256967636879580033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586863504645091253053355 3880295256967636879580033)
                  ·
                    refine ⟨2910221442725727659685025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880295256967636879580033 2910221442725727659685025)
                    ·
                      refine ⟨2182666082044295744763769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910221442725727659685025 2182666082044295744763769)
                      ·
                        rfl

theorem cell23_4250727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_4250727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250727 prefixEnd_4250727 := by exact prefixLift 4250727
  have htrace : WordTrace (prefixWord ++ tailWord_4250727) baseStart_4250727 baseEnd_4250727 := by
    simpa [prefixWord, tailWord_4250727, baseEnd_4250727] using wordTrace_append hprefix tailTrace_4250727
  have hstable : (prefixWord ++ tailWord_4250727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250727).length < 2 ^ (prefixWord ++ tailWord_4250727).sum := by decide
  have hdescent : baseEnd_4250727 < baseStart_4250727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250736 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2]
def baseStart_4250736 : Nat := 118140960795 + 4250736 * 2 ^ 59
def prefixEnd_4250736 : Nat := 4983230072969 + 3 ^ 40 * 4250736 * 2
def baseEnd_4250736 : Nat := 2182670703370186209551227

theorem tailTrace_4250736 : CollatzResearch.WordTrace tailWord_4250736 prefixEnd_4250736 2182670703370186209551227 := by
  unfold tailWord_4250736
  simp only [CollatzResearch.WordTrace]
  refine ⟨77518539364158457378326031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103358052485544609837768041 77518539364158457378326031)
  ·
    refine ⟨116277809046237686067489047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77518539364158457378326031 116277809046237686067489047)
    ·
      refine ⟨174416713569356529101233571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116277809046237686067489047 174416713569356529101233571)
      ·
        refine ⟨261625070354034793651850357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174416713569356529101233571 261625070354034793651850357)
        ·
          refine ⟨24527350345690761904860971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 261625070354034793651850357 24527350345690761904860971)
          ·
            refine ⟨36791025518536142857291457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24527350345690761904860971 36791025518536142857291457)
            ·
              refine ⟨27593269138902107142968593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36791025518536142857291457 27593269138902107142968593)
              ·
                refine ⟨20694951854176580357226445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27593269138902107142968593 20694951854176580357226445)
                ·
                  refine ⟨7760606945316217633959917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20694951854176580357226445 7760606945316217633959917)
                  ·
                    refine ⟨2910227604493581612734969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7760606945316217633959917 2910227604493581612734969)
                    ·
                      refine ⟨2182670703370186209551227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910227604493581612734969 2182670703370186209551227)
                      ·
                        rfl

theorem cell23_4250736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 3, 2].length) (baseStart_4250736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250736 prefixEnd_4250736 := by exact prefixLift 4250736
  have htrace : WordTrace (prefixWord ++ tailWord_4250736) baseStart_4250736 baseEnd_4250736 := by
    simpa [prefixWord, tailWord_4250736, baseEnd_4250736] using wordTrace_append hprefix tailTrace_4250736
  have hstable : (prefixWord ++ tailWord_4250736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250736).length < 2 ^ (prefixWord ++ tailWord_4250736).sum := by decide
  have hdescent : baseEnd_4250736 < baseStart_4250736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250753 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_4250753 : Nat := 118140960795 + 4250753 * 2 ^ 59
def prefixEnd_4250753 : Nat := 4983230072969 + 3 ^ 40 * 4250753 * 2
def baseEnd_4250753 : Nat := 2182679432541312643038649

theorem tailTrace_4250753 : CollatzResearch.WordTrace tailWord_4250753 prefixEnd_4250753 2182679432541312643038649 := by
  unfold tailWord_4250753
  simp only [CollatzResearch.WordTrace]
  refine ⟨155037698769255326660020913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103358465846170217773347275 155037698769255326660020913)
  ·
    refine ⟨116278274076941494995015685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155037698769255326660020913 116278274076941494995015685)
    ·
      refine ⟨21802176389426530311565441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116278274076941494995015685 21802176389426530311565441)
      ·
        refine ⟨16351632292069897733674081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21802176389426530311565441 16351632292069897733674081)
        ·
          refine ⟨12263724219052423300255561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16351632292069897733674081 12263724219052423300255561)
          ·
            refine ⟨9197793164289317475191671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12263724219052423300255561 9197793164289317475191671)
            ·
              refine ⟨13796689746433976212787507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9197793164289317475191671 13796689746433976212787507)
              ·
                refine ⟨20695034619650964319181261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13796689746433976212787507 20695034619650964319181261)
                ·
                  refine ⟨7760637982369111619692973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20695034619650964319181261 7760637982369111619692973)
                  ·
                    refine ⟨2910239243388416857384865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7760637982369111619692973 2910239243388416857384865)
                    ·
                      refine ⟨2182679432541312643038649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910239243388416857384865 2182679432541312643038649)
                      ·
                        rfl

theorem cell23_4250753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_4250753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250753 prefixEnd_4250753 := by exact prefixLift 4250753
  have htrace : WordTrace (prefixWord ++ tailWord_4250753) baseStart_4250753 baseEnd_4250753 := by
    simpa [prefixWord, tailWord_4250753, baseEnd_4250753] using wordTrace_append hprefix tailTrace_4250753
  have hstable : (prefixWord ++ tailWord_4250753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250753).length < 2 ^ (prefixWord ++ tailWord_4250753).sum := by decide
  have hdescent : baseEnd_4250753 < baseStart_4250753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250799 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_4250799 : Nat := 118140960795 + 4250799 * 2 ^ 59
def prefixEnd_4250799 : Nat := 4983230072969 + 3 ^ 40 * 4250799 * 2
def baseEnd_4250799 : Nat := 2182703052651419463063437

theorem tailTrace_4250799 : CollatzResearch.WordTrace tailWord_4250799 prefixEnd_4250799 2182703052651419463063437 := by
  unfold tailWord_4250799
  simp only [CollatzResearch.WordTrace]
  refine ⟨155039376527088676516195451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103359584351392451010796967 155039376527088676516195451)
  ·
    refine ⟨232559064790633014774293177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155039376527088676516195451 232559064790633014774293177)
    ·
      refine ⟨174419298592974761080719883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232559064790633014774293177 174419298592974761080719883)
      ·
        refine ⟨261628947889462141621079825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174419298592974761080719883 261628947889462141621079825)
        ·
          refine ⟨196221710917096606215809869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261628947889462141621079825 196221710917096606215809869)
          ·
            refine ⟨73583141593911227330928701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196221710917096606215809869 73583141593911227330928701)
            ·
              refine ⟨27593678097716710249098263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73583141593911227330928701 27593678097716710249098263)
              ·
                refine ⟨41390517146575065373647395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27593678097716710249098263 41390517146575065373647395)
                ·
                  refine ⟨62085775719862598060471093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41390517146575065373647395 62085775719862598060471093)
                  ·
                    refine ⟨5820541473737118568169165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62085775719862598060471093 5820541473737118568169165)
                    ·
                      refine ⟨2182703052651419463063437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5820541473737118568169165 2182703052651419463063437)
                      ·
                        rfl

theorem cell23_4250799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_4250799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250799 prefixEnd_4250799 := by exact prefixLift 4250799
  have htrace : WordTrace (prefixWord ++ tailWord_4250799) baseStart_4250799 baseEnd_4250799 := by
    simpa [prefixWord, tailWord_4250799, baseEnd_4250799] using wordTrace_append hprefix tailTrace_4250799
  have hstable : (prefixWord ++ tailWord_4250799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250799).length < 2 ^ (prefixWord ++ tailWord_4250799).sum := by decide
  have hdescent : baseEnd_4250799 < baseStart_4250799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250819 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 2, 5]
def baseStart_4250819 : Nat := 118140960795 + 4250819 * 2 ^ 59
def prefixEnd_4250819 : Nat := 4983230072969 + 3 ^ 40 * 4250819 * 2
def baseEnd_4250819 : Nat := 727571107421503128271115

theorem tailTrace_4250819 : CollatzResearch.WordTrace tailWord_4250819 prefixEnd_4250819 727571107421503128271115 := by
  unfold tailWord_4250819
  simp only [CollatzResearch.WordTrace]
  refine ⟨155040105987016219931923511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103360070658010813287949007 155040105987016219931923511)
  ·
    refine ⟨232560158980524329897885267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155040105987016219931923511 232560158980524329897885267)
    ·
      refine ⟨348840238470786494846827901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232560158980524329897885267 348840238470786494846827901)
      ·
        refine ⟨130815089426544935567560463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348840238470786494846827901 130815089426544935567560463)
        ·
          refine ⟨196222634139817403351340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130815089426544935567560463 196222634139817403351340695)
          ·
            refine ⟨294333951209726105027011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196222634139817403351340695 294333951209726105027011043)
            ·
              refine ⟨441500926814589157540516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294333951209726105027011043 441500926814589157540516565)
              ·
                refine ⟨10347677972216933379855857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 441500926814589157540516565 10347677972216933379855857)
                ·
                  refine ⟨7760758479162700034891893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10347677972216933379855857 7760758479162700034891893)
                  ·
                    refine ⟨727571107421503128271115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7760758479162700034891893 727571107421503128271115)
                    ·
                      rfl

theorem cell23_4250819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 5].length) (baseStart_4250819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250819 prefixEnd_4250819 := by exact prefixLift 4250819
  have htrace : WordTrace (prefixWord ++ tailWord_4250819) baseStart_4250819 baseEnd_4250819 := by
    simpa [prefixWord, tailWord_4250819, baseEnd_4250819] using wordTrace_append hprefix tailTrace_4250819
  have hstable : (prefixWord ++ tailWord_4250819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250819).length < 2 ^ (prefixWord ++ tailWord_4250819).sum := by decide
  have hdescent : baseEnd_4250819 < baseStart_4250819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250879 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 8]
def baseStart_4250879 : Nat := 118140960795 + 4250879 * 2 ^ 59
def prefixEnd_4250879 : Nat := 4983230072969 + 3 ^ 40 * 4250879 * 2
def baseEnd_4250879 : Nat := 242527125678197683340341

theorem tailTrace_4250879 : CollatzResearch.WordTrace tailWord_4250879 prefixEnd_4250879 242527125678197683340341 := by
  unfold tailWord_4250879
  simp only [CollatzResearch.WordTrace]
  refine ⟨155042294366798850179107691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103361529577865900119405127 155042294366798850179107691)
  ·
    refine ⟨232563441550198275268661537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155042294366798850179107691 232563441550198275268661537)
    ·
      refine ⟨174422581162648706451496153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232563441550198275268661537 174422581162648706451496153)
      ·
        refine ⟨130816935871986529838622115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174422581162648706451496153 130816935871986529838622115)
        ·
          refine ⟨196225403807979794757933173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130816935871986529838622115 196225403807979794757933173)
          ·
            refine ⟨18396131606998105758556235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196225403807979794757933173 18396131606998105758556235)
            ·
              refine ⟨27594197410497158637834353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18396131606998105758556235 27594197410497158637834353)
              ·
                refine ⟨20695648057872868978375765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27594197410497158637834353 20695648057872868978375765)
                ·
                  refine ⟨242527125678197683340341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20695648057872868978375765 242527125678197683340341)
                  ·
                    rfl

theorem cell23_4250879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 8].length) (baseStart_4250879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250879 prefixEnd_4250879 := by exact prefixLift 4250879
  have htrace : WordTrace (prefixWord ++ tailWord_4250879) baseStart_4250879 baseEnd_4250879 := by
    simpa [prefixWord, tailWord_4250879, baseEnd_4250879] using wordTrace_append hprefix tailTrace_4250879
  have hstable : (prefixWord ++ tailWord_4250879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250879).length < 2 ^ (prefixWord ++ tailWord_4250879).sum := by decide
  have hdescent : baseEnd_4250879 < baseStart_4250879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250980 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_4250980 : Nat := 118140960795 + 4250980 * 2 ^ 59
def prefixEnd_4250980 : Nat := 4983230072969 + 3 ^ 40 * 4250980 * 2
def baseEnd_4250980 : Nat := 2182795992649883254900105

theorem tailTrace_4250980 : CollatzResearch.WordTrace tailWord_4250980 prefixEnd_4250980 2182795992649883254900105 := by
  unfold tailWord_4250980
  simp only [CollatzResearch.WordTrace]
  refine ⟨77522989069716472214267197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103363985426288629619022929 77522989069716472214267197)
  ·
    refine ⟨29071120901143677080350199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77522989069716472214267197 29071120901143677080350199)
    ·
      refine ⟨43606681351715515620525299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29071120901143677080350199 43606681351715515620525299)
      ·
        refine ⟨65410022027573273430787949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43606681351715515620525299 65410022027573273430787949)
        ·
          refine ⟨24528758260339977536545481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65410022027573273430787949 24528758260339977536545481)
          ·
            refine ⟨18396568695254983152409111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24528758260339977536545481 18396568695254983152409111)
            ·
              refine ⟨27594853042882474728613667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18396568695254983152409111 27594853042882474728613667)
              ·
                refine ⟨41392279564323712092920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27594853042882474728613667 41392279564323712092920501)
                ·
                  refine ⟨3880526209155348008711297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41392279564323712092920501 3880526209155348008711297)
                  ·
                    refine ⟨2910394656866511006533473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880526209155348008711297 2910394656866511006533473)
                    ·
                      refine ⟨2182795992649883254900105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910394656866511006533473 2182795992649883254900105)
                      ·
                        rfl

theorem cell23_4250980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_4250980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250980 prefixEnd_4250980 := by exact prefixLift 4250980
  have htrace : WordTrace (prefixWord ++ tailWord_4250980) baseStart_4250980 baseEnd_4250980 := by
    simpa [prefixWord, tailWord_4250980, baseEnd_4250980] using wordTrace_append hprefix tailTrace_4250980
  have hstable : (prefixWord ++ tailWord_4250980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250980).length < 2 ^ (prefixWord ++ tailWord_4250980).sum := by decide
  have hdescent : baseEnd_4250980 < baseStart_4250980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4250984 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4250984 : Nat := 118140960795 + 4250984 * 2 ^ 59
def prefixEnd_4250984 : Nat := 4983230072969 + 3 ^ 40 * 4250984 * 2
def baseEnd_4250984 : Nat := 2182798046572501239250087

theorem tailTrace_4250984 : CollatzResearch.WordTrace tailWord_4250984 prefixEnd_4250984 2182798046572501239250087 := by
  unfold tailWord_4250984
  simp only [CollatzResearch.WordTrace]
  refine ⟨77523062015709226555840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103364082687612302074453337 77523062015709226555840003)
  ·
    refine ⟨116284593023563839833760005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77523062015709226555840003 116284593023563839833760005)
    ·
      refine ⟨21803361191918219968830001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116284593023563839833760005 21803361191918219968830001)
      ·
        refine ⟨16352520893938664976622501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21803361191918219968830001 16352520893938664976622501)
        ·
          refine ⟨3066097667613499683116719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16352520893938664976622501 3066097667613499683116719)
          ·
            refine ⟨4599146501420249524675079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066097667613499683116719 4599146501420249524675079)
            ·
              refine ⟨6898719752130374287012619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599146501420249524675079 6898719752130374287012619)
              ·
                refine ⟨10348079628195561430518929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6898719752130374287012619 10348079628195561430518929)
                ·
                  refine ⟨7761059721146671072889197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10348079628195561430518929 7761059721146671072889197)
                  ·
                    refine ⟨2910397395430001652333449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7761059721146671072889197 2910397395430001652333449)
                    ·
                      refine ⟨2182798046572501239250087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910397395430001652333449 2182798046572501239250087)
                      ·
                        rfl

theorem cell23_4250984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4250984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4250984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4250984 prefixEnd_4250984 := by exact prefixLift 4250984
  have htrace : WordTrace (prefixWord ++ tailWord_4250984) baseStart_4250984 baseEnd_4250984 := by
    simpa [prefixWord, tailWord_4250984, baseEnd_4250984] using wordTrace_append hprefix tailTrace_4250984
  have hstable : (prefixWord ++ tailWord_4250984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4250984).length < 2 ^ (prefixWord ++ tailWord_4250984).sum := by decide
  have hdescent : baseEnd_4250984 < baseStart_4250984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4250984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251048 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4251048 : Nat := 118140960795 + 4251048 * 2 ^ 59
def prefixEnd_4251048 : Nat := 4983230072969 + 3 ^ 40 * 4251048 * 2
def baseEnd_4251048 : Nat := 2182830909334388988849793

theorem tailTrace_4251048 : CollatzResearch.WordTrace tailWord_4251048 prefixEnd_4251048 2182830909334388988849793 := by
  unfold tailWord_4251048
  simp only [CollatzResearch.WordTrace]
  refine ⟨77524229151593296021004899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103365638868791061361339865 77524229151593296021004899)
  ·
    refine ⟨116286343727389944031507349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77524229151593296021004899 116286343727389944031507349)
    ·
      refine ⟨5450922362221403626476907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 116286343727389944031507349 5450922362221403626476907)
      ·
        refine ⟨8176383543332105439715361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450922362221403626476907 8176383543332105439715361)
        ·
          refine ⟨6132287657499079079786521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8176383543332105439715361 6132287657499079079786521)
          ·
            refine ⟨4599215743124309309839891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132287657499079079786521 4599215743124309309839891)
            ·
              refine ⟨6898823614686463964759837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599215743124309309839891 6898823614686463964759837)
              ·
                refine ⟨2587058855507423986784939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6898823614686463964759837 2587058855507423986784939)
                ·
                  refine ⟨3880588283261135980177409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587058855507423986784939 3880588283261135980177409)
                  ·
                    refine ⟨2910441212445851985133057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880588283261135980177409 2910441212445851985133057)
                    ·
                      refine ⟨2182830909334388988849793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2910441212445851985133057 2182830909334388988849793)
                      ·
                        rfl

theorem cell23_4251048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4251048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251048 prefixEnd_4251048 := by exact prefixLift 4251048
  have htrace : WordTrace (prefixWord ++ tailWord_4251048) baseStart_4251048 baseEnd_4251048 := by
    simpa [prefixWord, tailWord_4251048, baseEnd_4251048] using wordTrace_append hprefix tailTrace_4251048
  have hstable : (prefixWord ++ tailWord_4251048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251048).length < 2 ^ (prefixWord ++ tailWord_4251048).sum := by decide
  have hdescent : baseEnd_4251048 < baseStart_4251048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251133 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_4251133 : Nat := 118140960795 + 4251133 * 2 ^ 59
def prefixEnd_4251133 : Nat := 4983230072969 + 3 ^ 40 * 4251133 * 2
def baseEnd_4251133 : Nat := 2182874555190021156286901

theorem tailTrace_4251133 : CollatzResearch.WordTrace tailWord_4251133 prefixEnd_4251133 2182874555190021156286901 := by
  unfold tailWord_4251133
  simp only [CollatzResearch.WordTrace]
  refine ⟨155051558507878651558854053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103367705671919101039236035 155051558507878651558854053)
  ·
    refine ⟨29072167220227247167285135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155051558507878651558854053 29072167220227247167285135)
    ·
      refine ⟨43608250830340870750927703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29072167220227247167285135 43608250830340870750927703)
      ·
        refine ⟨65412376245511306126391555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43608250830340870750927703 65412376245511306126391555)
        ·
          refine ⟨98118564368266959189587333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65412376245511306126391555 98118564368266959189587333)
          ·
            refine ⟨18397230819050054848047625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98118564368266959189587333 18397230819050054848047625)
            ·
              refine ⟨13797923114287541136035719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18397230819050054848047625 13797923114287541136035719)
              ·
                refine ⟨20696884671431311704053579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13797923114287541136035719 20696884671431311704053579)
                ·
                  refine ⟨31045327007146967556080369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20696884671431311704053579 31045327007146967556080369)
                  ·
                    refine ⟨23283995255360225667060277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31045327007146967556080369 23283995255360225667060277)
                    ·
                      refine ⟨2182874555190021156286901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23283995255360225667060277 2182874555190021156286901)
                      ·
                        rfl

theorem cell23_4251133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_4251133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251133 prefixEnd_4251133 := by exact prefixLift 4251133
  have htrace : WordTrace (prefixWord ++ tailWord_4251133) baseStart_4251133 baseEnd_4251133 := by
    simpa [prefixWord, tailWord_4251133, baseEnd_4251133] using wordTrace_append hprefix tailTrace_4251133
  have hstable : (prefixWord ++ tailWord_4251133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251133).length < 2 ^ (prefixWord ++ tailWord_4251133).sum := by decide
  have hdescent : baseEnd_4251133 < baseStart_4251133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4251160 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4251160 : Nat := 118140960795 + 4251160 * 2 ^ 59
def prefixEnd_4251160 : Nat := 4983230072969 + 3 ^ 40 * 4251160 * 2
def baseEnd_4251160 : Nat := 2182888419167692550649277

theorem tailTrace_4251160 : CollatzResearch.WordTrace tailWord_4251160 prefixEnd_4251160 2182888419167692550649277 := by
  unfold tailWord_4251160
  simp only [CollatzResearch.WordTrace]
  refine ⟨77526271639390417585043467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103368362185853890113391289 77526271639390417585043467)
  ·
    refine ⟨116289407459085626377565201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77526271639390417585043467 116289407459085626377565201)
    ·
      refine ⟨87217055594314219783173901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116289407459085626377565201 87217055594314219783173901)
      ·
        refine ⟨32706395847867832418690213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87217055594314219783173901 32706395847867832418690213)
        ·
          refine ⟨6132449221475218578504415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32706395847867832418690213 6132449221475218578504415)
          ·
            refine ⟨9198673832212827867756623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6132449221475218578504415 9198673832212827867756623)
            ·
              refine ⟨13798010748319241801634935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9198673832212827867756623 13798010748319241801634935)
              ·
                refine ⟨20697016122478862702452403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13798010748319241801634935 20697016122478862702452403)
                ·
                  refine ⟨31045524183718294053678605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20697016122478862702452403 31045524183718294053678605)
                  ·
                    refine ⟨11642071568894360270129477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31045524183718294053678605 11642071568894360270129477)
                    ·
                      refine ⟨2182888419167692550649277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11642071568894360270129477 2182888419167692550649277)
                      ·
                        rfl

theorem cell23_4251160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4251160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4251160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4251160 prefixEnd_4251160 := by exact prefixLift 4251160
  have htrace : WordTrace (prefixWord ++ tailWord_4251160) baseStart_4251160 baseEnd_4251160 := by
    simpa [prefixWord, tailWord_4251160, baseEnd_4251160] using wordTrace_append hprefix tailTrace_4251160
  have hstable : (prefixWord ++ tailWord_4251160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4251160).length < 2 ^ (prefixWord ++ tailWord_4251160).sum := by decide
  have hdescent : baseEnd_4251160 < baseStart_4251160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4251160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
