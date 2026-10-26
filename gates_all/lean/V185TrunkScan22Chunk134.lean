import V185TrunkScan22Chunk133

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1196465 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_1196465 : Nat := 118140960795 + 1196465 * 2 ^ 59
def prefixEnd_1196465 : Nat := 4983230072969 + 3 ^ 40 * 1196465 * 2
def baseEnd_1196465 : Nat := 409574420854511039256709

theorem tailTrace_1196465 : CollatzResearch.WordTrace tailWord_1196465 prefixEnd_1196465 409574420854511039256709 := by
  unfold tailWord_1196465
  simp only [CollatzResearch.WordTrace]
  refine ⟨43638663610419119798774849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29092442406946079865849899 43638663610419119798774849)
  ·
    refine ⟨32728997707814339849081137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43638663610419119798774849 32728997707814339849081137)
    ·
      refine ⟨24546748280860754886810853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32728997707814339849081137 24546748280860754886810853)
      ·
        refine ⟨4602515302661391541277035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24546748280860754886810853 4602515302661391541277035)
        ·
          refine ⟨6903772953992087311915553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602515302661391541277035 6903772953992087311915553)
          ·
            refine ⟨5177829715494065483936665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6903772953992087311915553 5177829715494065483936665)
            ·
              refine ⟨3883372286620549112952499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177829715494065483936665 3883372286620549112952499)
              ·
                refine ⟨5825058429930823669428749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883372286620549112952499 5825058429930823669428749)
                ·
                  refine ⟨2184396911224058876035781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5825058429930823669428749 2184396911224058876035781)
                  ·
                    refine ⟨409574420854511039256709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2184396911224058876035781 409574420854511039256709)
                    ·
                      rfl

theorem cell22_1196465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_1196465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196465 prefixEnd_1196465 := by exact prefixLift 1196465
  have htrace : WordTrace (prefixWord ++ tailWord_1196465) baseStart_1196465 baseEnd_1196465 := by
    simpa [prefixWord, tailWord_1196465, baseEnd_1196465] using wordTrace_append hprefix tailTrace_1196465
  have hstable : (prefixWord ++ tailWord_1196465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196465).length < 2 ^ (prefixWord ++ tailWord_1196465).sum := by decide
  have hdescent : baseEnd_1196465 < baseStart_1196465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196523 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_1196523 : Nat := 118140960795 + 1196523 * 2 ^ 59
def prefixEnd_1196523 : Nat := 4983230072969 + 3 ^ 40 * 1196523 * 2
def baseEnd_1196523 : Nat := 409594275439818221306531

theorem tailTrace_1196523 : CollatzResearch.WordTrace tailWord_1196523 prefixEnd_1196523 409594275439818221306531 := by
  unfold tailWord_1196523
  simp only [CollatzResearch.WordTrace]
  refine ⟨43640779044208995704386223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29093852696139330469590815 43640779044208995704386223)
  ·
    refine ⟨65461168566313493556579335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43640779044208995704386223 65461168566313493556579335)
    ·
      refine ⟨98191752849470240334869003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65461168566313493556579335 98191752849470240334869003)
      ·
        refine ⟨147287629274205360502303505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98191752849470240334869003 147287629274205360502303505)
        ·
          refine ⟨110465721955654020376727629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147287629274205360502303505 110465721955654020376727629)
          ·
            refine ⟨41424645733370257641272861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110465721955654020376727629 41424645733370257641272861)
            ·
              refine ⟨15534242150013846615477323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41424645733370257641272861 15534242150013846615477323)
              ·
                refine ⟨23301363225020769923215985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15534242150013846615477323 23301363225020769923215985)
                ·
                  refine ⟨17476022418765577442411989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23301363225020769923215985 17476022418765577442411989)
                  ·
                    refine ⟨409594275439818221306531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17476022418765577442411989 409594275439818221306531)
                    ·
                      rfl

theorem cell22_1196523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_1196523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196523 prefixEnd_1196523 := by exact prefixLift 1196523
  have htrace : WordTrace (prefixWord ++ tailWord_1196523) baseStart_1196523 baseEnd_1196523 := by
    simpa [prefixWord, tailWord_1196523, baseEnd_1196523] using wordTrace_append hprefix tailTrace_1196523
  have hstable : (prefixWord ++ tailWord_1196523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196523).length < 2 ^ (prefixWord ++ tailWord_1196523).sum := by decide
  have hdescent : baseEnd_1196523 < baseStart_1196523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196647 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1196647 : Nat := 118140960795 + 1196647 * 2 ^ 59
def prefixEnd_1196647 : Nat := 4983230072969 + 3 ^ 40 * 1196647 * 2
def baseEnd_1196647 : Nat := 409636723173923231206151

theorem tailTrace_1196647 : CollatzResearch.WordTrace tailWord_1196647 prefixEnd_1196647 409636723173923231206151 := by
  unfold tailWord_1196647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43645301695759764881900195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29096867797173176587933463 43645301695759764881900195)
  ·
    refine ⟨65467952543639647322850293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43645301695759764881900195 65467952543639647322850293)
    ·
      refine ⟨6137620550966216936517215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65467952543639647322850293 6137620550966216936517215)
      ·
        refine ⟨9206430826449325404775823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6137620550966216936517215 9206430826449325404775823)
        ·
          refine ⟨13809646239673988107163735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9206430826449325404775823 13809646239673988107163735)
          ·
            refine ⟨20714469359510982160745603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13809646239673988107163735 20714469359510982160745603)
            ·
              refine ⟨31071704039266473241118405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20714469359510982160745603 31071704039266473241118405)
              ·
                refine ⟨5825944507362463732709701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31071704039266473241118405 5825944507362463732709701)
                ·
                  refine ⟨1092364595130461949883069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5825944507362463732709701 1092364595130461949883069)
                  ·
                    refine ⟨409636723173923231206151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092364595130461949883069 409636723173923231206151)
                    ·
                      rfl

theorem cell22_1196647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1196647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196647 prefixEnd_1196647 := by exact prefixLift 1196647
  have htrace : WordTrace (prefixWord ++ tailWord_1196647) baseStart_1196647 baseEnd_1196647 := by
    simpa [prefixWord, tailWord_1196647, baseEnd_1196647] using wordTrace_append hprefix tailTrace_1196647
  have hstable : (prefixWord ++ tailWord_1196647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196647).length < 2 ^ (prefixWord ++ tailWord_1196647).sum := by decide
  have hdescent : baseEnd_1196647 < baseStart_1196647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196711 : List Nat := [1, 1, 6, 3, 2, 1, 8]
def baseStart_1196711 : Nat := 118140960795 + 1196711 * 2 ^ 59
def prefixEnd_1196711 : Nat := 4983230072969 + 3 ^ 40 * 1196711 * 2
def baseEnd_1196711 : Nat := 15172541914142533244665

theorem tailTrace_1196711 : CollatzResearch.WordTrace tailWord_1196711 prefixEnd_1196711 15172541914142533244665 := by
  unfold tailWord_1196711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43647635967527903812229987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29098423978351935874819991 43647635967527903812229987)
  ·
    refine ⟨65471453951291855718344981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43647635967527903812229987 65471453951291855718344981)
    ·
      refine ⟨3068974403966805736797421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65471453951291855718344981 3068974403966805736797421)
      ·
        refine ⟨1150865401487552151299033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3068974403966805736797421 1150865401487552151299033)
        ·
          refine ⟨863149051115664113474275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150865401487552151299033 863149051115664113474275)
          ·
            refine ⟨1294723576673496170211413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863149051115664113474275 1294723576673496170211413)
            ·
              refine ⟨15172541914142533244665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1294723576673496170211413 15172541914142533244665)
              ·
                rfl

theorem cell22_1196711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 8].length) (baseStart_1196711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196711 prefixEnd_1196711 := by exact prefixLift 1196711
  have htrace : WordTrace (prefixWord ++ tailWord_1196711) baseStart_1196711 baseEnd_1196711 := by
    simpa [prefixWord, tailWord_1196711, baseEnd_1196711] using wordTrace_append hprefix tailTrace_1196711
  have hstable : (prefixWord ++ tailWord_1196711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196711).length < 2 ^ (prefixWord ++ tailWord_1196711).sum := by decide
  have hdescent : baseEnd_1196711 < baseStart_1196711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196722 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_1196722 : Nat := 118140960795 + 1196722 * 2 ^ 59
def prefixEnd_1196722 : Nat := 4983230072969 + 3 ^ 40 * 1196722 * 2
def baseEnd_1196722 : Nat := 136554132402216011860307

theorem tailTrace_1196722 : CollatzResearch.WordTrace tailWord_1196722 prefixEnd_1196722 136554132402216011860307 := by
  unfold tailWord_1196722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912009292622013172720105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29098691446992035127253613 10912009292622013172720105)
  ·
    refine ⟨8184006969466509879540079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10912009292622013172720105 8184006969466509879540079)
    ·
      refine ⟨12276010454199764819310119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184006969466509879540079 12276010454199764819310119)
      ·
        refine ⟨18414015681299647228965179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276010454199764819310119 18414015681299647228965179)
        ·
          refine ⟨27621023521949470843447769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18414015681299647228965179 27621023521949470843447769)
          ·
            refine ⟨20715767641462103132585827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27621023521949470843447769 20715767641462103132585827)
            ·
              refine ⟨31073651462193154698878741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20715767641462103132585827 31073651462193154698878741)
              ·
                refine ⟨1456577412290304126509941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31073651462193154698878741 1456577412290304126509941)
                ·
                  refine ⟨136554132402216011860307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456577412290304126509941 136554132402216011860307)
                  ·
                    rfl

theorem cell22_1196722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_1196722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196722 prefixEnd_1196722 := by exact prefixLift 1196722
  have htrace : WordTrace (prefixWord ++ tailWord_1196722) baseStart_1196722 baseEnd_1196722 := by
    simpa [prefixWord, tailWord_1196722, baseEnd_1196722] using wordTrace_append hprefix tailTrace_1196722
  have hstable : (prefixWord ++ tailWord_1196722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196722).length < 2 ^ (prefixWord ++ tailWord_1196722).sum := by decide
  have hdescent : baseEnd_1196722 < baseStart_1196722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196784 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_1196784 : Nat := 118140960795 + 1196784 * 2 ^ 59
def prefixEnd_1196784 : Nat := 4983230072969 + 3 ^ 40 * 1196784 * 2
def baseEnd_1196784 : Nat := 136561207024566846843577

theorem tailTrace_1196784 : CollatzResearch.WordTrace tailWord_1196784 prefixEnd_1196784 136561207024566846843577 := by
  unfold tailWord_1196784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825149248131718639818703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29100198997508958186424937 21825149248131718639818703)
  ·
    refine ⟨32737723872197577959728055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21825149248131718639818703 32737723872197577959728055)
    ·
      refine ⟨49106585808296366939592083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32737723872197577959728055 49106585808296366939592083)
      ·
        refine ⟨73659878712444550409388125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49106585808296366939592083 73659878712444550409388125)
        ·
          refine ⟨27622454517166706403520547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73659878712444550409388125 27622454517166706403520547)
          ·
            refine ⟨41433681775750059605280821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27622454517166706403520547 41433681775750059605280821)
            ·
              refine ⟨3884407666476568087995077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41433681775750059605280821 3884407666476568087995077)
              ·
                refine ⟨728326437464356516499077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3884407666476568087995077 728326437464356516499077)
                ·
                  refine ⟨136561207024566846843577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728326437464356516499077 136561207024566846843577)
                  ·
                    rfl

theorem cell22_1196784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_1196784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196784 prefixEnd_1196784 := by exact prefixLift 1196784
  have htrace : WordTrace (prefixWord ++ tailWord_1196784) baseStart_1196784 baseEnd_1196784 := by
    simpa [prefixWord, tailWord_1196784, baseEnd_1196784] using wordTrace_append hprefix tailTrace_1196784
  have hstable : (prefixWord ++ tailWord_1196784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196784).length < 2 ^ (prefixWord ++ tailWord_1196784).sum := by decide
  have hdescent : baseEnd_1196784 < baseStart_1196784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196788 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1196788 : Nat := 118140960795 + 1196788 * 2 ^ 59
def prefixEnd_1196788 : Nat := 4983230072969 + 3 ^ 40 * 1196788 * 2
def baseEnd_1196788 : Nat := 409684990355445863430719

theorem tailTrace_1196788 : CollatzResearch.WordTrace tailWord_1196788 prefixEnd_1196788 409684990355445863430719 := by
  unfold tailWord_1196788
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825222194124472981391509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29100296258832630641855345 21825222194124472981391509)
  ·
    refine ⟨1023057290349584671002727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21825222194124472981391509 1023057290349584671002727)
    ·
      refine ⟨1534585935524377006504091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023057290349584671002727 1534585935524377006504091)
      ·
        refine ⟨2301878903286565509756137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534585935524377006504091 2301878903286565509756137)
        ·
          refine ⟨1726409177464924132317103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2301878903286565509756137 1726409177464924132317103)
          ·
            refine ⟨2589613766197386198475655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726409177464924132317103 2589613766197386198475655)
            ·
              refine ⟨3884420649296079297713483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589613766197386198475655 3884420649296079297713483)
              ·
                refine ⟨5826630973944118946570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884420649296079297713483 5826630973944118946570225)
                ·
                  refine ⟨4369973230458089209927669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5826630973944118946570225 4369973230458089209927669)
                  ·
                    refine ⟨409684990355445863430719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4369973230458089209927669 409684990355445863430719)
                    ·
                      rfl

theorem cell22_1196788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1196788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196788 prefixEnd_1196788 := by exact prefixLift 1196788
  have htrace : WordTrace (prefixWord ++ tailWord_1196788) baseStart_1196788 baseEnd_1196788 := by
    simpa [prefixWord, tailWord_1196788, baseEnd_1196788] using wordTrace_append hprefix tailTrace_1196788
  have hstable : (prefixWord ++ tailWord_1196788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196788).length < 2 ^ (prefixWord ++ tailWord_1196788).sum := by decide
  have hdescent : baseEnd_1196788 < baseStart_1196788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196797 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1196797 : Nat := 118140960795 + 1196797 * 2 ^ 59
def prefixEnd_1196797 : Nat := 4983230072969 + 3 ^ 40 * 1196797 * 2
def baseEnd_1196797 : Nat := 409688071239372839955691

theorem tailTrace_1196797 : CollatzResearch.WordTrace tailWord_1196797 prefixEnd_1196797 409688071239372839955691 := by
  unfold tailWord_1196797
  simp only [CollatzResearch.WordTrace]
  refine ⟨43650772645216340499860645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29100515096810893666573763 43650772645216340499860645)
  ·
    refine ⟨8184519870978063843723871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43650772645216340499860645 8184519870978063843723871)
    ·
      refine ⟨12276779806467095765585807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184519870978063843723871 12276779806467095765585807)
      ·
        refine ⟨18415169709700643648378711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276779806467095765585807 18415169709700643648378711)
        ·
          refine ⟨27622754564550965472568067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18415169709700643648378711 27622754564550965472568067)
          ·
            refine ⟨41434131846826448208852101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27622754564550965472568067 41434131846826448208852101)
            ·
              refine ⟨7768899721279959039159769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41434131846826448208852101 7768899721279959039159769)
              ·
                refine ⟨5826674790959969279369827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7768899721279959039159769 5826674790959969279369827)
                ·
                  refine ⟨8740012186439953919054741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826674790959969279369827 8740012186439953919054741)
                  ·
                    refine ⟨409688071239372839955691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8740012186439953919054741 409688071239372839955691)
                    ·
                      rfl

theorem cell22_1196797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1196797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196797 prefixEnd_1196797 := by exact prefixLift 1196797
  have htrace : WordTrace (prefixWord ++ tailWord_1196797) baseStart_1196797 baseEnd_1196797 := by
    simpa [prefixWord, tailWord_1196797, baseEnd_1196797] using wordTrace_append hprefix tailTrace_1196797
  have hstable : (prefixWord ++ tailWord_1196797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196797).length < 2 ^ (prefixWord ++ tailWord_1196797).sum := by decide
  have hdescent : baseEnd_1196797 < baseStart_1196797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196921 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_1196921 : Nat := 118140960795 + 1196921 * 2 ^ 59
def prefixEnd_1196921 : Nat := 4983230072969 + 3 ^ 40 * 1196921 * 2
def baseEnd_1196921 : Nat := 409730518973477849855311

theorem tailTrace_1196921 : CollatzResearch.WordTrace tailWord_1196921 prefixEnd_1196921 409730518973477849855311 := by
  unfold tailWord_1196921
  simp only [CollatzResearch.WordTrace]
  refine ⟨43655295296767109677374617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29103530197844739784916411 43655295296767109677374617)
  ·
    refine ⟨32741471472575332258030963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43655295296767109677374617 32741471472575332258030963)
    ·
      refine ⟨49112207208862998387046445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32741471472575332258030963 49112207208862998387046445)
      ·
        refine ⟨18417077703323624395142417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49112207208862998387046445 18417077703323624395142417)
        ·
          refine ⟨13812808277492718296356813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18417077703323624395142417 13812808277492718296356813)
          ·
            refine ⟨5179803104059769361133805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13812808277492718296356813 5179803104059769361133805)
            ·
              refine ⟨1942426164022413510425177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5179803104059769361133805 1942426164022413510425177)
              ·
                refine ⟨1456819623016810132818883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942426164022413510425177 1456819623016810132818883)
                ·
                  refine ⟨2185229434525215199228325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456819623016810132818883 2185229434525215199228325)
                  ·
                    refine ⟨409730518973477849855311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185229434525215199228325 409730518973477849855311)
                    ·
                      rfl

theorem cell22_1196921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_1196921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196921 prefixEnd_1196921 := by exact prefixLift 1196921
  have htrace : WordTrace (prefixWord ++ tailWord_1196921) baseStart_1196921 baseEnd_1196921 := by
    simpa [prefixWord, tailWord_1196921, baseEnd_1196921] using wordTrace_append hprefix tailTrace_1196921
  have hstable : (prefixWord ++ tailWord_1196921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196921).length < 2 ^ (prefixWord ++ tailWord_1196921).sum := by decide
  have hdescent : baseEnd_1196921 < baseStart_1196921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196981 : List Nat := [1, 3, 3, 2, 1, 1, 5, 6]
def baseStart_1196981 : Nat := 118140960795 + 1196981 * 2 ^ 59
def prefixEnd_1196981 : Nat := 4983230072969 + 3 ^ 40 * 1196981 * 2
def baseEnd_1196981 : Nat := 45527895355517521483903

theorem tailTrace_1196981 : CollatzResearch.WordTrace tailWord_1196981 prefixEnd_1196981 45527895355517521483903 := by
  unfold tailWord_1196981
  simp only [CollatzResearch.WordTrace]
  refine ⟨43657483676549739924558797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29104989117699826616372531 43657483676549739924558797)
  ·
    refine ⟨16371556378706152471709549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43657483676549739924558797 16371556378706152471709549)
    ·
      refine ⟨6139333642014807176891081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16371556378706152471709549 6139333642014807176891081)
      ·
        refine ⟨4604500231511105382668311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6139333642014807176891081 4604500231511105382668311)
        ·
          refine ⟨6906750347266658074002467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604500231511105382668311 6906750347266658074002467)
          ·
            refine ⟨10360125520899987111003701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906750347266658074002467 10360125520899987111003701)
            ·
              refine ⟨971261767584373791656597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10360125520899987111003701 971261767584373791656597)
              ·
                refine ⟨45527895355517521483903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 971261767584373791656597 45527895355517521483903)
                ·
                  rfl

theorem cell22_1196981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 6].length) (baseStart_1196981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1196981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1196981 prefixEnd_1196981 := by exact prefixLift 1196981
  have htrace : WordTrace (prefixWord ++ tailWord_1196981) baseStart_1196981 baseEnd_1196981 := by
    simpa [prefixWord, tailWord_1196981, baseEnd_1196981] using wordTrace_append hprefix tailTrace_1196981
  have hstable : (prefixWord ++ tailWord_1196981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196981).length < 2 ^ (prefixWord ++ tailWord_1196981).sum := by decide
  have hdescent : baseEnd_1196981 < baseStart_1196981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197009 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 7]
def baseStart_1197009 : Nat := 118140960795 + 1197009 * 2 ^ 59
def prefixEnd_1197009 : Nat := 4983230072969 + 3 ^ 40 * 1197009 * 2
def baseEnd_1197009 : Nat := 136586881057291651218347

theorem tailTrace_1197009 : CollatzResearch.WordTrace tailWord_1197009 prefixEnd_1197009 136586881057291651218347 := by
  unfold tailWord_1197009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43658504920448300706578081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29105669946965533804385387 43658504920448300706578081)
  ·
    refine ⟨32743878690336225529933561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43658504920448300706578081 32743878690336225529933561)
    ·
      refine ⟨24557909017752169147450171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32743878690336225529933561 24557909017752169147450171)
      ·
        refine ⟨36836863526628253721175257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24557909017752169147450171 36836863526628253721175257)
        ·
          refine ⟨27627647644971190290881443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36836863526628253721175257 27627647644971190290881443)
          ·
            refine ⟨41441471467456785436322165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27627647644971190290881443 41441471467456785436322165)
            ·
              refine ⟨3885137950074073634655203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41441471467456785436322165 3885137950074073634655203)
              ·
                refine ⟨5827706925111110451982805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885137950074073634655203 5827706925111110451982805)
                ·
                  refine ⟨136586881057291651218347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5827706925111110451982805 136586881057291651218347)
                  ·
                    rfl

theorem cell22_1197009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_1197009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197009 prefixEnd_1197009 := by exact prefixLift 1197009
  have htrace : WordTrace (prefixWord ++ tailWord_1197009) baseStart_1197009 baseEnd_1197009 := by
    simpa [prefixWord, tailWord_1197009, baseEnd_1197009] using wordTrace_append hprefix tailTrace_1197009
  have hstable : (prefixWord ++ tailWord_1197009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197009).length < 2 ^ (prefixWord ++ tailWord_1197009).sum := by decide
  have hdescent : baseEnd_1197009 < baseStart_1197009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197090 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1197090 : Nat := 118140960795 + 1197090 * 2 ^ 59
def prefixEnd_1197090 : Nat := 4983230072969 + 3 ^ 40 * 1197090 * 2
def baseEnd_1197090 : Nat := 409788371127217742379793

theorem tailTrace_1197090 : CollatzResearch.WordTrace tailWord_1197090 prefixEnd_1197090 409788371127217742379793 := by
  unfold tailWord_1197090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915364808288712885069181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29107639488769901026851149 10915364808288712885069181)
  ·
    refine ⟨4093261803108267331900943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10915364808288712885069181 4093261803108267331900943)
    ·
      refine ⟨6139892704662400997851415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093261803108267331900943 6139892704662400997851415)
      ·
        refine ⟨9209839056993601496777123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139892704662400997851415 9209839056993601496777123)
        ·
          refine ⟨13814758585490402245165685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9209839056993601496777123 13814758585490402245165685)
          ·
            refine ⟨1295133617389725210484283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13814758585490402245165685 1295133617389725210484283)
            ·
              refine ⟨1942700426084587815726425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295133617389725210484283 1942700426084587815726425)
              ·
                refine ⟨1457025319563440861794819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942700426084587815726425 1457025319563440861794819)
                ·
                  refine ⟨2185537979345161292692229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457025319563440861794819 2185537979345161292692229)
                  ·
                    refine ⟨409788371127217742379793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2185537979345161292692229 409788371127217742379793)
                    ·
                      rfl

theorem cell22_1197090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1197090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197090 prefixEnd_1197090 := by exact prefixLift 1197090
  have htrace : WordTrace (prefixWord ++ tailWord_1197090) baseStart_1197090 baseEnd_1197090 := by
    simpa [prefixWord, tailWord_1197090, baseEnd_1197090] using wordTrace_append hprefix tailTrace_1197090
  have hstable : (prefixWord ++ tailWord_1197090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197090).length < 2 ^ (prefixWord ++ tailWord_1197090).sum := by decide
  have hdescent : baseEnd_1197090 < baseStart_1197090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197099 : List Nat := [1, 1, 1, 1, 2, 1, 5, 10]
def baseStart_1197099 : Nat := 118140960795 + 1197099 * 2 ^ 59
def prefixEnd_1197099 : Nat := 4983230072969 + 3 ^ 40 * 1197099 * 2
def baseEnd_1197099 : Nat := 45532383556793857656085

theorem tailTrace_1197099 : CollatzResearch.WordTrace tailWord_1197099 prefixEnd_1197099 45532383556793857656085 := by
  unfold tailWord_1197099
  simp only [CollatzResearch.WordTrace]
  refine ⟨43661787490122246077354351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29107858326748164051569567 43661787490122246077354351)
  ·
    refine ⟨65492681235183369116031527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43661787490122246077354351 65492681235183369116031527)
    ·
      refine ⟨98239021852775053674047291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65492681235183369116031527 98239021852775053674047291)
      ·
        refine ⟨147358532779162580511070937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98239021852775053674047291 147358532779162580511070937)
        ·
          refine ⟨110518899584371935383303203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147358532779162580511070937 110518899584371935383303203)
          ·
            refine ⟨165778349376557903074954805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110518899584371935383303203 165778349376557903074954805)
            ·
              refine ⟨15541720254052303413277013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165778349376557903074954805 15541720254052303413277013)
              ·
                refine ⟨45532383556793857656085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15541720254052303413277013 45532383556793857656085)
                ·
                  rfl

theorem cell22_1197099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_1197099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197099 prefixEnd_1197099 := by exact prefixLift 1197099
  have htrace : WordTrace (prefixWord ++ tailWord_1197099) baseStart_1197099 baseEnd_1197099 := by
    simpa [prefixWord, tailWord_1197099, baseEnd_1197099] using wordTrace_append hprefix tailTrace_1197099
  have hstable : (prefixWord ++ tailWord_1197099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197099).length < 2 ^ (prefixWord ++ tailWord_1197099).sum := by decide
  have hdescent : baseEnd_1197099 < baseStart_1197099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197133 : List Nat := [1, 6, 1, 1, 1, 2, 3, 7]
def baseStart_1197133 : Nat := 118140960795 + 1197133 * 2 ^ 59
def prefixEnd_1197133 : Nat := 4983230072969 + 3 ^ 40 * 1197133 * 2
def baseEnd_1197133 : Nat := 45533676767331107061629

theorem tailTrace_1197133 : CollatzResearch.WordTrace tailWord_1197133 prefixEnd_1197133 45533676767331107061629 := by
  unfold tailWord_1197133
  simp only [CollatzResearch.WordTrace]
  refine ⟨43663027571999069884092053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29108685047999379922728035 43663027571999069884092053)
  ·
    refine ⟨2046704417437456400816815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43663027571999069884092053 2046704417437456400816815)
    ·
      refine ⟨3070056626156184601225223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046704417437456400816815 3070056626156184601225223)
      ·
        refine ⟨4605084939234276901837835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070056626156184601225223 4605084939234276901837835)
        ·
          refine ⟨6907627408851415352756753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605084939234276901837835 6907627408851415352756753)
          ·
            refine ⟨5180720556638561514567565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6907627408851415352756753 5180720556638561514567565)
            ·
              refine ⟨1942770208739460567962837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5180720556638561514567565 1942770208739460567962837)
              ·
                refine ⟨45533676767331107061629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1942770208739460567962837 45533676767331107061629)
                ·
                  rfl

theorem cell22_1197133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 7].length) (baseStart_1197133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197133 prefixEnd_1197133 := by exact prefixLift 1197133
  have htrace : WordTrace (prefixWord ++ tailWord_1197133) baseStart_1197133 baseEnd_1197133 := by
    simpa [prefixWord, tailWord_1197133, baseEnd_1197133] using wordTrace_append hprefix tailTrace_1197133
  have hstable : (prefixWord ++ tailWord_1197133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197133).length < 2 ^ (prefixWord ++ tailWord_1197133).sum := by decide
  have hdescent : baseEnd_1197133 < baseStart_1197133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197176 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1197176 : Nat := 118140960795 + 1197176 * 2 ^ 59
def prefixEnd_1197176 : Nat := 4983230072969 + 3 ^ 40 * 1197176 * 2
def baseEnd_1197176 : Nat := 409817810684742184729529

theorem tailTrace_1197176 : CollatzResearch.WordTrace tailWord_1197176 prefixEnd_1197176 409817810684742184729529 := by
  unfold tailWord_1197176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832297955421644113953691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29109730607228858818604921 21832297955421644113953691)
  ·
    refine ⟨32748446933132466170930537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832297955421644113953691 32748446933132466170930537)
    ·
      refine ⟨24561335199849349628197903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32748446933132466170930537 24561335199849349628197903)
      ·
        refine ⟨36842002799774024442296855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24561335199849349628197903 36842002799774024442296855)
        ·
          refine ⟨55263004199661036663445283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36842002799774024442296855 55263004199661036663445283)
          ·
            refine ⟨82894506299491554995167925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55263004199661036663445283 82894506299491554995167925)
            ·
              refine ⟨7771359965577333280796993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82894506299491554995167925 7771359965577333280796993)
              ·
                refine ⟨5828519974182999960597745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7771359965577333280796993 5828519974182999960597745)
                ·
                  refine ⟨4371389980637249970448309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5828519974182999960597745 4371389980637249970448309)
                  ·
                    refine ⟨409817810684742184729529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4371389980637249970448309 409817810684742184729529)
                    ·
                      rfl

theorem cell22_1197176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1197176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197176 prefixEnd_1197176 := by exact prefixLift 1197176
  have htrace : WordTrace (prefixWord ++ tailWord_1197176) baseStart_1197176 baseEnd_1197176 := by
    simpa [prefixWord, tailWord_1197176, baseEnd_1197176] using wordTrace_append hprefix tailTrace_1197176
  have hstable : (prefixWord ++ tailWord_1197176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197176).length < 2 ^ (prefixWord ++ tailWord_1197176).sum := by decide
  have hdescent : baseEnd_1197176 < baseStart_1197176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197377 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1197377 : Nat := 118140960795 + 1197377 * 2 ^ 59
def prefixEnd_1197377 : Nat := 4983230072969 + 3 ^ 40 * 1197377 * 2
def baseEnd_1197377 : Nat := 409886617092444660453913

theorem tailTrace_1197377 : CollatzResearch.WordTrace tailWord_1197377 prefixEnd_1197377 409886617092444660453913 := by
  unfold tailWord_1197377
  simp only [CollatzResearch.WordTrace]
  refine ⟨43671926983115099555974385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29114617988743399703982923 43671926983115099555974385)
  ·
    refine ⟨32753945237336324666980789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43671926983115099555974385 32753945237336324666980789)
    ·
      refine ⟨3070682366000280437529449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32753945237336324666980789 3070682366000280437529449)
      ·
        refine ⟨2303011774500210328147087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070682366000280437529449 2303011774500210328147087)
        ·
          refine ⟨3454517661750315492220631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303011774500210328147087 3454517661750315492220631)
          ·
            refine ⟨5181776492625473238330947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454517661750315492220631 5181776492625473238330947)
            ·
              refine ⟨7772664738938209857496421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181776492625473238330947 7772664738938209857496421)
              ·
                refine ⟨1457374638550914348280579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7772664738938209857496421 1457374638550914348280579)
                ·
                  refine ⟨2186061957826371522420869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457374638550914348280579 2186061957826371522420869)
                  ·
                    refine ⟨409886617092444660453913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186061957826371522420869 409886617092444660453913)
                    ·
                      rfl

theorem cell22_1197377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1197377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197377 prefixEnd_1197377 := by exact prefixLift 1197377
  have htrace : WordTrace (prefixWord ++ tailWord_1197377) baseStart_1197377 baseEnd_1197377 := by
    simpa [prefixWord, tailWord_1197377, baseEnd_1197377] using wordTrace_append hprefix tailTrace_1197377
  have hstable : (prefixWord ++ tailWord_1197377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197377).length < 2 ^ (prefixWord ++ tailWord_1197377).sum := by decide
  have hdescent : baseEnd_1197377 < baseStart_1197377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197390 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1197390 : Nat := 118140960795 + 1197390 * 2 ^ 59
def prefixEnd_1197390 : Nat := 4983230072969 + 3 ^ 40 * 1197390 * 2
def baseEnd_1197390 : Nat := 409891067258116959878873

theorem tailTrace_1197390 : CollatzResearch.WordTrace tailWord_1197390 prefixEnd_1197390 409891067258116959878873 := by
  unfold tailWord_1197390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459050141508500347024703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29114934088045335184131749 5459050141508500347024703)
  ·
    refine ⟨8188575212262750520537055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459050141508500347024703 8188575212262750520537055)
    ·
      refine ⟨12282862818394125780805583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8188575212262750520537055 12282862818394125780805583)
      ·
        refine ⟨18424294227591188671208375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12282862818394125780805583 18424294227591188671208375)
        ·
          refine ⟨27636441341386783006812563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18424294227591188671208375 27636441341386783006812563)
          ·
            refine ⟨41454662012080174510218845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27636441341386783006812563 41454662012080174510218845)
            ·
              refine ⟨15545498254530065441332067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41454662012080174510218845 15545498254530065441332067)
              ·
                refine ⟨23318247381795098161998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15545498254530065441332067 23318247381795098161998101)
                ·
                  refine ⟨1093042846021645226343661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23318247381795098161998101 1093042846021645226343661)
                  ·
                    refine ⟨409891067258116959878873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093042846021645226343661 409891067258116959878873)
                    ·
                      rfl

theorem cell22_1197390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1197390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197390 prefixEnd_1197390 := by exact prefixLift 1197390
  have htrace : WordTrace (prefixWord ++ tailWord_1197390) baseStart_1197390 baseEnd_1197390 := by
    simpa [prefixWord, tailWord_1197390, baseEnd_1197390] using wordTrace_append hprefix tailTrace_1197390
  have hstable : (prefixWord ++ tailWord_1197390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197390).length < 2 ^ (prefixWord ++ tailWord_1197390).sum := by decide
  have hdescent : baseEnd_1197390 < baseStart_1197390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197420 : List Nat := [2, 2, 1, 1, 5, 2, 2, 7]
def baseStart_1197420 : Nat := 118140960795 + 1197420 * 2 ^ 59
def prefixEnd_1197420 : Nat := 4983230072969 + 3 ^ 40 * 1197420 * 2
def baseEnd_1197420 : Nat := 45544592985689653514309

theorem tailTrace_1197420 : CollatzResearch.WordTrace tailWord_1197420 prefixEnd_1197420 45544592985689653514309 := by
  unfold tailWord_1197420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21836747660979658949894857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29115663547972878599859809 21836747660979658949894857)
  ·
    refine ⟨16377560745734744212421143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21836747660979658949894857 16377560745734744212421143)
    ·
      refine ⟨24566341118602116318631715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16377560745734744212421143 24566341118602116318631715)
      ·
        refine ⟨36849511677903174477947573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24566341118602116318631715 36849511677903174477947573)
        ·
          refine ⟨3454641719803422607307585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36849511677903174477947573 3454641719803422607307585)
          ·
            refine ⟨2590981289852566955480689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454641719803422607307585 2590981289852566955480689)
            ·
              refine ⟨1943235967389425216610517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590981289852566955480689 1943235967389425216610517)
              ·
                refine ⟨45544592985689653514309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1943235967389425216610517 45544592985689653514309)
                ·
                  rfl

theorem cell22_1197420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_1197420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197420 prefixEnd_1197420 := by exact prefixLift 1197420
  have htrace : WordTrace (prefixWord ++ tailWord_1197420) baseStart_1197420 baseEnd_1197420 := by
    simpa [prefixWord, tailWord_1197420, baseEnd_1197420] using wordTrace_append hprefix tailTrace_1197420
  have hstable : (prefixWord ++ tailWord_1197420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197420).length < 2 ^ (prefixWord ++ tailWord_1197420).sum := by decide
  have hdescent : baseEnd_1197420 < baseStart_1197420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197435 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 5, 3]
def baseStart_1197435 : Nat := 118140960795 + 1197435 * 2 ^ 59
def prefixEnd_1197435 : Nat := 4983230072969 + 3 ^ 40 * 1197435 * 2
def baseEnd_1197435 : Nat := 409906471677751842503735

theorem tailTrace_1197435 : CollatzResearch.WordTrace tailWord_1197435 prefixEnd_1197435 409906471677751842503735 := by
  unfold tailWord_1197435
  simp only [CollatzResearch.WordTrace]
  refine ⟨43674042416904975461585759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29116028277936650307723839 43674042416904975461585759)
  ·
    refine ⟨65511063625357463192378639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43674042416904975461585759 65511063625357463192378639)
    ·
      refine ⟨98266595438036194788567959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65511063625357463192378639 98266595438036194788567959)
      ·
        refine ⟨147399893157054292182851939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98266595438036194788567959 147399893157054292182851939)
        ·
          refine ⟨221099839735581438274277909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147399893157054292182851939 221099839735581438274277909)
          ·
            refine ⟨10364054987605379919106777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221099839735581438274277909 10364054987605379919106777)
            ·
              refine ⟨7773041240704034939330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10364054987605379919106777 7773041240704034939330083)
              ·
                refine ⟨11659561861056052408995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7773041240704034939330083 11659561861056052408995125)
                ·
                  refine ⟨1093083924474004913343293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11659561861056052408995125 1093083924474004913343293)
                  ·
                    refine ⟨409906471677751842503735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093083924474004913343293 409906471677751842503735)
                    ·
                      rfl

theorem cell22_1197435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 3].length) (baseStart_1197435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197435 prefixEnd_1197435 := by exact prefixLift 1197435
  have htrace : WordTrace (prefixWord ++ tailWord_1197435) baseStart_1197435 baseEnd_1197435 := by
    simpa [prefixWord, tailWord_1197435, baseEnd_1197435] using wordTrace_append hprefix tailTrace_1197435
  have hstable : (prefixWord ++ tailWord_1197435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197435).length < 2 ^ (prefixWord ++ tailWord_1197435).sum := by decide
  have hdescent : baseEnd_1197435 < baseStart_1197435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197465 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 5]
def baseStart_1197465 : Nat := 118140960795 + 1197465 * 2 ^ 59
def prefixEnd_1197465 : Nat := 4983230072969 + 3 ^ 40 * 1197465 * 2
def baseEnd_1197465 : Nat := 136638913763613921417881

theorem tailTrace_1197465 : CollatzResearch.WordTrace tailWord_1197465 prefixEnd_1197465 136638913763613921417881 := by
  unfold tailWord_1197465
  simp only [CollatzResearch.WordTrace]
  refine ⟨43675136606796290585177849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29116757737864193723451899 43675136606796290585177849)
  ·
    refine ⟨32756352455097217938883387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43675136606796290585177849 32756352455097217938883387)
    ·
      refine ⟨49134528682645826908325081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32756352455097217938883387 49134528682645826908325081)
      ·
        refine ⟨36850896511984370181243811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49134528682645826908325081 36850896511984370181243811)
        ·
          refine ⟨55276344767976555271865717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36850896511984370181243811 55276344767976555271865717)
          ·
            refine ⟨5182157321997802056737411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55276344767976555271865717 5182157321997802056737411)
            ·
              refine ⟨7773235982996703085106117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5182157321997802056737411 7773235982996703085106117)
              ·
                refine ⟨1457481746811881828457397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7773235982996703085106117 1457481746811881828457397)
                ·
                  refine ⟨136638913763613921417881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457481746811881828457397 136638913763613921417881)
                  ·
                    rfl

theorem cell22_1197465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_1197465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197465 prefixEnd_1197465 := by exact prefixLift 1197465
  have htrace : WordTrace (prefixWord ++ tailWord_1197465) baseStart_1197465 baseEnd_1197465 := by
    simpa [prefixWord, tailWord_1197465, baseEnd_1197465] using wordTrace_append hprefix tailTrace_1197465
  have hstable : (prefixWord ++ tailWord_1197465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197465).length < 2 ^ (prefixWord ++ tailWord_1197465).sum := by decide
  have hdescent : baseEnd_1197465 < baseStart_1197465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197495 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_1197495 : Nat := 118140960795 + 1197495 * 2 ^ 59
def prefixEnd_1197495 : Nat := 4983230072969 + 3 ^ 40 * 1197495 * 2
def baseEnd_1197495 : Nat := 409927010903931686003551

theorem tailTrace_1197495 : CollatzResearch.WordTrace tailWord_1197495 prefixEnd_1197495 409927010903931686003551 := by
  unfold tailWord_1197495
  simp only [CollatzResearch.WordTrace]
  refine ⟨43676230796687605708769939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29117487197791737139179959 43676230796687605708769939)
  ·
    refine ⟨65514346195031408563154909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43676230796687605708769939 65514346195031408563154909)
    ·
      refine ⟨24567879823136778211183091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65514346195031408563154909 24567879823136778211183091)
      ·
        refine ⟨36851819734705167316774637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24567879823136778211183091 36851819734705167316774637)
        ·
          refine ⟨13819432400514437743790489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36851819734705167316774637 13819432400514437743790489)
          ·
            refine ⟨10364574300385828307842867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13819432400514437743790489 10364574300385828307842867)
            ·
              refine ⟨15546861450578742461764301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364574300385828307842867 15546861450578742461764301)
              ·
                refine ⟨5830073043967028423161613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15546861450578742461764301 5830073043967028423161613)
                ·
                  refine ⟨2186277391487635658685605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5830073043967028423161613 2186277391487635658685605)
                  ·
                    refine ⟨409927010903931686003551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186277391487635658685605 409927010903931686003551)
                    ·
                      rfl

theorem cell22_1197495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_1197495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197495 prefixEnd_1197495 := by exact prefixLift 1197495
  have htrace : WordTrace (prefixWord ++ tailWord_1197495) baseStart_1197495 baseEnd_1197495 := by
    simpa [prefixWord, tailWord_1197495, baseEnd_1197495] using wordTrace_append hprefix tailTrace_1197495
  have hstable : (prefixWord ++ tailWord_1197495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197495).length < 2 ^ (prefixWord ++ tailWord_1197495).sum := by decide
  have hdescent : baseEnd_1197495 < baseStart_1197495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197512 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1197512 : Nat := 118140960795 + 1197512 * 2 ^ 59
def prefixEnd_1197512 : Nat := 4983230072969 + 3 ^ 40 * 1197512 * 2
def baseEnd_1197512 : Nat := 409932830351349308328499

theorem tailTrace_1197512 : CollatzResearch.WordTrace tailWord_1197512 prefixEnd_1197512 409932830351349308328499 := by
  unfold tailWord_1197512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21838425418813008806069395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29117900558417345074759193 21838425418813008806069395)
  ·
    refine ⟨32757638128219513209104093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21838425418813008806069395 32757638128219513209104093)
    ·
      refine ⟨12284114298082317453414035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32757638128219513209104093 12284114298082317453414035)
      ·
        refine ⟨18426171447123476180121053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284114298082317453414035 18426171447123476180121053)
        ·
          refine ⟨6909814292671303567545395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18426171447123476180121053 6909814292671303567545395)
          ·
            refine ⟨10364721439006955351318093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909814292671303567545395 10364721439006955351318093)
            ·
              refine ⟨3886770539627608256744285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10364721439006955351318093 3886770539627608256744285)
              ·
                refine ⟨1457538952360353096279107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886770539627608256744285 1457538952360353096279107)
                ·
                  refine ⟨2186308428540529644418661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457538952360353096279107 2186308428540529644418661)
                  ·
                    refine ⟨409932830351349308328499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186308428540529644418661 409932830351349308328499)
                    ·
                      rfl

theorem cell22_1197512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1197512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197512 prefixEnd_1197512 := by exact prefixLift 1197512
  have htrace : WordTrace (prefixWord ++ tailWord_1197512) baseStart_1197512 baseEnd_1197512 := by
    simpa [prefixWord, tailWord_1197512, baseEnd_1197512] using wordTrace_append hprefix tailTrace_1197512
  have hstable : (prefixWord ++ tailWord_1197512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197512).length < 2 ^ (prefixWord ++ tailWord_1197512).sum := by decide
  have hdescent : baseEnd_1197512 < baseStart_1197512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197585 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1197585 : Nat := 118140960795 + 1197585 * 2 ^ 59
def prefixEnd_1197585 : Nat := 4983230072969 + 3 ^ 40 * 1197585 * 2
def baseEnd_1197585 : Nat := 409957819743201451253275

theorem tailTrace_1197585 : CollatzResearch.WordTrace tailWord_1197585 prefixEnd_1197585 409957819743201451253275 := by
  unfold tailWord_1197585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43679513366361551079546209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29119675577574367386364139 43679513366361551079546209)
  ·
    refine ⟨32759635024771163309659657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43679513366361551079546209 32759635024771163309659657)
    ·
      refine ⟨24569726268578372482244743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32759635024771163309659657 24569726268578372482244743)
      ·
        refine ⟨36854589402867558723367115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24569726268578372482244743 36854589402867558723367115)
        ·
          refine ⟨55281884104301338085050673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36854589402867558723367115 55281884104301338085050673)
          ·
            refine ⟨41461413078226003563788005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55281884104301338085050673 41461413078226003563788005)
            ·
              refine ⟨7774014952167375668210251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41461413078226003563788005 7774014952167375668210251)
              ·
                refine ⟨11661022428251063502315377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7774014952167375668210251 11661022428251063502315377)
                ·
                  refine ⟨8745766821188297626736533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11661022428251063502315377 8745766821188297626736533)
                  ·
                    refine ⟨409957819743201451253275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8745766821188297626736533 409957819743201451253275)
                    ·
                      rfl

theorem cell22_1197585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1197585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197585 prefixEnd_1197585 := by exact prefixLift 1197585
  have htrace : WordTrace (prefixWord ++ tailWord_1197585) baseStart_1197585 baseEnd_1197585 := by
    simpa [prefixWord, tailWord_1197585, baseEnd_1197585] using wordTrace_append hprefix tailTrace_1197585
  have hstable : (prefixWord ++ tailWord_1197585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197585).length < 2 ^ (prefixWord ++ tailWord_1197585).sum := by decide
  have hdescent : baseEnd_1197585 < baseStart_1197585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1197692 : Nat := 118140960795 + 1197692 * 2 ^ 59
def prefixEnd_1197692 : Nat := 4983230072969 + 3 ^ 40 * 1197692 * 2
def baseEnd_1197692 : Nat := 409994448029888838827947

theorem tailTrace_1197692 : CollatzResearch.WordTrace tailWord_1197692 prefixEnd_1197692 409994448029888838827947 := by
  unfold tailWord_1197692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21841707988486954176845665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29122277317982605569127553 21841707988486954176845665)
  ·
    refine ⟨16381280991365215632634249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21841707988486954176845665 16381280991365215632634249)
    ·
      refine ⟨12285960743523911724475687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16381280991365215632634249 12285960743523911724475687)
      ·
        refine ⟨18428941115285867586713531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12285960743523911724475687 18428941115285867586713531)
        ·
          refine ⟨27643411672928801380070297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18428941115285867586713531 27643411672928801380070297)
          ·
            refine ⟨20732558754696601035052723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27643411672928801380070297 20732558754696601035052723)
            ·
              refine ⟨31098838132044901552579085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20732558754696601035052723 31098838132044901552579085)
              ·
                refine ⟨11662064299516838082217157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31098838132044901552579085 11662064299516838082217157)
                ·
                  refine ⟨2186637056159407140415717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11662064299516838082217157 2186637056159407140415717)
                  ·
                    refine ⟨409994448029888838827947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2186637056159407140415717 409994448029888838827947)
                    ·
                      rfl

theorem cell22_1197692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1197692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197692 prefixEnd_1197692 := by exact prefixLift 1197692
  have htrace : WordTrace (prefixWord ++ tailWord_1197692) baseStart_1197692 baseEnd_1197692 := by
    simpa [prefixWord, tailWord_1197692, baseEnd_1197692] using wordTrace_append hprefix tailTrace_1197692
  have hstable : (prefixWord ++ tailWord_1197692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197692).length < 2 ^ (prefixWord ++ tailWord_1197692).sum := by decide
  have hdescent : baseEnd_1197692 < baseStart_1197692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197724 : List Nat := [2, 2, 3, 2, 3, 1, 1, 8]
def baseStart_1197724 : Nat := 118140960795 + 1197724 * 2 ^ 59
def prefixEnd_1197724 : Nat := 4983230072969 + 3 ^ 40 * 1197724 * 2
def baseEnd_1197724 : Nat := 45556155809316824669761

theorem tailTrace_1197724 : CollatzResearch.WordTrace tailWord_1197724 prefixEnd_1197724 45556155809316824669761 := by
  unfold tailWord_1197724
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842291556428988909428113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29123055408571985212570817 21842291556428988909428113)
  ·
    refine ⟨16381718667321741682071085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21842291556428988909428113 16381718667321741682071085)
    ·
      refine ⟨6143144500245653130776657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16381718667321741682071085 6143144500245653130776657)
      ·
        refine ⟨4607358375184239848082493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6143144500245653130776657 4607358375184239848082493)
        ·
          refine ⟨1727759390694089943030935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4607358375184239848082493 1727759390694089943030935)
          ·
            refine ⟨2591639086041134914546403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727759390694089943030935 2591639086041134914546403)
            ·
              refine ⟨3887458629061702371819605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591639086041134914546403 3887458629061702371819605)
              ·
                refine ⟨45556155809316824669761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3887458629061702371819605 45556155809316824669761)
                ·
                  rfl

theorem cell22_1197724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_1197724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197724 prefixEnd_1197724 := by exact prefixLift 1197724
  have htrace : WordTrace (prefixWord ++ tailWord_1197724) baseStart_1197724 baseEnd_1197724 := by
    simpa [prefixWord, tailWord_1197724, baseEnd_1197724] using wordTrace_append hprefix tailTrace_1197724
  have hstable : (prefixWord ++ tailWord_1197724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197724).length < 2 ^ (prefixWord ++ tailWord_1197724).sum := by decide
  have hdescent : baseEnd_1197724 < baseStart_1197724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197730 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1197730 : Nat := 118140960795 + 1197730 * 2 ^ 59
def prefixEnd_1197730 : Nat := 4983230072969 + 3 ^ 40 * 1197730 * 2
def baseEnd_1197730 : Nat := 136669152068823135459277

theorem tailTrace_1197730 : CollatzResearch.WordTrace tailWord_1197730 prefixEnd_1197730 136669152068823135459277 := by
  unfold tailWord_1197730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921200487709060210893661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29123201300557493895716429 10921200487709060210893661)
  ·
    refine ⟨4095450182890897579085123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10921200487709060210893661 4095450182890897579085123)
    ·
      refine ⟨6143175274336346368627685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4095450182890897579085123 6143175274336346368627685)
      ·
        refine ⟨1151845363938064944117691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6143175274336346368627685 1151845363938064944117691)
        ·
          refine ⟨1727768045907097416176537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151845363938064944117691 1727768045907097416176537)
          ·
            refine ⟨1295826034430323062132403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727768045907097416176537 1295826034430323062132403)
            ·
              refine ⟨1943739051645484593198605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295826034430323062132403 1943739051645484593198605)
              ·
                refine ⟨728902144367056722449477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1943739051645484593198605 728902144367056722449477)
                ·
                  refine ⟨136669152068823135459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728902144367056722449477 136669152068823135459277)
                  ·
                    rfl

theorem cell22_1197730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1197730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197730 prefixEnd_1197730 := by exact prefixLift 1197730
  have htrace : WordTrace (prefixWord ++ tailWord_1197730) baseStart_1197730 baseEnd_1197730 := by
    simpa [prefixWord, tailWord_1197730, baseEnd_1197730] using wordTrace_append hprefix tailTrace_1197730
  have hstable : (prefixWord ++ tailWord_1197730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197730).length < 2 ^ (prefixWord ++ tailWord_1197730).sum := by decide
  have hdescent : baseEnd_1197730 < baseStart_1197730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197756 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1197756 : Nat := 118140960795 + 1197756 * 2 ^ 59
def prefixEnd_1197756 : Nat := 4983230072969 + 3 ^ 40 * 1197756 * 2
def baseEnd_1197756 : Nat := 410016356537814005227751

theorem tailTrace_1197756 : CollatzResearch.WordTrace tailWord_1197756 prefixEnd_1197756 410016356537814005227751 := by
  unfold tailWord_1197756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842875124371023642010561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29123833499161364856014081 21842875124371023642010561)
  ·
    refine ⟨16382156343278267731507921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21842875124371023642010561 16382156343278267731507921)
    ·
      refine ⟨12286617257458700798630941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16382156343278267731507921 12286617257458700798630941)
      ·
        refine ⟨4607481471547012799486603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12286617257458700798630941 4607481471547012799486603)
        ·
          refine ⟨6911222207320519199229905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607481471547012799486603 6911222207320519199229905)
          ·
            refine ⟨5183416655490389399422429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6911222207320519199229905 5183416655490389399422429)
            ·
              refine ⟨1943781245808896024783411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5183416655490389399422429 1943781245808896024783411)
              ·
                refine ⟨2915671868713344037175117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943781245808896024783411 2915671868713344037175117)
                ·
                  refine ⟨1093376950767504013940669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2915671868713344037175117 1093376950767504013940669)
                  ·
                    refine ⟨410016356537814005227751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093376950767504013940669 410016356537814005227751)
                    ·
                      rfl

theorem cell22_1197756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1197756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197756 prefixEnd_1197756 := by exact prefixLift 1197756
  have htrace : WordTrace (prefixWord ++ tailWord_1197756) baseStart_1197756 baseEnd_1197756 := by
    simpa [prefixWord, tailWord_1197756, baseEnd_1197756] using wordTrace_append hprefix tailTrace_1197756
  have hstable : (prefixWord ++ tailWord_1197756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197756).length < 2 ^ (prefixWord ++ tailWord_1197756).sum := by decide
  have hdescent : baseEnd_1197756 < baseStart_1197756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197762 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1197762 : Nat := 118140960795 + 1197762 * 2 ^ 59
def prefixEnd_1197762 : Nat := 4983230072969 + 3 ^ 40 * 1197762 * 2
def baseEnd_1197762 : Nat := 410018410460431989577733

theorem tailTrace_1197762 : CollatzResearch.WordTrace tailWord_1197762 prefixEnd_1197762 410018410460431989577733 := by
  unfold tailWord_1197762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921492271680077577184885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29123979391146873539159693 10921492271680077577184885)
  ·
    refine ⟨1023889900470007272861083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10921492271680077577184885 1023889900470007272861083)
    ·
      refine ⟨1535834850705010909291625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023889900470007272861083 1535834850705010909291625)
      ·
        refine ⟨1151876138028758181968719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535834850705010909291625 1151876138028758181968719)
        ·
          refine ⟨1727814207043137272953079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151876138028758181968719 1727814207043137272953079)
          ·
            refine ⟨2591721310564705909429619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727814207043137272953079 2591721310564705909429619)
            ·
              refine ⟨3887581965847058864144429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591721310564705909429619 3887581965847058864144429)
              ·
                refine ⟨1457843237192647074054161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3887581965847058864144429 1457843237192647074054161)
                ·
                  refine ⟨1093382427894485305540621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457843237192647074054161 1093382427894485305540621)
                  ·
                    refine ⟨410018410460431989577733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093382427894485305540621 410018410460431989577733)
                    ·
                      rfl

theorem cell22_1197762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1197762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197762 prefixEnd_1197762 := by exact prefixLift 1197762
  have htrace : WordTrace (prefixWord ++ tailWord_1197762) baseStart_1197762 baseEnd_1197762 := by
    simpa [prefixWord, tailWord_1197762, baseEnd_1197762] using wordTrace_append hprefix tailTrace_1197762
  have hstable : (prefixWord ++ tailWord_1197762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197762).length < 2 ^ (prefixWord ++ tailWord_1197762).sum := by decide
  have hdescent : baseEnd_1197762 < baseStart_1197762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197767 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1197767 : Nat := 118140960795 + 1197767 * 2 ^ 59
def prefixEnd_1197767 : Nat := 4983230072969 + 3 ^ 40 * 1197767 * 2
def baseEnd_1197767 : Nat := 410020122062613643202717

theorem tailTrace_1197767 : CollatzResearch.WordTrace tailWord_1197767 prefixEnd_1197767 410020122062613643202717 := by
  unfold tailWord_1197767
  simp only [CollatzResearch.WordTrace]
  refine ⟨43686151451702196162671555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29124100967801464108447703 43686151451702196162671555)
  ·
    refine ⟨65529227177553294244007333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43686151451702196162671555 65529227177553294244007333)
    ·
      refine ⟨12286730095791242670751375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65529227177553294244007333 12286730095791242670751375)
      ·
        refine ⟨18430095143686864006127063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286730095791242670751375 18430095143686864006127063)
        ·
          refine ⟨27645142715530296009190595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18430095143686864006127063 27645142715530296009190595)
          ·
            refine ⟨41467714073295444013785893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27645142715530296009190595 41467714073295444013785893)
            ·
              refine ⟨7775196388742895752584855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41467714073295444013785893 7775196388742895752584855)
              ·
                refine ⟨11662794583114343628877283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775196388742895752584855 11662794583114343628877283)
                ·
                  refine ⟨17494191874671515443315925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11662794583114343628877283 17494191874671515443315925)
                  ·
                    refine ⟨410020122062613643202717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17494191874671515443315925 410020122062613643202717)
                    ·
                      rfl

theorem cell22_1197767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1197767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197767 prefixEnd_1197767 := by exact prefixLift 1197767
  have htrace : WordTrace (prefixWord ++ tailWord_1197767) baseStart_1197767 baseEnd_1197767 := by
    simpa [prefixWord, tailWord_1197767, baseEnd_1197767] using wordTrace_append hprefix tailTrace_1197767
  have hstable : (prefixWord ++ tailWord_1197767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197767).length < 2 ^ (prefixWord ++ tailWord_1197767).sum := by decide
  have hdescent : baseEnd_1197767 < baseStart_1197767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197829 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_1197829 : Nat := 118140960795 + 1197829 * 2 ^ 59
def prefixEnd_1197829 : Nat := 4983230072969 + 3 ^ 40 * 1197829 * 2
def baseEnd_1197829 : Nat := 410041345929666148152527

theorem tailTrace_1197829 : CollatzResearch.WordTrace tailWord_1197829 prefixEnd_1197829 410041345929666148152527 := by
  unfold tailWord_1197829
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688412777477580751428541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29125608518318387167619027 43688412777477580751428541)
  ·
    refine ⟨16383154791554092781785703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43688412777477580751428541 16383154791554092781785703)
    ·
      refine ⟨24574732187331139172678555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16383154791554092781785703 24574732187331139172678555)
      ·
        refine ⟨36862098280996708759017833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24574732187331139172678555 36862098280996708759017833)
        ·
          refine ⟨27646573710747531569263375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36862098280996708759017833 27646573710747531569263375)
          ·
            refine ⟨41469860566121297353895063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27646573710747531569263375 41469860566121297353895063)
            ·
              refine ⟨62204790849181946030842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41469860566121297353895063 62204790849181946030842595)
              ·
                refine ⟨93307186273772919046263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62204790849181946030842595 93307186273772919046263893)
                ·
                  refine ⟨1093443589145776395073405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 93307186273772919046263893 1093443589145776395073405)
                  ·
                    refine ⟨410041345929666148152527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093443589145776395073405 410041345929666148152527)
                    ·
                      rfl

theorem cell22_1197829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_1197829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197829 prefixEnd_1197829 := by exact prefixLift 1197829
  have htrace : WordTrace (prefixWord ++ tailWord_1197829) baseStart_1197829 baseEnd_1197829 := by
    simpa [prefixWord, tailWord_1197829, baseEnd_1197829] using wordTrace_append hprefix tailTrace_1197829
  have hstable : (prefixWord ++ tailWord_1197829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197829).length < 2 ^ (prefixWord ++ tailWord_1197829).sum := by decide
  have hdescent : baseEnd_1197829 < baseStart_1197829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197831 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 6]
def baseStart_1197831 : Nat := 118140960795 + 1197831 * 2 ^ 59
def prefixEnd_1197831 : Nat := 4983230072969 + 3 ^ 40 * 1197831 * 2
def baseEnd_1197831 : Nat := 136680676856846269867507

theorem tailTrace_1197831 : CollatzResearch.WordTrace tailWord_1197831 prefixEnd_1197831 136680676856846269867507 := by
  unfold tailWord_1197831
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688485723470335093001347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29125657148980223395334231 43688485723470335093001347)
  ·
    refine ⟨65532728585205502639502021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43688485723470335093001347 65532728585205502639502021)
    ·
      refine ⟨12287386609726031744906629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65532728585205502639502021 12287386609726031744906629)
      ·
        refine ⟨2303884989323630952169993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12287386609726031744906629 2303884989323630952169993)
        ·
          refine ⟨1727913741992723214127495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303884989323630952169993 1727913741992723214127495)
          ·
            refine ⟨2591870612989084821191243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727913741992723214127495 2591870612989084821191243)
            ·
              refine ⟨3887805919483627231786865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591870612989084821191243 3887805919483627231786865)
              ·
                refine ⟨2915854439612720423840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887805919483627231786865 2915854439612720423840149)
                ·
                  refine ⟨136680676856846269867507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2915854439612720423840149 136680676856846269867507)
                  ·
                    rfl

theorem cell22_1197831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_1197831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197831 prefixEnd_1197831 := by exact prefixLift 1197831
  have htrace : WordTrace (prefixWord ++ tailWord_1197831) baseStart_1197831 baseEnd_1197831 := by
    simpa [prefixWord, tailWord_1197831, baseEnd_1197831] using wordTrace_append hprefix tailTrace_1197831
  have hstable : (prefixWord ++ tailWord_1197831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197831).length < 2 ^ (prefixWord ++ tailWord_1197831).sum := by decide
  have hdescent : baseEnd_1197831 < baseStart_1197831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197891 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 3, 3]
def baseStart_1197891 : Nat := 118140960795 + 1197891 * 2 ^ 59
def prefixEnd_1197891 : Nat := 4983230072969 + 3 ^ 40 * 1197891 * 2
def baseEnd_1197891 : Nat := 410062569796718653102337

theorem tailTrace_1197891 : CollatzResearch.WordTrace tailWord_1197891 prefixEnd_1197891 410062569796718653102337 := by
  unfold tailWord_1197891
  simp only [CollatzResearch.WordTrace]
  refine ⟨43690674103252965340185527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29127116068835310226790351 43690674103252965340185527)
  ·
    refine ⟨65536011154879448010278291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43690674103252965340185527 65536011154879448010278291)
    ·
      refine ⟨98304016732319172015417437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65536011154879448010278291 98304016732319172015417437)
      ·
        refine ⟨36864006274619689505781539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98304016732319172015417437 36864006274619689505781539)
        ·
          refine ⟨55296009411929534258672309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36864006274619689505781539 55296009411929534258672309)
          ·
            refine ⟨5184000882368393836750529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55296009411929534258672309 5184000882368393836750529)
            ·
              refine ⟨3888000661776295377562897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5184000882368393836750529 3888000661776295377562897)
              ·
                refine ⟨2916000496332221533172173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888000661776295377562897 2916000496332221533172173)
                ·
                  refine ⟨1093500186124583074939565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2916000496332221533172173 1093500186124583074939565)
                  ·
                    refine ⟨410062569796718653102337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093500186124583074939565 410062569796718653102337)
                    ·
                      rfl

theorem cell22_1197891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 3].length) (baseStart_1197891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197891 prefixEnd_1197891 := by exact prefixLift 1197891
  have htrace : WordTrace (prefixWord ++ tailWord_1197891) baseStart_1197891 baseEnd_1197891 := by
    simpa [prefixWord, tailWord_1197891, baseEnd_1197891] using wordTrace_append hprefix tailTrace_1197891
  have hstable : (prefixWord ++ tailWord_1197891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197891).length < 2 ^ (prefixWord ++ tailWord_1197891).sum := by decide
  have hdescent : baseEnd_1197891 < baseStart_1197891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197949 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1197949 : Nat := 118140960795 + 1197949 * 2 ^ 59
def prefixEnd_1197949 : Nat := 4983230072969 + 3 ^ 40 * 1197949 * 2
def baseEnd_1197949 : Nat := 136694141460675278384053

theorem tailTrace_1197949 : CollatzResearch.WordTrace tailWord_1197949 prefixEnd_1197949 136694141460675278384053 := by
  unfold tailWord_1197949
  simp only [CollatzResearch.WordTrace]
  refine ⟨43692789537042841245796901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29128526358028560830531267 43692789537042841245796901)
  ·
    refine ⟨8192398038195532733586919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43692789537042841245796901 8192398038195532733586919)
    ·
      refine ⟨12288597057293299100380379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192398038195532733586919 12288597057293299100380379)
      ·
        refine ⟨18432895585939948650570569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288597057293299100380379 18432895585939948650570569)
        ·
          refine ⟨13824671689454961487927927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18432895585939948650570569 13824671689454961487927927)
          ·
            refine ⟨20737007534182442231891891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824671689454961487927927 20737007534182442231891891)
            ·
              refine ⟨31105511301273663347837837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20737007534182442231891891 31105511301273663347837837)
              ·
                refine ⟨11664566737977623755439189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31105511301273663347837837 11664566737977623755439189)
                ·
                  refine ⟨136694141460675278384053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11664566737977623755439189 136694141460675278384053)
                  ·
                    rfl

theorem cell22_1197949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1197949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197949 prefixEnd_1197949 := by exact prefixLift 1197949
  have htrace : WordTrace (prefixWord ++ tailWord_1197949) baseStart_1197949 baseEnd_1197949 := by
    simpa [prefixWord, tailWord_1197949, baseEnd_1197949] using wordTrace_append hprefix tailTrace_1197949
  have hstable : (prefixWord ++ tailWord_1197949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197949).length < 2 ^ (prefixWord ++ tailWord_1197949).sum := by decide
  have hdescent : baseEnd_1197949 < baseStart_1197949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197976 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_1197976 : Nat := 118140960795 + 1197976 * 2 ^ 59
def prefixEnd_1197976 : Nat := 4983230072969 + 3 ^ 40 * 1197976 * 2
def baseEnd_1197976 : Nat := 410091667033806764727077

theorem tailTrace_1197976 : CollatzResearch.WordTrace tailWord_1197976 prefixEnd_1197976 410091667033806764727077 := by
  unfold tailWord_1197976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846887153972512428514891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29129182871963349904686521 21846887153972512428514891)
  ·
    refine ⟨32770330730958768642772337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846887153972512428514891 32770330730958768642772337)
    ·
      refine ⟨24577748048219076482079253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32770330730958768642772337 24577748048219076482079253)
      ·
        refine ⟨1152081939760269210097465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24577748048219076482079253 1152081939760269210097465)
        ·
          refine ⟨864061454820201907573099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152081939760269210097465 864061454820201907573099)
          ·
            refine ⟨1296092182230302861359649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864061454820201907573099 1296092182230302861359649)
            ·
              refine ⟨972069136672727146019737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296092182230302861359649 972069136672727146019737)
              ·
                refine ⟨729051852504545359514803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972069136672727146019737 729051852504545359514803)
                ·
                  refine ⟨1093577778756818039272205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729051852504545359514803 1093577778756818039272205)
                  ·
                    refine ⟨410091667033806764727077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093577778756818039272205 410091667033806764727077)
                    ·
                      rfl

theorem cell22_1197976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_1197976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1197976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1197976 prefixEnd_1197976 := by exact prefixLift 1197976
  have htrace : WordTrace (prefixWord ++ tailWord_1197976) baseStart_1197976 baseEnd_1197976 := by
    simpa [prefixWord, tailWord_1197976, baseEnd_1197976] using wordTrace_append hprefix tailTrace_1197976
  have hstable : (prefixWord ++ tailWord_1197976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197976).length < 2 ^ (prefixWord ++ tailWord_1197976).sum := by decide
  have hdescent : baseEnd_1197976 < baseStart_1197976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198013 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1198013 : Nat := 118140960795 + 1198013 * 2 ^ 59
def prefixEnd_1198013 : Nat := 4983230072969 + 3 ^ 40 * 1198013 * 2
def baseEnd_1198013 : Nat := 410104332889951001551963

theorem tailTrace_1198013 : CollatzResearch.WordTrace tailWord_1198013 prefixEnd_1198013 410104332889951001551963 := by
  unfold tailWord_1198013
  simp only [CollatzResearch.WordTrace]
  refine ⟨43695123808810980176126693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29130082539207320117417795 43695123808810980176126693)
  ·
    refine ⟨8192835714152058783023755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43695123808810980176126693 8192835714152058783023755)
    ·
      refine ⟨12289253571228088174535633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192835714152058783023755 12289253571228088174535633)
      ·
        refine ⟨9216940178421066130901725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12289253571228088174535633 9216940178421066130901725)
        ·
          refine ⟨3456352566907899799088147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9216940178421066130901725 3456352566907899799088147)
          ·
            refine ⟨5184528850361849698632221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456352566907899799088147 5184528850361849698632221)
            ·
              refine ⟨1944198318885693636987083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5184528850361849698632221 1944198318885693636987083)
              ·
                refine ⟨2916297478328540455480625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944198318885693636987083 2916297478328540455480625)
                ·
                  refine ⟨2187223108746405341610469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916297478328540455480625 2187223108746405341610469)
                  ·
                    refine ⟨410104332889951001551963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187223108746405341610469 410104332889951001551963)
                    ·
                      rfl

theorem cell22_1198013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1198013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198013 prefixEnd_1198013 := by exact prefixLift 1198013
  have htrace : WordTrace (prefixWord ++ tailWord_1198013) baseStart_1198013 baseEnd_1198013 := by
    simpa [prefixWord, tailWord_1198013, baseEnd_1198013] using wordTrace_append hprefix tailTrace_1198013
  have hstable : (prefixWord ++ tailWord_1198013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198013).length < 2 ^ (prefixWord ++ tailWord_1198013).sum := by decide
  have hdescent : baseEnd_1198013 < baseStart_1198013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198131 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_1198131 : Nat := 118140960795 + 1198131 * 2 ^ 59
def prefixEnd_1198131 : Nat := 4983230072969 + 3 ^ 40 * 1198131 * 2
def baseEnd_1198131 : Nat := 410144726701438027101601

theorem tailTrace_1198131 : CollatzResearch.WordTrace tailWord_1198131 prefixEnd_1198131 410144726701438027101601 := by
  unfold tailWord_1198131
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699427622383486328922247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29132951748255657552614831 43699427622383486328922247)
  ·
    refine ⟨65549141433575229493383371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43699427622383486328922247 65549141433575229493383371)
    ·
      refine ⟨98323712150362844240075057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65549141433575229493383371 98323712150362844240075057)
      ·
        refine ⟨73742784112772133180056293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98323712150362844240075057 73742784112772133180056293)
        ·
          refine ⟨13826772021144774971260555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73742784112772133180056293 13826772021144774971260555)
          ·
            refine ⟨20740158031717162456890833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13826772021144774971260555 20740158031717162456890833)
            ·
              refine ⟨15555118523787871842668125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20740158031717162456890833 15555118523787871842668125)
              ·
                refine ⟨5833169446420451941000547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15555118523787871842668125 5833169446420451941000547)
                ·
                  refine ⟨8749754169630677911500821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833169446420451941000547 8749754169630677911500821)
                  ·
                    refine ⟨410144726701438027101601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8749754169630677911500821 410144726701438027101601)
                    ·
                      rfl

theorem cell22_1198131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_1198131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198131 prefixEnd_1198131 := by exact prefixLift 1198131
  have htrace : WordTrace (prefixWord ++ tailWord_1198131) baseStart_1198131 baseEnd_1198131 := by
    simpa [prefixWord, tailWord_1198131, baseEnd_1198131] using wordTrace_append hprefix tailTrace_1198131
  have hstable : (prefixWord ++ tailWord_1198131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198131).length < 2 ^ (prefixWord ++ tailWord_1198131).sum := by decide
  have hdescent : baseEnd_1198131 < baseStart_1198131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198133 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1198133 : Nat := 118140960795 + 1198133 * 2 ^ 59
def prefixEnd_1198133 : Nat := 4983230072969 + 3 ^ 40 * 1198133 * 2
def baseEnd_1198133 : Nat := 410145411342310688551595

theorem tailTrace_1198133 : CollatzResearch.WordTrace tailWord_1198133 prefixEnd_1198133 410145411342310688551595 := by
  unfold tailWord_1198133
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699500568376240670495053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29133000378917493780330035 43699500568376240670495053)
  ·
    refine ⟨16387312713141090251435645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43699500568376240670495053 16387312713141090251435645)
    ·
      refine ⟨6145242267427908844288367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16387312713141090251435645 6145242267427908844288367)
      ·
        refine ⟨9217863401141863266432551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145242267427908844288367 9217863401141863266432551)
        ·
          refine ⟨13826795101712794899648827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217863401141863266432551 13826795101712794899648827)
          ·
            refine ⟨20740192652569192349473241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13826795101712794899648827 20740192652569192349473241)
            ·
              refine ⟨15555144489426894262104931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20740192652569192349473241 15555144489426894262104931)
              ·
                refine ⟨23332716734140341393157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15555144489426894262104931 23332716734140341393157397)
                ·
                  refine ⟨1093721096912828502804253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23332716734140341393157397 1093721096912828502804253)
                  ·
                    refine ⟨410145411342310688551595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093721096912828502804253 410145411342310688551595)
                    ·
                      rfl

theorem cell22_1198133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1198133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198133 prefixEnd_1198133 := by exact prefixLift 1198133
  have htrace : WordTrace (prefixWord ++ tailWord_1198133) baseStart_1198133 baseEnd_1198133 := by
    simpa [prefixWord, tailWord_1198133, baseEnd_1198133] using wordTrace_append hprefix tailTrace_1198133
  have hstable : (prefixWord ++ tailWord_1198133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198133).length < 2 ^ (prefixWord ++ tailWord_1198133).sum := by decide
  have hdescent : baseEnd_1198133 < baseStart_1198133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198137 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_1198137 : Nat := 118140960795 + 1198137 * 2 ^ 59
def prefixEnd_1198137 : Nat := 4983230072969 + 3 ^ 40 * 1198137 * 2
def baseEnd_1198137 : Nat := 410146780624056011451583

theorem tailTrace_1198137 : CollatzResearch.WordTrace tailWord_1198137 prefixEnd_1198137 410146780624056011451583 := by
  unfold tailWord_1198137
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699646460361749353640665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29133097640241166235760443 43699646460361749353640665)
  ·
    refine ⟨32774734845271312015230499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43699646460361749353640665 32774734845271312015230499)
    ·
      refine ⟨49162102267906968022845749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32774734845271312015230499 49162102267906968022845749)
      ·
        refine ⟨4608947087616278252141789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49162102267906968022845749 4608947087616278252141789)
        ·
          refine ⟨1728355157856104344553171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4608947087616278252141789 1728355157856104344553171)
          ·
            refine ⟨2592532736784156516829757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728355157856104344553171 2592532736784156516829757)
            ·
              refine ⟨972199776294058693811159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2592532736784156516829757 972199776294058693811159)
              ·
                refine ⟨1458299664441088040716739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972199776294058693811159 1458299664441088040716739)
                ·
                  refine ⟨2187449496661632061075109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458299664441088040716739 2187449496661632061075109)
                  ·
                    refine ⟨410146780624056011451583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187449496661632061075109 410146780624056011451583)
                    ·
                      rfl

theorem cell22_1198137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_1198137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198137 prefixEnd_1198137 := by exact prefixLift 1198137
  have htrace : WordTrace (prefixWord ++ tailWord_1198137) baseStart_1198137 baseEnd_1198137 := by
    simpa [prefixWord, tailWord_1198137, baseEnd_1198137] using wordTrace_append hprefix tailTrace_1198137
  have hstable : (prefixWord ++ tailWord_1198137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198137).length < 2 ^ (prefixWord ++ tailWord_1198137).sum := by decide
  have hdescent : baseEnd_1198137 < baseStart_1198137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198150 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1198150 : Nat := 118140960795 + 1198150 * 2 ^ 59
def prefixEnd_1198150 : Nat := 4983230072969 + 3 ^ 40 * 1198150 * 2
def baseEnd_1198150 : Nat := 410151230789728310876543

theorem tailTrace_1198150 : CollatzResearch.WordTrace tailWord_1198150 prefixEnd_1198150 410151230789728310876543 := by
  unfold tailWord_1198150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365628769041082892933247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29133413739543101715909269 1365628769041082892933247)
  ·
    refine ⟨2048443153561624339399871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365628769041082892933247 2048443153561624339399871)
    ·
      refine ⟨3072664730342436509099807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048443153561624339399871 3072664730342436509099807)
      ·
        refine ⟨4608997095513654763649711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072664730342436509099807 4608997095513654763649711)
        ·
          refine ⟨6913495643270482145474567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608997095513654763649711 6913495643270482145474567)
          ·
            refine ⟨10370243464905723218211851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913495643270482145474567 10370243464905723218211851)
            ·
              refine ⟨15555365197358584827317777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10370243464905723218211851 15555365197358584827317777)
              ·
                refine ⟨11666523898018938620488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15555365197358584827317777 11666523898018938620488333)
                ·
                  refine ⟨4374946461757101982683125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11666523898018938620488333 4374946461757101982683125)
                  ·
                    refine ⟨410151230789728310876543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4374946461757101982683125 410151230789728310876543)
                    ·
                      rfl

theorem cell22_1198150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1198150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198150 prefixEnd_1198150 := by exact prefixLift 1198150
  have htrace : WordTrace (prefixWord ++ tailWord_1198150) baseStart_1198150 baseEnd_1198150 := by
    simpa [prefixWord, tailWord_1198150, baseEnd_1198150] using wordTrace_append hprefix tailTrace_1198150
  have hstable : (prefixWord ++ tailWord_1198150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198150).length < 2 ^ (prefixWord ++ tailWord_1198150).sum := by decide
  have hdescent : baseEnd_1198150 < baseStart_1198150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1198161 : Nat := 118140960795 + 1198161 * 2 ^ 59
def prefixEnd_1198161 : Nat := 4983230072969 + 3 ^ 40 * 1198161 * 2
def baseEnd_1198161 : Nat := 410154996314527948851509

theorem tailTrace_1198161 : CollatzResearch.WordTrace tailWord_1198161 prefixEnd_1198161 410154996314527948851509 := by
  unfold tailWord_1198161
  simp only [CollatzResearch.WordTrace]
  refine ⟨43700521812274801452514337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29133681208183200968342891 43700521812274801452514337)
  ·
    refine ⟨32775391359206101089385753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43700521812274801452514337 32775391359206101089385753)
    ·
      refine ⟨24581543519404575817039315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32775391359206101089385753 24581543519404575817039315)
      ·
        refine ⟨36872315279106863725558973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24581543519404575817039315 36872315279106863725558973)
        ·
          refine ⟨13827118229665073897084615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36872315279106863725558973 13827118229665073897084615)
          ·
            refine ⟨20740677344497610845626923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13827118229665073897084615 20740677344497610845626923)
            ·
              refine ⟨31111016016746416268440385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20740677344497610845626923 31111016016746416268440385)
              ·
                refine ⟨23333262012559812201330289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31111016016746416268440385 23333262012559812201330289)
                ·
                  refine ⟨17499946509419859150997717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23333262012559812201330289 17499946509419859150997717)
                  ·
                    refine ⟨410154996314527948851509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17499946509419859150997717 410154996314527948851509)
                    ·
                      rfl

theorem cell22_1198161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1198161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198161 prefixEnd_1198161 := by exact prefixLift 1198161
  have htrace : WordTrace (prefixWord ++ tailWord_1198161) baseStart_1198161 baseEnd_1198161 := by
    simpa [prefixWord, tailWord_1198161, baseEnd_1198161] using wordTrace_append hprefix tailTrace_1198161
  have hstable : (prefixWord ++ tailWord_1198161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198161).length < 2 ^ (prefixWord ++ tailWord_1198161).sum := by decide
  have hdescent : baseEnd_1198161 < baseStart_1198161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198212 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_1198212 : Nat := 118140960795 + 1198212 * 2 ^ 59
def prefixEnd_1198212 : Nat := 4983230072969 + 3 ^ 40 * 1198212 * 2
def baseEnd_1198212 : Nat := 410172454656780815826353

theorem tailTrace_1198212 : CollatzResearch.WordTrace tailWord_1198212 prefixEnd_1198212 410172454656780815826353 := by
  unfold tailWord_1198212
  simp only [CollatzResearch.WordTrace]
  refine ⟨21851190967545018581310445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29134921290060024775080593 21851190967545018581310445)
  ·
    refine ⟨8194196612829381967991417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21851190967545018581310445 8194196612829381967991417)
    ·
      refine ⟨6145647459622036475993563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8194196612829381967991417 6145647459622036475993563)
      ·
        refine ⟨9218471189433054713990345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145647459622036475993563 9218471189433054713990345)
        ·
          refine ⟨6913853392074791035492759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9218471189433054713990345 6913853392074791035492759)
          ·
            refine ⟨10370780088112186553239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913853392074791035492759 10370780088112186553239139)
            ·
              refine ⟨15556170132168279829858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10370780088112186553239139 15556170132168279829858709)
              ·
                refine ⟨729195474945388117024627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15556170132168279829858709 729195474945388117024627)
                ·
                  refine ⟨1093793212418082175536941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729195474945388117024627 1093793212418082175536941)
                  ·
                    refine ⟨410172454656780815826353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093793212418082175536941 410172454656780815826353)
                    ·
                      rfl

theorem cell22_1198212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_1198212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198212 prefixEnd_1198212 := by exact prefixLift 1198212
  have htrace : WordTrace (prefixWord ++ tailWord_1198212) baseStart_1198212 baseEnd_1198212 := by
    simpa [prefixWord, tailWord_1198212, baseEnd_1198212] using wordTrace_append hprefix tailTrace_1198212
  have hstable : (prefixWord ++ tailWord_1198212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198212).length < 2 ^ (prefixWord ++ tailWord_1198212).sum := by decide
  have hdescent : baseEnd_1198212 < baseStart_1198212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198283 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_1198283 : Nat := 118140960795 + 1198283 * 2 ^ 59
def prefixEnd_1198283 : Nat := 4983230072969 + 3 ^ 40 * 1198283 * 2
def baseEnd_1198283 : Nat := 410196759407760297301135

theorem tailTrace_1198283 : CollatzResearch.WordTrace tailWord_1198283 prefixEnd_1198283 410196759407760297301135 := by
  unfold tailWord_1198283
  simp only [CollatzResearch.WordTrace]
  refine ⟨43704971517832816288455503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29136647678555210858970335 43704971517832816288455503)
  ·
    refine ⟨65557457276749224432683255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43704971517832816288455503 65557457276749224432683255)
    ·
      refine ⟨98336185915123836649024883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65557457276749224432683255 98336185915123836649024883)
      ·
        refine ⟨147504278872685754973537325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98336185915123836649024883 147504278872685754973537325)
        ·
          refine ⟨55314104577257158115076497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147504278872685754973537325 55314104577257158115076497)
          ·
            refine ⟨41485578432942868586307373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55314104577257158115076497 41485578432942868586307373)
            ·
              refine ⟨15557091912353575719865265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41485578432942868586307373 15557091912353575719865265)
              ·
                refine ⟨11667818934265181789898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15557091912353575719865265 11667818934265181789898949)
                ·
                  refine ⟨2187716050174721585606053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11667818934265181789898949 2187716050174721585606053)
                  ·
                    refine ⟨410196759407760297301135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187716050174721585606053 410196759407760297301135)
                    ·
                      rfl

theorem cell22_1198283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_1198283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198283 prefixEnd_1198283 := by exact prefixLift 1198283
  have htrace : WordTrace (prefixWord ++ tailWord_1198283) baseStart_1198283 baseEnd_1198283 := by
    simpa [prefixWord, tailWord_1198283, baseEnd_1198283] using wordTrace_append hprefix tailTrace_1198283
  have hstable : (prefixWord ++ tailWord_1198283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198283).length < 2 ^ (prefixWord ++ tailWord_1198283).sum := by decide
  have hdescent : baseEnd_1198283 < baseStart_1198283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198298 : List Nat := [3, 1, 1, 2, 2, 1, 4, 8]
def baseStart_1198298 : Nat := 118140960795 + 1198298 * 2 ^ 59
def prefixEnd_1198298 : Nat := 4983230072969 + 3 ^ 40 * 1198298 * 2
def baseEnd_1198298 : Nat := 45577988246033917575121

theorem tailTrace_1198298 : CollatzResearch.WordTrace tailWord_1198298 prefixEnd_1198298 45577988246033917575121 := by
  unfold tailWord_1198298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926379653194618462562887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29137012408518982566834365 10926379653194618462562887)
  ·
    refine ⟨16389569479791927693844331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926379653194618462562887 16389569479791927693844331)
    ·
      refine ⟨24584354219687891540766497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16389569479791927693844331 24584354219687891540766497)
      ·
        refine ⟨18438265664765918655574873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24584354219687891540766497 18438265664765918655574873)
        ·
          refine ⟨13828699248574438991681155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18438265664765918655574873 13828699248574438991681155)
          ·
            refine ⟨20743048872861658487521733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13828699248574438991681155 20743048872861658487521733)
            ·
              refine ⟨3889321663661560966410325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20743048872861658487521733 3889321663661560966410325)
              ·
                refine ⟨45577988246033917575121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3889321663661560966410325 45577988246033917575121)
                ·
                  rfl

theorem cell22_1198298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_1198298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198298 prefixEnd_1198298 := by exact prefixLift 1198298
  have htrace : WordTrace (prefixWord ++ tailWord_1198298) baseStart_1198298 baseEnd_1198298 := by
    simpa [prefixWord, tailWord_1198298, baseEnd_1198298] using wordTrace_append hprefix tailTrace_1198298
  have hstable : (prefixWord ++ tailWord_1198298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198298).length < 2 ^ (prefixWord ++ tailWord_1198298).sum := by decide
  have hdescent : baseEnd_1198298 < baseStart_1198298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198381 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1198381 : Nat := 118140960795 + 1198381 * 2 ^ 59
def prefixEnd_1198381 : Nat := 4983230072969 + 3 ^ 40 * 1198381 * 2
def baseEnd_1198381 : Nat := 410230306810520708350835

theorem tailTrace_1198381 : CollatzResearch.WordTrace tailWord_1198381 prefixEnd_1198381 410230306810520708350835 := by
  unfold tailWord_1198381
  simp only [CollatzResearch.WordTrace]
  refine ⟨43708545871477779025522997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29139030580985186017015331 43708545871477779025522997)
  ·
    refine ⟨4097676175451041783642781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43708545871477779025522997 4097676175451041783642781)
    ·
      refine ⟨1536628565794140668866043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4097676175451041783642781 1536628565794140668866043)
      ·
        refine ⟨2304942848691211003299065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536628565794140668866043 2304942848691211003299065)
        ·
          refine ⟨1728707136518408252474299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304942848691211003299065 1728707136518408252474299)
          ·
            refine ⟨2593060704777612378711449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728707136518408252474299 2593060704777612378711449)
            ·
              refine ⟨1944795528583209284033587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2593060704777612378711449 1944795528583209284033587)
              ·
                refine ⟨2917193292874813926050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944795528583209284033587 2917193292874813926050381)
                ·
                  refine ⟨1093947484828055222268893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2917193292874813926050381 1093947484828055222268893)
                  ·
                    refine ⟨410230306810520708350835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093947484828055222268893 410230306810520708350835)
                    ·
                      rfl

theorem cell22_1198381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1198381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198381 prefixEnd_1198381 := by exact prefixLift 1198381
  have htrace : WordTrace (prefixWord ++ tailWord_1198381) baseStart_1198381 baseEnd_1198381 := by
    simpa [prefixWord, tailWord_1198381, baseEnd_1198381] using wordTrace_append hprefix tailTrace_1198381
  have hstable : (prefixWord ++ tailWord_1198381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198381).length < 2 ^ (prefixWord ++ tailWord_1198381).sum := by decide
  have hdescent : baseEnd_1198381 < baseStart_1198381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198407 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1198407 : Nat := 118140960795 + 1198407 * 2 ^ 59
def prefixEnd_1198407 : Nat := 4983230072969 + 3 ^ 40 * 1198407 * 2
def baseEnd_1198407 : Nat := 410239207141865307200755

theorem tailTrace_1198407 : CollatzResearch.WordTrace tailWord_1198407 prefixEnd_1198407 410239207141865307200755 := by
  unfold tailWord_1198407
  simp only [CollatzResearch.WordTrace]
  refine ⟨43709494169383585465969475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29139662779589056977312983 43709494169383585465969475)
  ·
    refine ⟨65564241254075378198954213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43709494169383585465969475 65564241254075378198954213)
    ·
      refine ⟨12293295235139133412303915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65564241254075378198954213 12293295235139133412303915)
      ·
        refine ⟨18439942852708700118455873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12293295235139133412303915 18439942852708700118455873)
        ·
          refine ⟨13829957139531525088841905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18439942852708700118455873 13829957139531525088841905)
          ·
            refine ⟨10372467854648643816631429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13829957139531525088841905 10372467854648643816631429)
            ·
              refine ⟨1944837722746620715618393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10372467854648643816631429 1944837722746620715618393)
              ·
                refine ⟨1458628292059965536713795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944837722746620715618393 1458628292059965536713795)
                ·
                  refine ⟨2187942438089948305070693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458628292059965536713795 2187942438089948305070693)
                  ·
                    refine ⟨410239207141865307200755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2187942438089948305070693 410239207141865307200755)
                    ·
                      rfl

theorem cell22_1198407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1198407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198407 prefixEnd_1198407 := by exact prefixLift 1198407
  have htrace : WordTrace (prefixWord ++ tailWord_1198407) baseStart_1198407 baseEnd_1198407 := by
    simpa [prefixWord, tailWord_1198407, baseEnd_1198407] using wordTrace_append hprefix tailTrace_1198407
  have hstable : (prefixWord ++ tailWord_1198407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198407).length < 2 ^ (prefixWord ++ tailWord_1198407).sum := by decide
  have hdescent : baseEnd_1198407 < baseStart_1198407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198437 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_1198437 : Nat := 118140960795 + 1198437 * 2 ^ 59
def prefixEnd_1198437 : Nat := 4983230072969 + 3 ^ 40 * 1198437 * 2
def baseEnd_1198437 : Nat := 410249476754955228950663

theorem tailTrace_1198437 : CollatzResearch.WordTrace tailWord_1198437 prefixEnd_1198437 410249476754955228950663 := by
  unfold tailWord_1198437
  simp only [CollatzResearch.WordTrace]
  refine ⟨43710588359274900589561565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29140392239516600393041043 43710588359274900589561565)
  ·
    refine ⟨16391470634728087721085587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43710588359274900589561565 16391470634728087721085587)
    ·
      refine ⟨24587205952092131581628381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16391470634728087721085587 24587205952092131581628381)
      ·
        refine ⟨9220202232034549343110643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24587205952092131581628381 9220202232034549343110643)
        ·
          refine ⟨13830303348051824014665965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9220202232034549343110643 13830303348051824014665965)
          ·
            refine ⟨5186363755519434005499737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13830303348051824014665965 5186363755519434005499737)
            ·
              refine ⟨3889772816639575504124803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186363755519434005499737 3889772816639575504124803)
              ·
                refine ⟨5834659224959363256187205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889772816639575504124803 5834659224959363256187205)
                ·
                  refine ⟨1093998604679880610535101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5834659224959363256187205 1093998604679880610535101)
                  ·
                    refine ⟨410249476754955228950663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093998604679880610535101 410249476754955228950663)
                    ·
                      rfl

theorem cell22_1198437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_1198437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198437 prefixEnd_1198437 := by exact prefixLift 1198437
  have htrace : WordTrace (prefixWord ++ tailWord_1198437) baseStart_1198437 baseEnd_1198437 := by
    simpa [prefixWord, tailWord_1198437, baseEnd_1198437] using wordTrace_append hprefix tailTrace_1198437
  have hstable : (prefixWord ++ tailWord_1198437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198437).length < 2 ^ (prefixWord ++ tailWord_1198437).sum := by decide
  have hdescent : baseEnd_1198437 < baseStart_1198437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198450 : List Nat := [3, 2, 1, 2, 1, 3, 1, 9]
def baseStart_1198450 : Nat := 118140960795 + 1198450 * 2 ^ 59
def prefixEnd_1198450 : Nat := 4983230072969 + 3 ^ 40 * 1198450 * 2
def baseEnd_1198450 : Nat := 45583769657847503152847

theorem tailTrace_1198450 : CollatzResearch.WordTrace tailWord_1198450 prefixEnd_1198450 45583769657847503152847 := by
  unfold tailWord_1198450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10927765627056950952446201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29140708338818535873189869 10927765627056950952446201)
  ·
    refine ⟨8195824220292713214334651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10927765627056950952446201 8195824220292713214334651)
    ·
      refine ⟨12293736330439069821501977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8195824220292713214334651 12293736330439069821501977)
      ·
        refine ⟨9220302247829302366126483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12293736330439069821501977 9220302247829302366126483)
        ·
          refine ⟨13830453371743953549189725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9220302247829302366126483 13830453371743953549189725)
          ·
            refine ⟨5186420014403982580946147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13830453371743953549189725 5186420014403982580946147)
            ·
              refine ⟨7779630021605973871419221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186420014403982580946147 7779630021605973871419221)
              ·
                refine ⟨45583769657847503152847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7779630021605973871419221 45583769657847503152847)
                ·
                  rfl

theorem cell22_1198450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_1198450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198450 prefixEnd_1198450 := by exact prefixLift 1198450
  have htrace : WordTrace (prefixWord ++ tailWord_1198450) baseStart_1198450 baseEnd_1198450 := by
    simpa [prefixWord, tailWord_1198450, baseEnd_1198450] using wordTrace_append hprefix tailTrace_1198450
  have hstable : (prefixWord ++ tailWord_1198450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198450).length < 2 ^ (prefixWord ++ tailWord_1198450).sum := by decide
  have hdescent : baseEnd_1198450 < baseStart_1198450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198604 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1198604 : Nat := 118140960795 + 1198604 * 2 ^ 59
def prefixEnd_1198604 : Nat := 4983230072969 + 3 ^ 40 * 1198604 * 2
def baseEnd_1198604 : Nat := 410306644267822460025151

theorem tailTrace_1198604 : CollatzResearch.WordTrace tailWord_1198604 prefixEnd_1198604 410306644267822460025151 := by
  unfold tailWord_1198604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21858339674834944055445433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29144452899779925407260577 21858339674834944055445433)
  ·
    refine ⟨16393754756126208041584075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21858339674834944055445433 16393754756126208041584075)
    ·
      refine ⟨24590632134189312062376113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16393754756126208041584075 24590632134189312062376113)
      ·
        refine ⟨18442974100641984046782085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24590632134189312062376113 18442974100641984046782085)
        ·
          refine ⟨3458057643870372008771641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18442974100641984046782085 3458057643870372008771641)
          ·
            refine ⟨2593543232902779006578731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458057643870372008771641 2593543232902779006578731)
            ·
              refine ⟨3890314849354168509868097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593543232902779006578731 3890314849354168509868097)
              ·
                refine ⟨2917736137015626382401073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3890314849354168509868097 2917736137015626382401073)
                ·
                  refine ⟨2188302102761719786800805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917736137015626382401073 2188302102761719786800805)
                  ·
                    refine ⟨410306644267822460025151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188302102761719786800805 410306644267822460025151)
                    ·
                      rfl

theorem cell22_1198604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1198604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198604 prefixEnd_1198604 := by exact prefixLift 1198604
  have htrace : WordTrace (prefixWord ++ tailWord_1198604) baseStart_1198604 baseEnd_1198604 := by
    simpa [prefixWord, tailWord_1198604, baseEnd_1198604] using wordTrace_append hprefix tailTrace_1198604
  have hstable : (prefixWord ++ tailWord_1198604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198604).length < 2 ^ (prefixWord ++ tailWord_1198604).sum := by decide
  have hdescent : baseEnd_1198604 < baseStart_1198604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198707 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_1198707 : Nat := 118140960795 + 1198707 * 2 ^ 59
def prefixEnd_1198707 : Nat := 4983230072969 + 3 ^ 40 * 1198707 * 2
def baseEnd_1198707 : Nat := 410341903272764524699835

theorem tailTrace_1198707 : CollatzResearch.WordTrace tailWord_1198707 prefixEnd_1198707 410341903272764524699835 := by
  unfold tailWord_1198707
  simp only [CollatzResearch.WordTrace]
  refine ⟨43720436068296736701890375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29146957378864491134593583 43720436068296736701890375)
  ·
    refine ⟨65580654102445105052835563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43720436068296736701890375 65580654102445105052835563)
    ·
      refine ⟨98370981153667657579253345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65580654102445105052835563 98370981153667657579253345)
      ·
        refine ⟨73778235865250743184440009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98370981153667657579253345 73778235865250743184440009)
        ·
          refine ⟨55333676898938057388330007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73778235865250743184440009 55333676898938057388330007)
          ·
            refine ⟨83000515348407086082495011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55333676898938057388330007 83000515348407086082495011)
            ·
              refine ⟨124500773022610629123742517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83000515348407086082495011 124500773022610629123742517)
              ·
                refine ⟨11671947470869746480350861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124500773022610629123742517 11671947470869746480350861)
                ·
                  refine ⟨4376980301576154930131573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11671947470869746480350861 4376980301576154930131573)
                  ·
                    refine ⟨410341903272764524699835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4376980301576154930131573 410341903272764524699835)
                    ·
                      rfl

theorem cell22_1198707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_1198707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198707 prefixEnd_1198707 := by exact prefixLift 1198707
  have htrace : WordTrace (prefixWord ++ tailWord_1198707) baseStart_1198707 baseEnd_1198707 := by
    simpa [prefixWord, tailWord_1198707, baseEnd_1198707] using wordTrace_append hprefix tailTrace_1198707
  have hstable : (prefixWord ++ tailWord_1198707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198707).length < 2 ^ (prefixWord ++ tailWord_1198707).sum := by decide
  have hdescent : baseEnd_1198707 < baseStart_1198707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198711 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1198711 : Nat := 118140960795 + 1198711 * 2 ^ 59
def prefixEnd_1198711 : Nat := 4983230072969 + 3 ^ 40 * 1198711 * 2
def baseEnd_1198711 : Nat := 410343272554509847599823

theorem tailTrace_1198711 : CollatzResearch.WordTrace tailWord_1198711 prefixEnd_1198711 410343272554509847599823 := by
  unfold tailWord_1198711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43720581960282245385035987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29147054640188163590023991 43720581960282245385035987)
  ·
    refine ⟨65580872940423368077553981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43720581960282245385035987 65580872940423368077553981)
    ·
      refine ⟨24592827352658763029082743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65580872940423368077553981 24592827352658763029082743)
      ·
        refine ⟨36889241028988144543624115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24592827352658763029082743 36889241028988144543624115)
        ·
          refine ⟨55333861543482216815436173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36889241028988144543624115 55333861543482216815436173)
          ·
            refine ⟨20750198078805831305788565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55333861543482216815436173 20750198078805831305788565)
            ·
              refine ⟨972665534944023342458839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20750198078805831305788565 972665534944023342458839)
              ·
                refine ⟨1458998302416035013688259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972665534944023342458839 1458998302416035013688259)
                ·
                  refine ⟨2188497453624052520532389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458998302416035013688259 2188497453624052520532389)
                  ·
                    refine ⟨410343272554509847599823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188497453624052520532389 410343272554509847599823)
                    ·
                      rfl

theorem cell22_1198711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1198711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198711 prefixEnd_1198711 := by exact prefixLift 1198711
  have htrace : WordTrace (prefixWord ++ tailWord_1198711) baseStart_1198711 baseEnd_1198711 := by
    simpa [prefixWord, tailWord_1198711, baseEnd_1198711] using wordTrace_append hprefix tailTrace_1198711
  have hstable : (prefixWord ++ tailWord_1198711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198711).length < 2 ^ (prefixWord ++ tailWord_1198711).sum := by decide
  have hdescent : baseEnd_1198711 < baseStart_1198711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198876 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1198876 : Nat := 118140960795 + 1198876 * 2 ^ 59
def prefixEnd_1198876 : Nat := 4983230072969 + 3 ^ 40 * 1198876 * 2
def baseEnd_1198876 : Nat := 410399755426504417224317

theorem tailTrace_1198876 : CollatzResearch.WordTrace tailWord_1198876 prefixEnd_1198876 410399755426504417224317 := by
  unfold tailWord_1198876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863300002342239282396241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29151066669789652376528321 21863300002342239282396241)
  ·
    refine ⟨16397475001756679461797181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21863300002342239282396241 16397475001756679461797181)
    ·
      refine ⟨6149053125658754798173943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16397475001756679461797181 6149053125658754798173943)
      ·
        refine ⟨9223579688488132197260915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149053125658754798173943 9223579688488132197260915)
        ·
          refine ⟨13835369532732198295891373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9223579688488132197260915 13835369532732198295891373)
          ·
            refine ⟨5188263574774574360959265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13835369532732198295891373 5188263574774574360959265)
            ·
              refine ⟨3891197681080930770719449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188263574774574360959265 3891197681080930770719449)
              ·
                refine ⟨2918398260810698078039587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3891197681080930770719449 2918398260810698078039587)
                ·
                  refine ⟨4377597391216047117059381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918398260810698078039587 4377597391216047117059381)
                  ·
                    refine ⟨410399755426504417224317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4377597391216047117059381 410399755426504417224317)
                    ·
                      rfl

theorem cell22_1198876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1198876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198876 prefixEnd_1198876 := by exact prefixLift 1198876
  have htrace : WordTrace (prefixWord ++ tailWord_1198876) baseStart_1198876 baseEnd_1198876 := by
    simpa [prefixWord, tailWord_1198876, baseEnd_1198876] using wordTrace_append hprefix tailTrace_1198876
  have hstable : (prefixWord ++ tailWord_1198876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198876).length < 2 ^ (prefixWord ++ tailWord_1198876).sum := by decide
  have hdescent : baseEnd_1198876 < baseStart_1198876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198880 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_1198880 : Nat := 118140960795 + 1198880 * 2 ^ 59
def prefixEnd_1198880 : Nat := 4983230072969 + 3 ^ 40 * 1198880 * 2
def baseEnd_1198880 : Nat := 410401124708249740124305

theorem tailTrace_1198880 : CollatzResearch.WordTrace tailWord_1198880 prefixEnd_1198880 410401124708249740124305 := by
  unfold tailWord_1198880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863372948334993623969047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29151163931113324831958729 21863372948334993623969047)
  ·
    refine ⟨32795059422502490435953571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21863372948334993623969047 32795059422502490435953571)
    ·
      refine ⟨49192589133753735653930357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32795059422502490435953571 49192589133753735653930357)
      ·
        refine ⟨4611805231289412717555971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49192589133753735653930357 4611805231289412717555971)
        ·
          refine ⟨6917707846934119076333957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611805231289412717555971 6917707846934119076333957)
          ·
            refine ⟨1297070221300147326812617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6917707846934119076333957 1297070221300147326812617)
            ·
              refine ⟨972802665975110495109463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297070221300147326812617 972802665975110495109463)
              ·
                refine ⟨1459203998962665742664195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972802665975110495109463 1459203998962665742664195)
                ·
                  refine ⟨2188805998443998613996293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459203998962665742664195 2188805998443998613996293)
                  ·
                    refine ⟨410401124708249740124305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2188805998443998613996293 410401124708249740124305)
                    ·
                      rfl

theorem cell22_1198880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_1198880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198880 prefixEnd_1198880 := by exact prefixLift 1198880
  have htrace : WordTrace (prefixWord ++ tailWord_1198880) baseStart_1198880 baseEnd_1198880 := by
    simpa [prefixWord, tailWord_1198880, baseEnd_1198880] using wordTrace_append hprefix tailTrace_1198880
  have hstable : (prefixWord ++ tailWord_1198880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198880).length < 2 ^ (prefixWord ++ tailWord_1198880).sum := by decide
  have hdescent : baseEnd_1198880 < baseStart_1198880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198910 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1198910 : Nat := 118140960795 + 1198910 * 2 ^ 59
def prefixEnd_1198910 : Nat := 4983230072969 + 3 ^ 40 * 1198910 * 2
def baseEnd_1198910 : Nat := 410411394321339661874213

theorem tailTrace_1198910 : CollatzResearch.WordTrace tailWord_1198910 prefixEnd_1198910 410411394321339661874213 := by
  unfold tailWord_1198910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465980010820162796441273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29151893391040868247686789 5465980010820162796441273)
  ·
    refine ⟨4099485008115122097330955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5465980010820162796441273 4099485008115122097330955)
    ·
      refine ⟨6149227512172683145996433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099485008115122097330955 6149227512172683145996433)
      ·
        refine ⟨4611920634129512359497325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6149227512172683145996433 4611920634129512359497325)
        ·
          refine ⟨1729470237798567134811497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4611920634129512359497325 1729470237798567134811497)
          ·
            refine ⟨1297102678348925351108623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729470237798567134811497 1297102678348925351108623)
            ·
              refine ⟨1945654017523388026662935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297102678348925351108623 1945654017523388026662935)
              ·
                refine ⟨2918481026285082039994403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945654017523388026662935 2918481026285082039994403)
                ·
                  refine ⟨4377721539427623059991605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918481026285082039994403 4377721539427623059991605)
                  ·
                    refine ⟨410411394321339661874213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4377721539427623059991605 410411394321339661874213)
                    ·
                      rfl

theorem cell22_1198910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1198910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198910 prefixEnd_1198910 := by exact prefixLift 1198910
  have htrace : WordTrace (prefixWord ++ tailWord_1198910) baseStart_1198910 baseEnd_1198910 := by
    simpa [prefixWord, tailWord_1198910, baseEnd_1198910] using wordTrace_append hprefix tailTrace_1198910
  have hstable : (prefixWord ++ tailWord_1198910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198910).length < 2 ^ (prefixWord ++ tailWord_1198910).sum := by decide
  have hdescent : baseEnd_1198910 < baseStart_1198910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198951 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 7]
def baseStart_1198951 : Nat := 118140960795 + 1198951 * 2 ^ 59
def prefixEnd_1198951 : Nat := 4983230072969 + 3 ^ 40 * 1198951 * 2
def baseEnd_1198951 : Nat := 136808476486409740533029

theorem tailTrace_1198951 : CollatzResearch.WordTrace tailWord_1198951 prefixEnd_1198951 136808476486409740533029 := by
  unfold tailWord_1198951
  simp only [CollatzResearch.WordTrace]
  refine ⟨43729335479412766373772707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29152890319608510915848471 43729335479412766373772707)
  ·
    refine ⟨65594003219119149560659061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43729335479412766373772707 65594003219119149560659061)
    ·
      refine ⟨6149437801792420271311787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65594003219119149560659061 6149437801792420271311787)
      ·
        refine ⟨9224156702688630406967681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149437801792420271311787 9224156702688630406967681)
        ·
          refine ⟨6918117527016472805225761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9224156702688630406967681 6918117527016472805225761)
          ·
            refine ⟨5188588145262354603919321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6918117527016472805225761 5188588145262354603919321)
            ·
              refine ⟨3891441108946765952939491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5188588145262354603919321 3891441108946765952939491)
              ·
                refine ⟨5837161663420148929409237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891441108946765952939491 5837161663420148929409237)
                ·
                  refine ⟨136808476486409740533029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5837161663420148929409237 136808476486409740533029)
                  ·
                    rfl

theorem cell22_1198951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_1198951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1198951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1198951 prefixEnd_1198951 := by exact prefixLift 1198951
  have htrace : WordTrace (prefixWord ++ tailWord_1198951) baseStart_1198951 baseEnd_1198951 := by
    simpa [prefixWord, tailWord_1198951, baseEnd_1198951] using wordTrace_append hprefix tailTrace_1198951
  have hstable : (prefixWord ++ tailWord_1198951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198951).length < 2 ^ (prefixWord ++ tailWord_1198951).sum := by decide
  have hdescent : baseEnd_1198951 < baseStart_1198951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199058 : List Nat := [3, 2, 2, 3, 1, 2, 9]
def baseStart_1199058 : Nat := 118140960795 + 1199058 * 2 ^ 59
def prefixEnd_1199058 : Nat := 4983230072969 + 3 ^ 40 * 1199058 * 2
def baseEnd_1199058 : Nat := 15202298435033948487917

theorem tailTrace_1199058 : CollatzResearch.WordTrace tailWord_1199058 prefixEnd_1199058 15202298435033948487917 := by
  unfold tailWord_1199058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933309522506280911979457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29155492060016749098611885 10933309522506280911979457)
  ·
    refine ⟨8199982141879710683984593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10933309522506280911979457 8199982141879710683984593)
    ·
      refine ⟨6149986606409783012988445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8199982141879710683984593 6149986606409783012988445)
      ·
        refine ⟨2306244977403668629870667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6149986606409783012988445 2306244977403668629870667)
        ·
          refine ⟨3459367466105502944806001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306244977403668629870667 3459367466105502944806001)
          ·
            refine ⟨2594525599579127208604501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459367466105502944806001 2594525599579127208604501)
            ·
              refine ⟨15202298435033948487917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2594525599579127208604501 15202298435033948487917)
              ·
                rfl

theorem cell22_1199058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 9].length) (baseStart_1199058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199058 prefixEnd_1199058 := by exact prefixLift 1199058
  have htrace : WordTrace (prefixWord ++ tailWord_1199058) baseStart_1199058 baseEnd_1199058 := by
    simpa [prefixWord, tailWord_1199058, baseEnd_1199058] using wordTrace_append hprefix tailTrace_1199058
  have hstable : (prefixWord ++ tailWord_1199058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199058).length < 2 ^ (prefixWord ++ tailWord_1199058).sum := by decide
  have hdescent : baseEnd_1199058 < baseStart_1199058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199062 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1199062 : Nat := 118140960795 + 1199062 * 2 ^ 59
def prefixEnd_1199062 : Nat := 4983230072969 + 3 ^ 40 * 1199062 * 2
def baseEnd_1199062 : Nat := 410463427027661932073747

theorem tailTrace_1199062 : CollatzResearch.WordTrace tailWord_1199062 prefixEnd_1199062 410463427027661932073747 := by
  unfold tailWord_1199062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2733336498875664520691465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29155589321340421554042293 2733336498875664520691465)
  ·
    refine ⟨2050002374156748390518599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2733336498875664520691465 2050002374156748390518599)
    ·
      refine ⟨3075003561235122585777899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2050002374156748390518599 3075003561235122585777899)
      ·
        refine ⟨4612505341852683878666849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3075003561235122585777899 4612505341852683878666849)
        ·
          refine ⟨3459379006389512909000137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612505341852683878666849 3459379006389512909000137)
          ·
            refine ⟨2594534254792134681750103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459379006389512909000137 2594534254792134681750103)
            ·
              refine ⟨3891801382188202022625155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594534254792134681750103 3891801382188202022625155)
              ·
                refine ⟨5837702073282303033937733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891801382188202022625155 5837702073282303033937733)
                ·
                  refine ⟨1094569138740431818863325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5837702073282303033937733 1094569138740431818863325)
                  ·
                    refine ⟨410463427027661932073747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1094569138740431818863325 410463427027661932073747)
                    ·
                      rfl

theorem cell22_1199062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1199062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199062 prefixEnd_1199062 := by exact prefixLift 1199062
  have htrace : WordTrace (prefixWord ++ tailWord_1199062) baseStart_1199062 baseEnd_1199062 := by
    simpa [prefixWord, tailWord_1199062, baseEnd_1199062] using wordTrace_append hprefix tailTrace_1199062
  have hstable : (prefixWord ++ tailWord_1199062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199062).length < 2 ^ (prefixWord ++ tailWord_1199062).sum := by decide
  have hdescent : baseEnd_1199062 < baseStart_1199062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199137 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 5]
def baseStart_1199137 : Nat := 118140960795 + 1199137 * 2 ^ 59
def prefixEnd_1199137 : Nat := 4983230072969 + 3 ^ 40 * 1199137 * 2
def baseEnd_1199137 : Nat := 136829700353462245482839

theorem tailTrace_1199137 : CollatzResearch.WordTrace tailWord_1199137 prefixEnd_1199137 136829700353462245482839 := by
  unfold tailWord_1199137
  simp only [CollatzResearch.WordTrace]
  refine ⟨43736119456738920140043665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29157412971159280093362443 43736119456738920140043665)
  ·
    refine ⟨32802089592554190105032749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43736119456738920140043665 32802089592554190105032749)
    ·
      refine ⟨12300783597207821289387281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32802089592554190105032749 12300783597207821289387281)
      ·
        refine ⟨9225587697905865967040461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12300783597207821289387281 9225587697905865967040461)
        ·
          refine ⟨3459595386714699737640173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9225587697905865967040461 3459595386714699737640173)
          ·
            refine ⟨1297348270018012401615065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3459595386714699737640173 1297348270018012401615065)
            ·
              refine ⟨973011202513509301211299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297348270018012401615065 973011202513509301211299)
              ·
                refine ⟨1459516803770263951816949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973011202513509301211299 1459516803770263951816949)
                ·
                  refine ⟨136829700353462245482839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1459516803770263951816949 136829700353462245482839)
                  ·
                    rfl

theorem cell22_1199137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_1199137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199137 prefixEnd_1199137 := by exact prefixLift 1199137
  have htrace : WordTrace (prefixWord ++ tailWord_1199137) baseStart_1199137 baseEnd_1199137 := by
    simpa [prefixWord, tailWord_1199137, baseEnd_1199137] using wordTrace_append hprefix tailTrace_1199137
  have hstable : (prefixWord ++ tailWord_1199137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199137).length < 2 ^ (prefixWord ++ tailWord_1199137).sum := by decide
  have hdescent : baseEnd_1199137 < baseStart_1199137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199150 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1199150 : Nat := 118140960795 + 1199150 * 2 ^ 59
def prefixEnd_1199150 : Nat := 4983230072969 + 3 ^ 40 * 1199150 * 2
def baseEnd_1199150 : Nat := 410493551226059035873477

theorem tailTrace_1199150 : CollatzResearch.WordTrace tailWord_1199150 prefixEnd_1199150 410493551226059035873477 := by
  unfold tailWord_1199150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5467074200711477920033363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29157729070461215573511269 5467074200711477920033363)
  ·
    refine ⟨8200611301067216880050045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5467074200711477920033363 8200611301067216880050045)
    ·
      refine ⟨3075229237900206330018767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8200611301067216880050045 3075229237900206330018767)
      ·
        refine ⟨4612843856850309495028151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3075229237900206330018767 4612843856850309495028151)
        ·
          refine ⟨6919265785275464242542227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612843856850309495028151 6919265785275464242542227)
          ·
            refine ⟨10378898677913196363813341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919265785275464242542227 10378898677913196363813341)
            ·
              refine ⟨3892087004217448636430003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10378898677913196363813341 3892087004217448636430003)
              ·
                refine ⟨5838130506326172954645005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892087004217448636430003 5838130506326172954645005)
                ·
                  refine ⟨2189298939872314857991877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5838130506326172954645005 2189298939872314857991877)
                  ·
                    refine ⟨410493551226059035873477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2189298939872314857991877 410493551226059035873477)
                    ·
                      rfl

theorem cell22_1199150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1199150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199150 prefixEnd_1199150 := by exact prefixLift 1199150
  have htrace : WordTrace (prefixWord ++ tailWord_1199150) baseStart_1199150 baseEnd_1199150 := by
    simpa [prefixWord, tailWord_1199150, baseEnd_1199150] using wordTrace_append hprefix tailTrace_1199150
  have hstable : (prefixWord ++ tailWord_1199150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199150).length < 2 ^ (prefixWord ++ tailWord_1199150).sum := by decide
  have hdescent : baseEnd_1199150 < baseStart_1199150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199242 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1199242 : Nat := 118140960795 + 1199242 * 2 ^ 59
def prefixEnd_1199242 : Nat := 4983230072969 + 3 ^ 40 * 1199242 * 2
def baseEnd_1199242 : Nat := 410525044706201462573195

theorem tailTrace_1199242 : CollatzResearch.WordTrace tailWord_1199242 prefixEnd_1199242 410525044706201462573195 := by
  unfold tailWord_1199242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934987280339630768153995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29159966080905682048410653 10934987280339630768153995)
  ·
    refine ⟨16402480920509446152230993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934987280339630768153995 16402480920509446152230993)
    ·
      refine ⟨12301860690382084614173245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402480920509446152230993 12301860690382084614173245)
      ·
        refine ⟨4613197758893281730314967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12301860690382084614173245 4613197758893281730314967)
        ·
          refine ⟨6919796638339922595472451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613197758893281730314967 6919796638339922595472451)
          ·
            refine ⟨10379694957509883893208677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919796638339922595472451 10379694957509883893208677)
            ·
              refine ⟨1946192804533103229976627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10379694957509883893208677 1946192804533103229976627)
              ·
                refine ⟨2919289206799654844964941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946192804533103229976627 2919289206799654844964941)
                ·
                  refine ⟨1094733452549870566861853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2919289206799654844964941 1094733452549870566861853)
                  ·
                    refine ⟨410525044706201462573195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1094733452549870566861853 410525044706201462573195)
                    ·
                      rfl

theorem cell22_1199242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1199242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199242 prefixEnd_1199242 := by exact prefixLift 1199242
  have htrace : WordTrace (prefixWord ++ tailWord_1199242) baseStart_1199242 baseEnd_1199242 := by
    simpa [prefixWord, tailWord_1199242, baseEnd_1199242] using wordTrace_append hprefix tailTrace_1199242
  have hstable : (prefixWord ++ tailWord_1199242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199242).length < 2 ^ (prefixWord ++ tailWord_1199242).sum := by decide
  have hdescent : baseEnd_1199242 < baseStart_1199242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199253 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1199253 : Nat := 118140960795 + 1199253 * 2 ^ 59
def prefixEnd_1199253 : Nat := 4983230072969 + 3 ^ 40 * 1199253 * 2
def baseEnd_1199253 : Nat := 410528810231001100548161

theorem tailTrace_1199253 : CollatzResearch.WordTrace tailWord_1199253 prefixEnd_1199253 410528810231001100548161 := by
  unfold tailWord_1199253
  simp only [CollatzResearch.WordTrace]
  refine ⟨43740350324318671951266413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29160233549545781300844275 43740350324318671951266413)
  ·
    refine ⟨16402631371619501981724905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43740350324318671951266413 16402631371619501981724905)
    ·
      refine ⟨12301973528714626486293679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402631371619501981724905 12301973528714626486293679)
      ·
        refine ⟨18452960293071939729440519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301973528714626486293679 18452960293071939729440519)
        ·
          refine ⟨27679440439607909594160779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18452960293071939729440519 27679440439607909594160779)
          ·
            refine ⟨41519160659411864391241169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27679440439607909594160779 41519160659411864391241169)
            ·
              refine ⟨31139370494558898293430877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41519160659411864391241169 31139370494558898293430877)
              ·
                refine ⟨11677263935459586860036579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31139370494558898293430877 11677263935459586860036579)
                ·
                  refine ⟨17515895903189380290054869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11677263935459586860036579 17515895903189380290054869)
                  ·
                    refine ⟨410528810231001100548161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17515895903189380290054869 410528810231001100548161)
                    ·
                      rfl

theorem cell22_1199253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1199253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199253 prefixEnd_1199253 := by exact prefixLift 1199253
  have htrace : WordTrace (prefixWord ++ tailWord_1199253) baseStart_1199253 baseEnd_1199253 := by
    simpa [prefixWord, tailWord_1199253, baseEnd_1199253] using wordTrace_append hprefix tailTrace_1199253
  have hstable : (prefixWord ++ tailWord_1199253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199253).length < 2 ^ (prefixWord ++ tailWord_1199253).sum := by decide
  have hdescent : baseEnd_1199253 < baseStart_1199253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199283 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 8]
def baseStart_1199283 : Nat := 118140960795 + 1199283 * 2 ^ 59
def prefixEnd_1199283 : Nat := 4983230072969 + 3 ^ 40 * 1199283 * 2
def baseEnd_1199283 : Nat := 136846359948030340766023

theorem tailTrace_1199283 : CollatzResearch.WordTrace tailWord_1199283 prefixEnd_1199283 136846359948030340766023 := by
  unfold tailWord_1199283
  simp only [CollatzResearch.WordTrace]
  refine ⟨43741444514209987074858503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29160963009473324716572335 43741444514209987074858503)
  ·
    refine ⟨65612166771314980612287755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43741444514209987074858503 65612166771314980612287755)
    ·
      refine ⟨98418250156972470918431633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65612166771314980612287755 98418250156972470918431633)
      ·
        refine ⟨73813687617729353188823725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98418250156972470918431633 73813687617729353188823725)
        ·
          refine ⟨27680132856648507445808897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73813687617729353188823725 27680132856648507445808897)
          ·
            refine ⟨20760099642486380584356673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27680132856648507445808897 20760099642486380584356673)
            ·
              refine ⟨15570074731864785438267505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20760099642486380584356673 15570074731864785438267505)
              ·
                refine ⟨11677556048898589078700629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15570074731864785438267505 11677556048898589078700629)
                ·
                  refine ⟨136846359948030340766023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11677556048898589078700629 136846359948030340766023)
                  ·
                    rfl

theorem cell22_1199283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_1199283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199283 prefixEnd_1199283 := by exact prefixLift 1199283
  have htrace : WordTrace (prefixWord ++ tailWord_1199283) baseStart_1199283 baseEnd_1199283 := by
    simpa [prefixWord, tailWord_1199283, baseEnd_1199283] using wordTrace_append hprefix tailTrace_1199283
  have hstable : (prefixWord ++ tailWord_1199283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199283).length < 2 ^ (prefixWord ++ tailWord_1199283).sum := by decide
  have hdescent : baseEnd_1199283 < baseStart_1199283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199377 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_1199377 : Nat := 118140960795 + 1199377 * 2 ^ 59
def prefixEnd_1199377 : Nat := 4983230072969 + 3 ^ 40 * 1199377 * 2
def baseEnd_1199377 : Nat := 410571257965106110447781

theorem tailTrace_1199377 : CollatzResearch.WordTrace tailWord_1199377 prefixEnd_1199377 410571257965106110447781 := by
  unfold tailWord_1199377
  simp only [CollatzResearch.WordTrace]
  refine ⟨43744872975869441128780385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29163248650579627419186923 43744872975869441128780385)
  ·
    refine ⟨32808654731902080846585289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43744872975869441128780385 32808654731902080846585289)
    ·
      refine ⟨24606491048926560634938967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32808654731902080846585289 24606491048926560634938967)
      ·
        refine ⟨36909736573389840952408451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24606491048926560634938967 36909736573389840952408451)
        ·
          refine ⟨55364604860084761428612677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36909736573389840952408451 55364604860084761428612677)
          ·
            refine ⟨10380863411265892767864877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55364604860084761428612677 10380863411265892767864877)
            ·
              refine ⟨3892823779224709787949329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10380863411265892767864877 3892823779224709787949329)
              ·
                refine ⟨2919617834418532340961997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892823779224709787949329 2919617834418532340961997)
                ·
                  refine ⟨1094856687906949627860749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2919617834418532340961997 1094856687906949627860749)
                  ·
                    refine ⟨410571257965106110447781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1094856687906949627860749 410571257965106110447781)
                    ·
                      rfl

theorem cell22_1199377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_1199377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199377 prefixEnd_1199377 := by exact prefixLift 1199377
  have htrace : WordTrace (prefixWord ++ tailWord_1199377) baseStart_1199377 baseEnd_1199377 := by
    simpa [prefixWord, tailWord_1199377, baseEnd_1199377] using wordTrace_append hprefix tailTrace_1199377
  have hstable : (prefixWord ++ tailWord_1199377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199377).length < 2 ^ (prefixWord ++ tailWord_1199377).sum := by decide
  have hdescent : baseEnd_1199377 < baseStart_1199377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199422 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1199422 : Nat := 118140960795 + 1199422 * 2 ^ 59
def prefixEnd_1199422 : Nat := 4983230072969 + 3 ^ 40 * 1199422 * 2
def baseEnd_1199422 : Nat := 410586662384740993072643

theorem tailTrace_1199422 : CollatzResearch.WordTrace tailWord_1199422 prefixEnd_1199422 410586662384740993072643 := by
  unfold tailWord_1199422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468314282588301726771065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29164342840470942542779013 5468314282588301726771065)
  ·
    refine ⟨4101235711941226295078299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5468314282588301726771065 4101235711941226295078299)
    ·
      refine ⟨6151853567911839442617449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101235711941226295078299 6151853567911839442617449)
      ·
        refine ⟨4613890175933879581963087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6151853567911839442617449 4613890175933879581963087)
        ·
          refine ⟨6920835263900819372944631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613890175933879581963087 6920835263900819372944631)
          ·
            refine ⟨10381252895851229059416947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920835263900819372944631 10381252895851229059416947)
            ·
              refine ⟨15571879343776843589125421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381252895851229059416947 15571879343776843589125421)
              ·
                refine ⟨5839454753916316345922033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15571879343776843589125421 5839454753916316345922033)
                ·
                  refine ⟨4379591065437237259441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839454753916316345922033 4379591065437237259441525)
                  ·
                    refine ⟨410586662384740993072643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4379591065437237259441525 410586662384740993072643)
                    ·
                      rfl

theorem cell22_1199422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1199422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199422 prefixEnd_1199422 := by exact prefixLift 1199422
  have htrace : WordTrace (prefixWord ++ tailWord_1199422) baseStart_1199422 baseEnd_1199422 := by
    simpa [prefixWord, tailWord_1199422, baseEnd_1199422] using wordTrace_append hprefix tailTrace_1199422
  have hstable : (prefixWord ++ tailWord_1199422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199422).length < 2 ^ (prefixWord ++ tailWord_1199422).sum := by decide
  have hdescent : baseEnd_1199422 < baseStart_1199422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199430 : List Nat := [6, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1199430 : Nat := 118140960795 + 1199430 * 2 ^ 59
def prefixEnd_1199430 : Nat := 4983230072969 + 3 ^ 40 * 1199430 * 2
def baseEnd_1199430 : Nat := 45621044549803515430291

theorem tailTrace_1199430 : CollatzResearch.WordTrace tailWord_1199430 prefixEnd_1199430 45621044549803515430291 := by
  unfold tailWord_1199430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1367087688896169724389367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29164537363118287453639829 1367087688896169724389367)
  ·
    refine ⟨2050631533344254586584051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1367087688896169724389367 2050631533344254586584051)
    ·
      refine ⟨3075947300016381879876077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2050631533344254586584051 3075947300016381879876077)
      ·
        refine ⟨1153480237506143204953529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3075947300016381879876077 1153480237506143204953529)
        ·
          refine ⟨865110178129607403715147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153480237506143204953529 865110178129607403715147)
          ·
            refine ⟨1297665267194411105572721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865110178129607403715147 1297665267194411105572721)
            ·
              refine ⟨973248950395808329179541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297665267194411105572721 973248950395808329179541)
              ·
                refine ⟨45621044549803515430291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 973248950395808329179541 45621044549803515430291)
                ·
                  rfl

theorem cell22_1199430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1199430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199430 prefixEnd_1199430 := by exact prefixLift 1199430
  have htrace : WordTrace (prefixWord ++ tailWord_1199430) baseStart_1199430 baseEnd_1199430 := by
    simpa [prefixWord, tailWord_1199430, baseEnd_1199430] using wordTrace_append hprefix tailTrace_1199430
  have hstable : (prefixWord ++ tailWord_1199430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199430).length < 2 ^ (prefixWord ++ tailWord_1199430).sum := by decide
  have hdescent : baseEnd_1199430 < baseStart_1199430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199465 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_1199465 : Nat := 118140960795 + 1199465 * 2 ^ 59
def prefixEnd_1199465 : Nat := 4983230072969 + 3 ^ 40 * 1199465 * 2
def baseEnd_1199465 : Nat := 410601382163503214247511

theorem tailTrace_1199465 : CollatzResearch.WordTrace tailWord_1199465 prefixEnd_1199465 410601382163503214247511 := by
  unfold tailWord_1199465
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748082599550632157983849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165388399700421438655899 43748082599550632157983849)
  ·
    refine ⟨32811061949662974118487887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43748082599550632157983849 32811061949662974118487887)
    ·
      refine ⟨49216592924494461177731831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32811061949662974118487887 49216592924494461177731831)
      ·
        refine ⟨73824889386741691766597747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49216592924494461177731831 73824889386741691766597747)
        ·
          refine ⟨110737334080112537649896621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73824889386741691766597747 110737334080112537649896621)
          ·
            refine ⟨41526500280042201618711233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110737334080112537649896621 41526500280042201618711233)
            ·
              refine ⟨31144875210031651214033425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41526500280042201618711233 31144875210031651214033425)
              ·
                refine ⟨23358656407523738410525069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31144875210031651214033425 23358656407523738410525069)
                ·
                  refine ⟨8759496152821401903946901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23358656407523738410525069 8759496152821401903946901)
                  ·
                    refine ⟨410601382163503214247511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8759496152821401903946901 410601382163503214247511)
                    ·
                      rfl

theorem cell22_1199465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_1199465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199465 prefixEnd_1199465 := by exact prefixLift 1199465
  have htrace : WordTrace (prefixWord ++ tailWord_1199465) baseStart_1199465 baseEnd_1199465 := by
    simpa [prefixWord, tailWord_1199465, baseEnd_1199465] using wordTrace_append hprefix tailTrace_1199465
  have hstable : (prefixWord ++ tailWord_1199465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199465).length < 2 ^ (prefixWord ++ tailWord_1199465).sum := by decide
  have hdescent : baseEnd_1199465 < baseStart_1199465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199469 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1199469 : Nat := 118140960795 + 1199469 * 2 ^ 59
def prefixEnd_1199469 : Nat := 4983230072969 + 3 ^ 40 * 1199469 * 2
def baseEnd_1199469 : Nat := 136867583815082845715833

theorem tailTrace_1199469 : CollatzResearch.WordTrace tailWord_1199469 prefixEnd_1199469 136867583815082845715833 := by
  unfold tailWord_1199469
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748228491536140841129461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165485661024093894086307 43748228491536140841129461)
  ·
    refine ⟨4101396421081513203855887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43748228491536140841129461 4101396421081513203855887)
    ·
      refine ⟨6152094631622269805783831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101396421081513203855887 6152094631622269805783831)
      ·
        refine ⟨9228141947433404708675747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152094631622269805783831 9228141947433404708675747)
        ·
          refine ⟨13842212921150107063013621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228141947433404708675747 13842212921150107063013621)
          ·
            refine ⟨1297707461357822537157527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13842212921150107063013621 1297707461357822537157527)
            ·
              refine ⟨1946561192036733805736291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297707461357822537157527 1946561192036733805736291)
              ·
                refine ⟨2919841788055100708604437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946561192036733805736291 2919841788055100708604437)
                ·
                  refine ⟨136867583815082845715833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2919841788055100708604437 136867583815082845715833)
                  ·
                    rfl

theorem cell22_1199469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1199469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199469 prefixEnd_1199469 := by exact prefixLift 1199469
  have htrace : WordTrace (prefixWord ++ tailWord_1199469) baseStart_1199469 baseEnd_1199469 := by
    simpa [prefixWord, tailWord_1199469, baseEnd_1199469] using wordTrace_append hprefix tailTrace_1199469
  have hstable : (prefixWord ++ tailWord_1199469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199469).length < 2 ^ (prefixWord ++ tailWord_1199469).sum := by decide
  have hdescent : baseEnd_1199469 < baseStart_1199469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199484 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1199484 : Nat := 118140960795 + 1199484 * 2 ^ 59
def prefixEnd_1199484 : Nat := 4983230072969 + 3 ^ 40 * 1199484 * 2
def baseEnd_1199484 : Nat := 410607886251793498022453

theorem tailTrace_1199484 : CollatzResearch.WordTrace tailWord_1199484 prefixEnd_1199484 410607886251793498022453 := by
  unfold tailWord_1199484
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874387793240899201462753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29165850390987865601950337 21874387793240899201462753)
  ·
    refine ⟨16405790844930674401097065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21874387793240899201462753 16405790844930674401097065)
    ·
      refine ⟨12304343133698005800822799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16405790844930674401097065 12304343133698005800822799)
      ·
        refine ⟨18456514700547008701234199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304343133698005800822799 18456514700547008701234199)
        ·
          refine ⟨27684772050820513051851299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18456514700547008701234199 27684772050820513051851299)
          ·
            refine ⟨41527158076230769577776949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27684772050820513051851299 41527158076230769577776949)
            ·
              refine ⟨3893171069646634647916589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41527158076230769577776949 3893171069646634647916589)
              ·
                refine ⟨1459939151117487992968721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3893171069646634647916589 1459939151117487992968721)
                ·
                  refine ⟨1094954363338115994726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459939151117487992968721 1094954363338115994726541)
                  ·
                    refine ⟨410607886251793498022453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1094954363338115994726541 410607886251793498022453)
                    ·
                      rfl

theorem cell22_1199484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1199484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199484 prefixEnd_1199484 := by exact prefixLift 1199484
  have htrace : WordTrace (prefixWord ++ tailWord_1199484) baseStart_1199484 baseEnd_1199484 := by
    simpa [prefixWord, tailWord_1199484, baseEnd_1199484] using wordTrace_append hprefix tailTrace_1199484
  have hstable : (prefixWord ++ tailWord_1199484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199484).length < 2 ^ (prefixWord ++ tailWord_1199484).sum := by decide
  have hdescent : baseEnd_1199484 < baseStart_1199484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199527 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1199527 : Nat := 118140960795 + 1199527 * 2 ^ 59
def prefixEnd_1199527 : Nat := 4983230072969 + 3 ^ 40 * 1199527 * 2
def baseEnd_1199527 : Nat := 410622606030555719197321

theorem tailTrace_1199527 : CollatzResearch.WordTrace tailWord_1199527 prefixEnd_1199527 410622606030555719197321 := by
  unfold tailWord_1199527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750343925326016746740835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29166895950217344497827223 43750343925326016746740835)
  ·
    refine ⟨65625515887989025120111253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43750343925326016746740835 65625515887989025120111253)
    ·
      refine ⟨3076196057249485552505215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65625515887989025120111253 3076196057249485552505215)
      ·
        refine ⟨4614294085874228328757823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076196057249485552505215 4614294085874228328757823)
        ·
          refine ⟨6921441128811342493136735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614294085874228328757823 6921441128811342493136735)
          ·
            refine ⟨10382161693217013739705103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6921441128811342493136735 10382161693217013739705103)
            ·
              refine ⟨15573242539825520609557655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10382161693217013739705103 15573242539825520609557655)
              ·
                refine ⟨23359863809738280914336483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15573242539825520609557655 23359863809738280914336483)
                ·
                  refine ⟨35039795714607421371504725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23359863809738280914336483 35039795714607421371504725)
                  ·
                    refine ⟨410622606030555719197321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35039795714607421371504725 410622606030555719197321)
                    ·
                      rfl

theorem cell22_1199527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1199527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199527 prefixEnd_1199527 := by exact prefixLift 1199527
  have htrace : WordTrace (prefixWord ++ tailWord_1199527) baseStart_1199527 baseEnd_1199527 := by
    simpa [prefixWord, tailWord_1199527, baseEnd_1199527] using wordTrace_append hprefix tailTrace_1199527
  have hstable : (prefixWord ++ tailWord_1199527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199527).length < 2 ^ (prefixWord ++ tailWord_1199527).sum := by decide
  have hdescent : baseEnd_1199527 < baseStart_1199527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199606 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1199606 : Nat := 118140960795 + 1199606 * 2 ^ 59
def prefixEnd_1199606 : Nat := 4983230072969 + 3 ^ 40 * 1199606 * 2
def baseEnd_1199606 : Nat := 410649649345025846472079

theorem tailTrace_1199606 : CollatzResearch.WordTrace tailWord_1199606 prefixEnd_1199606 410649649345025846472079 := by
  unfold tailWord_1199606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734576580752488327429167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29168816861359875492577781 2734576580752488327429167)
  ·
    refine ⟨4101864871128732491143751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734576580752488327429167 4101864871128732491143751)
    ·
      refine ⟨6152797306693098736715627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101864871128732491143751 6152797306693098736715627)
      ·
        refine ⟨9229195960039648105073441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152797306693098736715627 9229195960039648105073441)
        ·
          refine ⟨6921896970029736078805081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9229195960039648105073441 6921896970029736078805081)
          ·
            refine ⟨5191422727522302059103811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6921896970029736078805081 5191422727522302059103811)
            ·
              refine ⟨7787134091283453088655717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191422727522302059103811 7787134091283453088655717)
              ·
                refine ⟨1460087642115647454122947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7787134091283453088655717 1460087642115647454122947)
                ·
                  refine ⟨2190131463173471181184421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460087642115647454122947 2190131463173471181184421)
                  ·
                    refine ⟨410649649345025846472079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190131463173471181184421 410649649345025846472079)
                    ·
                      rfl

theorem cell22_1199606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1199606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199606 prefixEnd_1199606 := by exact prefixLift 1199606
  have htrace : WordTrace (prefixWord ++ tailWord_1199606) baseStart_1199606 baseEnd_1199606 := by
    simpa [prefixWord, tailWord_1199606, baseEnd_1199606] using wordTrace_append hprefix tailTrace_1199606
  have hstable : (prefixWord ++ tailWord_1199606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199606).length < 2 ^ (prefixWord ++ tailWord_1199606).sum := by decide
  have hdescent : baseEnd_1199606 < baseStart_1199606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199614 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1199614 : Nat := 118140960795 + 1199614 * 2 ^ 59
def prefixEnd_1199614 : Nat := 4983230072969 + 3 ^ 40 * 1199614 * 2
def baseEnd_1199614 : Nat := 410652387908516492272055

theorem tailTrace_1199614 : CollatzResearch.WordTrace tailWord_1199614 prefixEnd_1199614 410652387908516492272055 := by
  unfold tailWord_1199614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469189634501353825644737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29169011384007220403438597 5469189634501353825644737)
  ·
    refine ⟨4101892225876015369233553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5469189634501353825644737 4101892225876015369233553)
    ·
      refine ⟨3076419169407011526925165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4101892225876015369233553 3076419169407011526925165)
      ·
        refine ⟨1153657188527629322596937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3076419169407011526925165 1153657188527629322596937)
        ·
          refine ⟨865242891395721991947703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153657188527629322596937 865242891395721991947703)
          ·
            refine ⟨1297864337093582987921555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865242891395721991947703 1297864337093582987921555)
            ·
              refine ⟨1946796505640374481882333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297864337093582987921555 1946796505640374481882333)
              ·
                refine ⟨730048689615140430705875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1946796505640374481882333 730048689615140430705875)
                ·
                  refine ⟨1095073034422710646058813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730048689615140430705875 1095073034422710646058813)
                  ·
                    refine ⟨410652387908516492272055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095073034422710646058813 410652387908516492272055)
                    ·
                      rfl

theorem cell22_1199614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1199614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199614 prefixEnd_1199614 := by exact prefixLift 1199614
  have htrace : WordTrace (prefixWord ++ tailWord_1199614) baseStart_1199614 baseEnd_1199614 := by
    simpa [prefixWord, tailWord_1199614, baseEnd_1199614] using wordTrace_append hprefix tailTrace_1199614
  have hstable : (prefixWord ++ tailWord_1199614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199614).length < 2 ^ (prefixWord ++ tailWord_1199614).sum := by decide
  have hdescent : baseEnd_1199614 < baseStart_1199614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199649 : List Nat := [1, 2, 3, 2, 2, 3, 2, 7]
def baseStart_1199649 : Nat := 118140960795 + 1199649 * 2 ^ 59
def prefixEnd_1199649 : Nat := 4983230072969 + 3 ^ 40 * 1199649 * 2
def baseEnd_1199649 : Nat := 45629374347087563071883

theorem tailTrace_1199649 : CollatzResearch.WordTrace tailWord_1199649 prefixEnd_1199649 45629374347087563071883 := by
  unfold tailWord_1199649
  simp only [CollatzResearch.WordTrace]
  refine ⟨43754793630884031582682001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29169862420589354388454667 43754793630884031582682001)
  ·
    refine ⟨32816095223163023687011501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43754793630884031582682001 32816095223163023687011501)
    ·
      refine ⟨12306035708686133882629313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32816095223163023687011501 12306035708686133882629313)
      ·
        refine ⟨9229526781514600411971985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12306035708686133882629313 9229526781514600411971985)
        ·
          refine ⟨6922145086135950308978989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9229526781514600411971985 6922145086135950308978989)
          ·
            refine ⟨2595804407300981365867121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6922145086135950308978989 2595804407300981365867121)
            ·
              refine ⟨1946853305475736024400341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595804407300981365867121 1946853305475736024400341)
              ·
                refine ⟨45629374347087563071883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1946853305475736024400341 45629374347087563071883)
                ·
                  rfl

theorem cell22_1199649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 7].length) (baseStart_1199649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199649 prefixEnd_1199649 := by exact prefixLift 1199649
  have htrace : WordTrace (prefixWord ++ tailWord_1199649) baseStart_1199649 baseEnd_1199649 := by
    simpa [prefixWord, tailWord_1199649, baseEnd_1199649] using wordTrace_append hprefix tailTrace_1199649
  have hstable : (prefixWord ++ tailWord_1199649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199649).length < 2 ^ (prefixWord ++ tailWord_1199649).sum := by decide
  have hdescent : baseEnd_1199649 < baseStart_1199649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199664 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_1199664 : Nat := 118140960795 + 1199664 * 2 ^ 59
def prefixEnd_1199664 : Nat := 4983230072969 + 3 ^ 40 * 1199664 * 2
def baseEnd_1199664 : Nat := 410669503930333028521901

theorem tailTrace_1199664 : CollatzResearch.WordTrace tailWord_1199664 prefixEnd_1199664 410669503930333028521901 := by
  unfold tailWord_1199664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21877670362914844572239023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29170227150553126096318697 21877670362914844572239023)
  ·
    refine ⟨32816505544372266858358535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21877670362914844572239023 32816505544372266858358535)
    ·
      refine ⟨49224758316558400287537803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32816505544372266858358535 49224758316558400287537803)
      ·
        refine ⟨73837137474837600431306705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49224758316558400287537803 73837137474837600431306705)
        ·
          refine ⟨55377853106128200323480029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73837137474837600431306705 55377853106128200323480029)
          ·
            refine ⟨20766694914798075121305011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55377853106128200323480029 20766694914798075121305011)
            ·
              refine ⟨31150042372197112681957517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20766694914798075121305011 31150042372197112681957517)
              ·
                refine ⟨11681265889573917255734069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31150042372197112681957517 11681265889573917255734069)
                ·
                  refine ⟨1095118677147554742725069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11681265889573917255734069 1095118677147554742725069)
                  ·
                    refine ⟨410669503930333028521901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095118677147554742725069 410669503930333028521901)
                    ·
                      rfl

theorem cell22_1199664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_1199664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199664 prefixEnd_1199664 := by exact prefixLift 1199664
  have htrace : WordTrace (prefixWord ++ tailWord_1199664) baseStart_1199664 baseEnd_1199664 := by
    simpa [prefixWord, tailWord_1199664, baseEnd_1199664] using wordTrace_append hprefix tailTrace_1199664
  have hstable : (prefixWord ++ tailWord_1199664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199664).length < 2 ^ (prefixWord ++ tailWord_1199664).sum := by decide
  have hdescent : baseEnd_1199664 < baseStart_1199664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199756 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_1199756 : Nat := 118140960795 + 1199756 * 2 ^ 59
def prefixEnd_1199756 : Nat := 4983230072969 + 3 ^ 40 * 1199756 * 2
def baseEnd_1199756 : Nat := 136900332470158485073873

theorem tailTrace_1199756 : CollatzResearch.WordTrace tailWord_1199756 prefixEnd_1199756 136900332470158485073873 := by
  unfold tailWord_1199756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21879348120748194428413561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29172464160997592571218081 21879348120748194428413561)
  ·
    refine ⟨16409511090561145821310171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21879348120748194428413561 16409511090561145821310171)
    ·
      refine ⟨24614266635841718731965257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16409511090561145821310171 24614266635841718731965257)
      ·
        refine ⟨18460699976881289048973943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24614266635841718731965257 18460699976881289048973943)
        ·
          refine ⟨27691049965321933573460915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18460699976881289048973943 27691049965321933573460915)
          ·
            refine ⟨41536574947982900360191373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27691049965321933573460915 41536574947982900360191373)
            ·
              refine ⟨15576215605493587635071765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41536574947982900360191373 15576215605493587635071765)
              ·
                refine ⟨730135106507511920393989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15576215605493587635071765 730135106507511920393989)
                ·
                  refine ⟨136900332470158485073873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730135106507511920393989 136900332470158485073873)
                  ·
                    rfl

theorem cell22_1199756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_1199756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199756 prefixEnd_1199756 := by exact prefixLift 1199756
  have htrace : WordTrace (prefixWord ++ tailWord_1199756) baseStart_1199756 baseEnd_1199756 := by
    simpa [prefixWord, tailWord_1199756, baseEnd_1199756] using wordTrace_append hprefix tailTrace_1199756
  have hstable : (prefixWord ++ tailWord_1199756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199756).length < 2 ^ (prefixWord ++ tailWord_1199756).sum := by decide
  have hdescent : baseEnd_1199756 < baseStart_1199756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199769 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_1199769 : Nat := 118140960795 + 1199769 * 2 ^ 59
def prefixEnd_1199769 : Nat := 4983230072969 + 3 ^ 40 * 1199769 * 2
def baseEnd_1199769 : Nat := 410705447576147754646579

theorem tailTrace_1199769 : CollatzResearch.WordTrace tailWord_1199769 prefixEnd_1199769 410705447576147754646579 := by
  unfold tailWord_1199769
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759170390449292077050361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29172780260299528051366907 43759170390449292077050361)
  ·
    refine ⟨32819377792836969057787771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43759170390449292077050361 32819377792836969057787771)
    ·
      refine ⟨49229066689255453586681657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32819377792836969057787771 49229066689255453586681657)
      ·
        refine ⟨36921800016941590190011243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49229066689255453586681657 36921800016941590190011243)
        ·
          refine ⟨55382700025412385285016865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36921800016941590190011243 55382700025412385285016865)
          ·
            refine ⟨41537025019059288963762649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55382700025412385285016865 41537025019059288963762649)
            ·
              refine ⟨31152768764294466722821987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41537025019059288963762649 31152768764294466722821987)
              ·
                refine ⟨46729153146441700084232981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31152768764294466722821987 46729153146441700084232981)
                ·
                  refine ⟨2190429053739454691448421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46729153146441700084232981 2190429053739454691448421)
                  ·
                    refine ⟨410705447576147754646579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190429053739454691448421 410705447576147754646579)
                    ·
                      rfl

theorem cell22_1199769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_1199769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199769 prefixEnd_1199769 := by exact prefixLift 1199769
  have htrace : WordTrace (prefixWord ++ tailWord_1199769) baseStart_1199769 baseEnd_1199769 := by
    simpa [prefixWord, tailWord_1199769, baseEnd_1199769] using wordTrace_append hprefix tailTrace_1199769
  have hstable : (prefixWord ++ tailWord_1199769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199769).length < 2 ^ (prefixWord ++ tailWord_1199769).sum := by decide
  have hdescent : baseEnd_1199769 < baseStart_1199769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199775 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 1, 4]
def baseStart_1199775 : Nat := 118140960795 + 1199775 * 2 ^ 59
def prefixEnd_1199775 : Nat := 4983230072969 + 3 ^ 40 * 1199775 * 2
def baseEnd_1199775 : Nat := 410707501498765738996561

theorem tailTrace_1199775 : CollatzResearch.WordTrace tailWord_1199775 prefixEnd_1199775 410707501498765738996561 := by
  unfold tailWord_1199775
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759389228427555101768779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29172926152285036734512519 43759389228427555101768779)
  ·
    refine ⟨65639083842641332652653169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43759389228427555101768779 65639083842641332652653169)
    ·
      refine ⟨49229312881980999489489877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65639083842641332652653169 49229312881980999489489877)
      ·
        refine ⟨1153812020671429675534919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49229312881980999489489877 1153812020671429675534919)
        ·
          refine ⟨1730718031007144513302379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153812020671429675534919 1730718031007144513302379)
          ·
            refine ⟨2596077046510716769953569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730718031007144513302379 2596077046510716769953569)
            ·
              refine ⟨1947057784883037577465177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596077046510716769953569 1947057784883037577465177)
              ·
                refine ⟨1460293338662278183098883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947057784883037577465177 1460293338662278183098883)
                ·
                  refine ⟨2190440007993417274648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460293338662278183098883 2190440007993417274648325)
                  ·
                    refine ⟨410707501498765738996561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2190440007993417274648325 410707501498765738996561)
                    ·
                      rfl

theorem cell22_1199775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_1199775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199775 prefixEnd_1199775 := by exact prefixLift 1199775
  have htrace : WordTrace (prefixWord ++ tailWord_1199775) baseStart_1199775 baseEnd_1199775 := by
    simpa [prefixWord, tailWord_1199775, baseEnd_1199775] using wordTrace_append hprefix tailTrace_1199775
  have hstable : (prefixWord ++ tailWord_1199775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199775).length < 2 ^ (prefixWord ++ tailWord_1199775).sum := by decide
  have hdescent : baseEnd_1199775 < baseStart_1199775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199953 : List Nat := [1, 2, 2, 1, 5, 1, 4, 6]
def baseStart_1199953 : Nat := 118140960795 + 1199953 * 2 ^ 59
def prefixEnd_1199953 : Nat := 4983230072969 + 3 ^ 40 * 1199953 * 2
def baseEnd_1199953 : Nat := 45640937170714734227335

theorem tailTrace_1199953 : CollatzResearch.WordTrace tailWord_1199953 prefixEnd_1199953 45640937170714734227335 := by
  unfold tailWord_1199953
  simp only [CollatzResearch.WordTrace]
  refine ⟨43765881421782691501748513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29177254281188461001165675 43765881421782691501748513)
  ·
    refine ⟨32824411066337018626311385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43765881421782691501748513 32824411066337018626311385)
    ·
      refine ⟨24618308299752763969733539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32824411066337018626311385 24618308299752763969733539)
      ·
        refine ⟨36927462449629145954600309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24618308299752763969733539 36927462449629145954600309)
        ·
          refine ⟨3461949604652732433243779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36927462449629145954600309 3461949604652732433243779)
          ·
            refine ⟨5192924406979098649865669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461949604652732433243779 5192924406979098649865669)
            ·
              refine ⟨973673326308580996849813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5192924406979098649865669 973673326308580996849813)
              ·
                refine ⟨45640937170714734227335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 973673326308580996849813 45640937170714734227335)
                ·
                  rfl

theorem cell22_1199953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 6].length) (baseStart_1199953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1199953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1199953 prefixEnd_1199953 := by exact prefixLift 1199953
  have htrace : WordTrace (prefixWord ++ tailWord_1199953) baseStart_1199953 baseEnd_1199953 := by
    simpa [prefixWord, tailWord_1199953, baseEnd_1199953] using wordTrace_append hprefix tailTrace_1199953
  have hstable : (prefixWord ++ tailWord_1199953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199953).length < 2 ^ (prefixWord ++ tailWord_1199953).sum := by decide
  have hdescent : baseEnd_1199953 < baseStart_1199953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200109 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1200109 : Nat := 118140960795 + 1200109 * 2 ^ 59
def prefixEnd_1200109 : Nat := 4983230072969 + 3 ^ 40 * 1200109 * 2
def baseEnd_1200109 : Nat := 410821836524500201145537

theorem tailTrace_1200109 : CollatzResearch.WordTrace tailWord_1200109 prefixEnd_1200109 410821836524500201145537 := by
  unfold tailWord_1200109
  simp only [CollatzResearch.WordTrace]
  refine ⟨43771571209217530144427381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29181047472811686762951587 43771571209217530144427381)
  ·
    refine ⟨4103584800864143451040067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43771571209217530144427381 4103584800864143451040067)
    ·
      refine ⟨6155377201296215176560101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103584800864143451040067 6155377201296215176560101)
      ·
        refine ⟨1154133225243040345605019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6155377201296215176560101 1154133225243040345605019)
        ·
          refine ⟨1731199837864560518407529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154133225243040345605019 1731199837864560518407529)
          ·
            refine ⟨1298399878398420388805647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731199837864560518407529 1298399878398420388805647)
            ·
              refine ⟨1947599817597630583208471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298399878398420388805647 1947599817597630583208471)
              ·
                refine ⟨2921399726396445874812707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947599817597630583208471 2921399726396445874812707)
                ·
                  refine ⟨4382099589594668812219061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921399726396445874812707 4382099589594668812219061)
                  ·
                    refine ⟨410821836524500201145537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4382099589594668812219061 410821836524500201145537)
                    ·
                      rfl

theorem cell22_1200109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1200109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200109 prefixEnd_1200109 := by exact prefixLift 1200109
  have htrace : WordTrace (prefixWord ++ tailWord_1200109) baseStart_1200109 baseEnd_1200109 := by
    simpa [prefixWord, tailWord_1200109, baseEnd_1200109] using wordTrace_append hprefix tailTrace_1200109
  have hstable : (prefixWord ++ tailWord_1200109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200109).length < 2 ^ (prefixWord ++ tailWord_1200109).sum := by decide
  have hdescent : baseEnd_1200109 < baseStart_1200109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200120 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1200120 : Nat := 118140960795 + 1200120 * 2 ^ 59
def prefixEnd_1200120 : Nat := 4983230072969 + 3 ^ 40 * 1200120 * 2
def baseEnd_1200120 : Nat := 410825602049299839120503

theorem tailTrace_1200120 : CollatzResearch.WordTrace tailWord_1200120 prefixEnd_1200120 410825602049299839120503 := by
  unfold tailWord_1200120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21885986206088839511538907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29181314941451786015385209 21885986206088839511538907)
  ·
    refine ⟨32828979309133259267308361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21885986206088839511538907 32828979309133259267308361)
    ·
      refine ⟨24621734481849944450481271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32828979309133259267308361 24621734481849944450481271)
      ·
        refine ⟨36932601722774916675721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24621734481849944450481271 36932601722774916675721907)
        ·
          refine ⟨55398902584162375013582861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36932601722774916675721907 55398902584162375013582861)
          ·
            refine ⟨20774588469060890630093573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55398902584162375013582861 20774588469060890630093573)
            ·
              refine ⟨3895235337948916993142545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20774588469060890630093573 3895235337948916993142545)
              ·
                refine ⟨2921426503461687744856909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895235337948916993142545 2921426503461687744856909)
                ·
                  refine ⟨1095534938798132904321341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2921426503461687744856909 1095534938798132904321341)
                  ·
                    refine ⟨410825602049299839120503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095534938798132904321341 410825602049299839120503)
                    ·
                      rfl

theorem cell22_1200120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1200120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200120 prefixEnd_1200120 := by exact prefixLift 1200120
  have htrace : WordTrace (prefixWord ++ tailWord_1200120) baseStart_1200120 baseEnd_1200120 := by
    simpa [prefixWord, tailWord_1200120, baseEnd_1200120] using wordTrace_append hprefix tailTrace_1200120
  have hstable : (prefixWord ++ tailWord_1200120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200120).length < 2 ^ (prefixWord ++ tailWord_1200120).sum := by decide
  have hdescent : baseEnd_1200120 < baseStart_1200120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200133 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 7]
def baseStart_1200133 : Nat := 118140960795 + 1200133 * 2 ^ 59
def prefixEnd_1200133 : Nat := 4983230072969 + 3 ^ 40 * 1200133 * 2
def baseEnd_1200133 : Nat := 136943350738324046181821

theorem tailTrace_1200133 : CollatzResearch.WordTrace tailWord_1200133 prefixEnd_1200133 136943350738324046181821 := by
  unfold tailWord_1200133
  simp only [CollatzResearch.WordTrace]
  refine ⟨43772446561130582243301053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29181631040753721495534035 43772446561130582243301053)
  ·
    refine ⟨16414667460423968341237895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43772446561130582243301053 16414667460423968341237895)
    ·
      refine ⟨24622001190635952511856843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16414667460423968341237895 24622001190635952511856843)
      ·
        refine ⟨36933001785953928767785265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24622001190635952511856843 36933001785953928767785265)
        ·
          refine ⟨27699751339465446575838949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36933001785953928767785265 27699751339465446575838949)
          ·
            refine ⟨5193703376149771232969803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27699751339465446575838949 5193703376149771232969803)
            ·
              refine ⟨7790555064224656849454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193703376149771232969803 7790555064224656849454705)
              ·
                refine ⟨5842916298168492637091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7790555064224656849454705 5842916298168492637091029)
                ·
                  refine ⟨136943350738324046181821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5842916298168492637091029 136943350738324046181821)
                  ·
                    rfl

theorem cell22_1200133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_1200133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200133 prefixEnd_1200133 := by exact prefixLift 1200133
  have htrace : WordTrace (prefixWord ++ tailWord_1200133) baseStart_1200133 baseEnd_1200133 := by
    simpa [prefixWord, tailWord_1200133, baseEnd_1200133] using wordTrace_append hprefix tailTrace_1200133
  have hstable : (prefixWord ++ tailWord_1200133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200133).length < 2 ^ (prefixWord ++ tailWord_1200133).sum := by decide
  have hdescent : baseEnd_1200133 < baseStart_1200133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200141 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1200141 : Nat := 118140960795 + 1200141 * 2 ^ 59
def prefixEnd_1200141 : Nat := 4983230072969 + 3 ^ 40 * 1200141 * 2
def baseEnd_1200141 : Nat := 410832790778462784345439

theorem tailTrace_1200141 : CollatzResearch.WordTrace tailWord_1200141 prefixEnd_1200141 410832790778462784345439 := by
  unfold tailWord_1200141
  simp only [CollatzResearch.WordTrace]
  refine ⟨43772738345101599609592277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29181825563401066406394851 43772738345101599609592277)
  ·
    refine ⟨1025923554963318740849819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43772738345101599609592277 1025923554963318740849819)
    ·
      refine ⟨1538885332444978111274729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025923554963318740849819 1538885332444978111274729)
      ·
        refine ⟨1154163999333733583456047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1538885332444978111274729 1154163999333733583456047)
        ·
          refine ⟨1731245999000600375184071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154163999333733583456047 1731245999000600375184071)
          ·
            refine ⟨2596868998500900562776107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731245999000600375184071 2596868998500900562776107)
            ·
              refine ⟨3895303497751350844164161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596868998500900562776107 3895303497751350844164161)
              ·
                refine ⟨2921477623313513133123121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895303497751350844164161 2921477623313513133123121)
                ·
                  refine ⟨2191108217485134849842341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921477623313513133123121 2191108217485134849842341)
                  ·
                    refine ⟨410832790778462784345439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191108217485134849842341 410832790778462784345439)
                    ·
                      rfl

theorem cell22_1200141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1200141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200141 prefixEnd_1200141 := by exact prefixLift 1200141
  have htrace : WordTrace (prefixWord ++ tailWord_1200141) baseStart_1200141 baseEnd_1200141 := by
    simpa [prefixWord, tailWord_1200141, baseEnd_1200141] using wordTrace_append hprefix tailTrace_1200141
  have hstable : (prefixWord ++ tailWord_1200141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200141).length < 2 ^ (prefixWord ++ tailWord_1200141).sum := by decide
  have hdescent : baseEnd_1200141 < baseStart_1200141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200208 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1200208 : Nat := 118140960795 + 1200208 * 2 ^ 59
def prefixEnd_1200208 : Nat := 4983230072969 + 3 ^ 40 * 1200208 * 2
def baseEnd_1200208 : Nat := 410855726247696942920233

theorem tailTrace_1200208 : CollatzResearch.WordTrace tailWord_1200208 prefixEnd_1200208 410855726247696942920233 := by
  unfold tailWord_1200208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21887591017929435026140639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29183454690572580034854185 21887591017929435026140639)
  ·
    refine ⟨32831386526894152539210959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21887591017929435026140639 32831386526894152539210959)
    ·
      refine ⟨49247079790341228808816439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32831386526894152539210959 49247079790341228808816439)
      ·
        refine ⟨73870619685511843213224659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49247079790341228808816439 73870619685511843213224659)
        ·
          refine ⟨110805929528267764819836989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73870619685511843213224659 110805929528267764819836989)
          ·
            refine ⟨41552223573100411807438871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110805929528267764819836989 41552223573100411807438871)
            ·
              refine ⟨62328335359650617711158307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41552223573100411807438871 62328335359650617711158307)
              ·
                refine ⟨93492503039475926566737461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62328335359650617711158307 93492503039475926566737461)
                ·
                  refine ⟨8764922159950868115631637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93492503039475926566737461 8764922159950868115631637)
                  ·
                    refine ⟨410855726247696942920233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8764922159950868115631637 410855726247696942920233)
                    ·
                      rfl

theorem cell22_1200208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1200208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200208 prefixEnd_1200208 := by exact prefixLift 1200208
  have htrace : WordTrace (prefixWord ++ tailWord_1200208) baseStart_1200208 baseEnd_1200208 := by
    simpa [prefixWord, tailWord_1200208, baseEnd_1200208] using wordTrace_append hprefix tailTrace_1200208
  have hstable : (prefixWord ++ tailWord_1200208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200208).length < 2 ^ (prefixWord ++ tailWord_1200208).sum := by decide
  have hdescent : baseEnd_1200208 < baseStart_1200208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200214 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1200214 : Nat := 118140960795 + 1200214 * 2 ^ 59
def prefixEnd_1200214 : Nat := 4983230072969 + 3 ^ 40 * 1200214 * 2
def baseEnd_1200214 : Nat := 410857780170314927270215

theorem tailTrace_1200214 : CollatzResearch.WordTrace tailWord_1200214 prefixEnd_1200214 410857780170314927270215 := by
  unfold tailWord_1200214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735962554614820817312481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29183600582558088717999797 2735962554614820817312481)
  ·
    refine ⟨2051971915961115612984361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2735962554614820817312481 2051971915961115612984361)
    ·
      refine ⟨1538978936970836709738271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2051971915961115612984361 1538978936970836709738271)
      ·
        refine ⟨2308468405456255064607407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1538978936970836709738271 2308468405456255064607407)
        ·
          refine ⟨3462702608184382596911111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308468405456255064607407 3462702608184382596911111)
          ·
            refine ⟨5194053912276573895366667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462702608184382596911111 5194053912276573895366667)
            ·
              refine ⟨7791080868414860843050001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194053912276573895366667 7791080868414860843050001)
              ·
                refine ⟨5843310651311145632287501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7791080868414860843050001 5843310651311145632287501)
                ·
                  refine ⟨2191241494241679612107813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5843310651311145632287501 2191241494241679612107813)
                  ·
                    refine ⟨410857780170314927270215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191241494241679612107813 410857780170314927270215)
                    ·
                      rfl

theorem cell22_1200214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1200214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200214 prefixEnd_1200214 := by exact prefixLift 1200214
  have htrace : WordTrace (prefixWord ++ tailWord_1200214) baseStart_1200214 baseEnd_1200214 := by
    simpa [prefixWord, tailWord_1200214, baseEnd_1200214] using wordTrace_append hprefix tailTrace_1200214
  have hstable : (prefixWord ++ tailWord_1200214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200214).length < 2 ^ (prefixWord ++ tailWord_1200214).sum := by decide
  have hdescent : baseEnd_1200214 < baseStart_1200214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200223 : List Nat := [1, 1, 2, 3, 1, 1, 2, 11]
def baseStart_1200223 : Nat := 118140960795 + 1200223 * 2 ^ 59
def prefixEnd_1200223 : Nat := 4983230072969 + 3 ^ 40 * 1200223 * 2
def baseEnd_1200223 : Nat := 45651206783804655977243

theorem tailTrace_1200223 : CollatzResearch.WordTrace tailWord_1200223 prefixEnd_1200223 45651206783804655977243 := by
  unfold tailWord_1200223
  simp only [CollatzResearch.WordTrace]
  refine ⟨43775729130804527614077323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29183819420536351742718215 43775729130804527614077323)
  ·
    refine ⟨65663593696206791421115985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43775729130804527614077323 65663593696206791421115985)
    ·
      refine ⟨49247695272155093565836989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65663593696206791421115985 49247695272155093565836989)
      ·
        refine ⟨18467885727058160087188871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49247695272155093565836989 18467885727058160087188871)
        ·
          refine ⟨27701828590587240130783307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18467885727058160087188871 27701828590587240130783307)
          ·
            refine ⟨41552742885880860196174961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27701828590587240130783307 41552742885880860196174961)
            ·
              refine ⟨31164557164410645147131221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41552742885880860196174961 31164557164410645147131221)
              ·
                refine ⟨45651206783804655977243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31164557164410645147131221 45651206783804655977243)
                ·
                  rfl

theorem cell22_1200223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 11].length) (baseStart_1200223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200223 prefixEnd_1200223 := by exact prefixLift 1200223
  have htrace : WordTrace (prefixWord ++ tailWord_1200223) baseStart_1200223 baseEnd_1200223 := by
    simpa [prefixWord, tailWord_1200223, baseEnd_1200223] using wordTrace_append hprefix tailTrace_1200223
  have hstable : (prefixWord ++ tailWord_1200223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200223).length < 2 ^ (prefixWord ++ tailWord_1200223).sum := by decide
  have hdescent : baseEnd_1200223 < baseStart_1200223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200227 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 2, 3]
def baseStart_1200227 : Nat := 118140960795 + 1200227 * 2 ^ 59
def prefixEnd_1200227 : Nat := 4983230072969 + 3 ^ 40 * 1200227 * 2
def baseEnd_1200227 : Nat := 410862230335987226695175

theorem tailTrace_1200227 : CollatzResearch.WordTrace tailWord_1200227 prefixEnd_1200227 410862230335987226695175 := by
  unfold tailWord_1200227
  simp only [CollatzResearch.WordTrace]
  refine ⟨43775875022790036297222935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29183916681860024198148623 43775875022790036297222935)
  ·
    refine ⟨65663812534185054445834403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43775875022790036297222935 65663812534185054445834403)
    ·
      refine ⟨98495718801277581668751605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65663812534185054445834403 98495718801277581668751605)
      ·
        refine ⟨9233973637619773281445463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98495718801277581668751605 9233973637619773281445463)
        ·
          refine ⟨13850960456429659922168195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9233973637619773281445463 13850960456429659922168195)
          ·
            refine ⟨20776440684644489883252293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13850960456429659922168195 20776440684644489883252293)
            ·
              refine ⟨3895582628370841853109805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20776440684644489883252293 3895582628370841853109805)
              ·
                refine ⟨1460843485639065694916177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3895582628370841853109805 1460843485639065694916177)
                ·
                  refine ⟨1095632614229299271187133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460843485639065694916177 1095632614229299271187133)
                  ·
                    refine ⟨410862230335987226695175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095632614229299271187133 410862230335987226695175)
                    ·
                      rfl

theorem cell22_1200227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 3].length) (baseStart_1200227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200227 prefixEnd_1200227 := by exact prefixLift 1200227
  have htrace : WordTrace (prefixWord ++ tailWord_1200227) baseStart_1200227 baseEnd_1200227 := by
    simpa [prefixWord, tailWord_1200227, baseEnd_1200227] using wordTrace_append hprefix tailTrace_1200227
  have hstable : (prefixWord ++ tailWord_1200227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200227).length < 2 ^ (prefixWord ++ tailWord_1200227).sum := by decide
  have hdescent : baseEnd_1200227 < baseStart_1200227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200242 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1200242 : Nat := 118140960795 + 1200242 * 2 ^ 59
def prefixEnd_1200242 : Nat := 4983230072969 + 3 ^ 40 * 1200242 * 2
def baseEnd_1200242 : Nat := 410867365142532187570129

theorem tailTrace_1200242 : CollatzResearch.WordTrace tailWord_1200242 prefixEnd_1200242 410867365142532187570129 := by
  unfold tailWord_1200242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944105529433923464754745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29184281411823795906012653 10944105529433923464754745)
  ·
    refine ⟨8208079147075442598566059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10944105529433923464754745 8208079147075442598566059)
    ·
      refine ⟨12312118720613163897849089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8208079147075442598566059 12312118720613163897849089)
      ·
        refine ⟨9234089040459872923386817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12312118720613163897849089 9234089040459872923386817)
        ·
          refine ⟨6925566780344904692540113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234089040459872923386817 6925566780344904692540113)
          ·
            refine ⟨5194175085258678519405085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6925566780344904692540113 5194175085258678519405085)
            ·
              refine ⟨1947815656972004444776907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5194175085258678519405085 1947815656972004444776907)
              ·
                refine ⟨2921723485458006667165361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947815656972004444776907 2921723485458006667165361)
                ·
                  refine ⟨2191292614093505000374021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921723485458006667165361 2191292614093505000374021)
                  ·
                    refine ⟨410867365142532187570129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191292614093505000374021 410867365142532187570129)
                    ·
                      rfl

theorem cell22_1200242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1200242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200242 prefixEnd_1200242 := by exact prefixLift 1200242
  have htrace : WordTrace (prefixWord ++ tailWord_1200242) baseStart_1200242 baseEnd_1200242 := by
    simpa [prefixWord, tailWord_1200242, baseEnd_1200242] using wordTrace_append hprefix tailTrace_1200242
  have hstable : (prefixWord ++ tailWord_1200242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200242).length < 2 ^ (prefixWord ++ tailWord_1200242).sum := by decide
  have hdescent : baseEnd_1200242 < baseStart_1200242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200272 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_1200272 : Nat := 118140960795 + 1200272 * 2 ^ 59
def prefixEnd_1200272 : Nat := 4983230072969 + 3 ^ 40 * 1200272 * 2
def baseEnd_1200272 : Nat := 410877634755622109320037

theorem tailTrace_1200272 : CollatzResearch.WordTrace tailWord_1200272 prefixEnd_1200272 410877634755622109320037 := by
  unfold tailWord_1200272
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888758153813504491305535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29185010871751339321740713 21888758153813504491305535)
  ·
    refine ⟨32833137230720256736958303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21888758153813504491305535 32833137230720256736958303)
    ·
      refine ⟨49249705846080385105437455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32833137230720256736958303 49249705846080385105437455)
      ·
        refine ⟨73874558769120577658156183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49249705846080385105437455 73874558769120577658156183)
        ·
          refine ⟨110811838153680866487234275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73874558769120577658156183 110811838153680866487234275)
          ·
            refine ⟨166217757230521299730851413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110811838153680866487234275 166217757230521299730851413)
            ·
              refine ⟨1947864342545171481220915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 166217757230521299730851413 1947864342545171481220915)
              ·
                refine ⟨2921796513817757221831373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947864342545171481220915 2921796513817757221831373)
                ·
                  refine ⟨1095673692681658958186765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2921796513817757221831373 1095673692681658958186765)
                  ·
                    refine ⟨410877634755622109320037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095673692681658958186765 410877634755622109320037)
                    ·
                      rfl

theorem cell22_1200272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_1200272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200272 prefixEnd_1200272 := by exact prefixLift 1200272
  have htrace : WordTrace (prefixWord ++ tailWord_1200272) baseStart_1200272 baseEnd_1200272 := by
    simpa [prefixWord, tailWord_1200272, baseEnd_1200272] using wordTrace_append hprefix tailTrace_1200272
  have hstable : (prefixWord ++ tailWord_1200272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200272).length < 2 ^ (prefixWord ++ tailWord_1200272).sum := by decide
  have hdescent : baseEnd_1200272 < baseStart_1200272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200308 : List Nat := [2, 5, 3, 1, 2, 1, 8]
def baseStart_1200308 : Nat := 118140960795 + 1200308 * 2 ^ 59
def prefixEnd_1200308 : Nat := 4983230072969 + 3 ^ 40 * 1200308 * 2
def baseEnd_1200308 : Nat := 15218146603382593163701

theorem tailTrace_1200308 : CollatzResearch.WordTrace tailWord_1200308 prefixEnd_1200308 15218146603382593163701 := by
  unfold tailWord_1200308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21889414667748293565460789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29185886223664391420614385 21889414667748293565460789)
  ·
    refine ⟨2052132625101402521761949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21889414667748293565460789 2052132625101402521761949)
    ·
      refine ⟨769549734413025945660731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2052132625101402521761949 769549734413025945660731)
      ·
        refine ⟨1154324601619538918491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769549734413025945660731 1154324601619538918491097)
        ·
          refine ⟨865743451214654188868323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154324601619538918491097 865743451214654188868323)
          ·
            refine ⟨1298615176821981283302485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865743451214654188868323 1298615176821981283302485)
            ·
              refine ⟨15218146603382593163701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1298615176821981283302485 15218146603382593163701)
              ·
                rfl

theorem cell22_1200308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 8].length) (baseStart_1200308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200308 prefixEnd_1200308 := by exact prefixLift 1200308
  have htrace : WordTrace (prefixWord ++ tailWord_1200308) baseStart_1200308 baseEnd_1200308 := by
    simpa [prefixWord, tailWord_1200308, baseEnd_1200308] using wordTrace_append hprefix tailTrace_1200308
  have hstable : (prefixWord ++ tailWord_1200308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200308).length < 2 ^ (prefixWord ++ tailWord_1200308).sum := by decide
  have hdescent : baseEnd_1200308 < baseStart_1200308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200349 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1200349 : Nat := 118140960795 + 1200349 * 2 ^ 59
def prefixEnd_1200349 : Nat := 4983230072969 + 3 ^ 40 * 1200349 * 2
def baseEnd_1200349 : Nat := 410903993429219575144801

theorem tailTrace_1200349 : CollatzResearch.WordTrace tailWord_1200349 prefixEnd_1200349 410903993429219575144801 := by
  unfold tailWord_1200349
  simp only [CollatzResearch.WordTrace]
  refine ⟨43780324728348051133164101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29186883152232034088776067 43780324728348051133164101)
  ·
    refine ⟨8208810886565259587468269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43780324728348051133164101 8208810886565259587468269)
    ·
      refine ⟨3078304082461972345300601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8208810886565259587468269 3078304082461972345300601)
      ·
        refine ⟨2308728061846479258975451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078304082461972345300601 2308728061846479258975451)
        ·
          refine ⟨3463092092769718888463177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308728061846479258975451 3463092092769718888463177)
          ·
            refine ⟨2597319069577289166347383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463092092769718888463177 2597319069577289166347383)
            ·
              refine ⟨3895978604365933749521075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597319069577289166347383 3895978604365933749521075)
              ·
                refine ⟨5843967906548900624281613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895978604365933749521075 5843967906548900624281613)
                ·
                  refine ⟨2191487964955837734105605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5843967906548900624281613 2191487964955837734105605)
                  ·
                    refine ⟨410903993429219575144801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191487964955837734105605 410903993429219575144801)
                    ·
                      rfl

theorem cell22_1200349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1200349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200349 prefixEnd_1200349 := by exact prefixLift 1200349
  have htrace : WordTrace (prefixWord ++ tailWord_1200349) baseStart_1200349 baseEnd_1200349 := by
    simpa [prefixWord, tailWord_1200349, baseEnd_1200349] using wordTrace_append hprefix tailTrace_1200349
  have hstable : (prefixWord ++ tailWord_1200349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200349).length < 2 ^ (prefixWord ++ tailWord_1200349).sum := by decide
  have hdescent : baseEnd_1200349 < baseStart_1200349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200362 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1200362 : Nat := 118140960795 + 1200362 * 2 ^ 59
def prefixEnd_1200362 : Nat := 4983230072969 + 3 ^ 40 * 1200362 * 2
def baseEnd_1200362 : Nat := 410908443594891874569761

theorem tailTrace_1200362 : CollatzResearch.WordTrace tailWord_1200362 prefixEnd_1200362 410908443594891874569761 := by
  unfold tailWord_1200362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10945199719325238588346835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29187199251533969568924893 10945199719325238588346835)
  ·
    refine ⟨16417799578987857882520253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10945199719325238588346835 16417799578987857882520253)
    ·
      refine ⟨6156674842120446705945095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16417799578987857882520253 6156674842120446705945095)
      ·
        refine ⟨9235012263180670058917643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6156674842120446705945095 9235012263180670058917643)
        ·
          refine ⟨13852518394771005088376465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9235012263180670058917643 13852518394771005088376465)
          ·
            refine ⟨10389388796078253816282349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13852518394771005088376465 10389388796078253816282349)
            ·
              refine ⟨3896020798529345181105881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10389388796078253816282349 3896020798529345181105881)
              ·
                refine ⟨2922015598897008885829411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896020798529345181105881 2922015598897008885829411)
                ·
                  refine ⟨4383023398345513328744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922015598897008885829411 4383023398345513328744117)
                  ·
                    refine ⟨410908443594891874569761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4383023398345513328744117 410908443594891874569761)
                    ·
                      rfl

theorem cell22_1200362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1200362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200362 prefixEnd_1200362 := by exact prefixLift 1200362
  have htrace : WordTrace (prefixWord ++ tailWord_1200362) baseStart_1200362 baseEnd_1200362 := by
    simpa [prefixWord, tailWord_1200362, baseEnd_1200362] using wordTrace_append hprefix tailTrace_1200362
  have hstable : (prefixWord ++ tailWord_1200362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200362).length < 2 ^ (prefixWord ++ tailWord_1200362).sum := by decide
  have hdescent : baseEnd_1200362 < baseStart_1200362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200392 : List Nat := [2, 1, 3, 2, 3, 1, 3, 7]
def baseStart_1200392 : Nat := 118140960795 + 1200392 * 2 ^ 59
def prefixEnd_1200392 : Nat := 4983230072969 + 3 ^ 40 * 1200392 * 2
def baseEnd_1200392 : Nat := 45657634800886866257741

theorem tailTrace_1200392 : CollatzResearch.WordTrace tailWord_1200392 prefixEnd_1200392 45657634800886866257741 := by
  unfold tailWord_1200392
  simp only [CollatzResearch.WordTrace]
  refine ⟨21890946533596134738489715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29187928711461512984652953 21890946533596134738489715)
  ·
    refine ⟨32836419800394202107734573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21890946533596134738489715 32836419800394202107734573)
    ·
      refine ⟨12313657425147825790400465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32836419800394202107734573 12313657425147825790400465)
      ·
        refine ⟨9235243068860869342800349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12313657425147825790400465 9235243068860869342800349)
        ·
          refine ⟨3463216150822826003550131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9235243068860869342800349 3463216150822826003550131)
          ·
            refine ⟨5194824226234239005325197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463216150822826003550131 5194824226234239005325197)
            ·
              refine ⟨1948059084837839626996949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5194824226234239005325197 1948059084837839626996949)
              ·
                refine ⟨45657634800886866257741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1948059084837839626996949 45657634800886866257741)
                ·
                  rfl

theorem cell22_1200392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_1200392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200392 prefixEnd_1200392 := by exact prefixLift 1200392
  have htrace : WordTrace (prefixWord ++ tailWord_1200392) baseStart_1200392 baseEnd_1200392 := by
    simpa [prefixWord, tailWord_1200392, baseEnd_1200392] using wordTrace_append hprefix tailTrace_1200392
  have hstable : (prefixWord ++ tailWord_1200392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200392).length < 2 ^ (prefixWord ++ tailWord_1200392).sum := by decide
  have hdescent : baseEnd_1200392 < baseStart_1200392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200430 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1200430 : Nat := 118140960795 + 1200430 * 2 ^ 59
def prefixEnd_1200430 : Nat := 4983230072969 + 3 ^ 40 * 1200430 * 2
def baseEnd_1200430 : Nat := 410931721384562363869553

theorem tailTrace_1200430 : CollatzResearch.WordTrace tailWord_1200430 prefixEnd_1200430 410931721384562363869553 := by
  unfold tailWord_1200430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472909880131825245857843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29188852694036401311241829 5472909880131825245857843)
  ·
    refine ⟨8209364820197737868786765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5472909880131825245857843 8209364820197737868786765)
    ·
      refine ⟨3078511807574151700795037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8209364820197737868786765 3078511807574151700795037)
      ·
        refine ⟨1154441927840306887798139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3078511807574151700795037 1154441927840306887798139)
        ·
          refine ⟨1731662891760460331697209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154441927840306887798139 1731662891760460331697209)
          ·
            refine ⟨1298747168820345248772907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731662891760460331697209 1298747168820345248772907)
            ·
              refine ⟨1948120753230517873159361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298747168820345248772907 1948120753230517873159361)
              ·
                refine ⟨1461090564922888404869521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948120753230517873159361 1461090564922888404869521)
                ·
                  refine ⟨1095817923692166303652141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461090564922888404869521 1095817923692166303652141)
                  ·
                    refine ⟨410931721384562363869553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095817923692166303652141 410931721384562363869553)
                    ·
                      rfl

theorem cell22_1200430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1200430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200430 prefixEnd_1200430 := by exact prefixLift 1200430
  have htrace : WordTrace (prefixWord ++ tailWord_1200430) baseStart_1200430 baseEnd_1200430 := by
    simpa [prefixWord, tailWord_1200430, baseEnd_1200430] using wordTrace_append hprefix tailTrace_1200430
  have hstable : (prefixWord ++ tailWord_1200430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200430).length < 2 ^ (prefixWord ++ tailWord_1200430).sum := by decide
  have hdescent : baseEnd_1200430 < baseStart_1200430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200437 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 7]
def baseStart_1200437 : Nat := 118140960795 + 1200437 * 2 ^ 59
def prefixEnd_1200437 : Nat := 4983230072969 + 3 ^ 40 * 1200437 * 2
def baseEnd_1200437 : Nat := 136978039209205559648177

theorem tailTrace_1200437 : CollatzResearch.WordTrace tailWord_1200437 prefixEnd_1200437 136978039209205559648177 := by
  unfold tailWord_1200437
  simp only [CollatzResearch.WordTrace]
  refine ⟨43783534352029242162367565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29189022901352828108245043 43783534352029242162367565)
  ·
    refine ⟨16418825382010965810887837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43783534352029242162367565 16418825382010965810887837)
    ·
      refine ⟨6157059518254112179082939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16418825382010965810887837 6157059518254112179082939)
      ·
        refine ⟨9235589277381168268624409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157059518254112179082939 9235589277381168268624409)
        ·
          refine ⟨6926691958035876201468307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9235589277381168268624409 6926691958035876201468307)
          ·
            refine ⟨10390037937053814302202461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926691958035876201468307 10390037937053814302202461)
            ·
              refine ⟨3896264226395180363325923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10390037937053814302202461 3896264226395180363325923)
              ·
                refine ⟨5844396339592770544988885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896264226395180363325923 5844396339592770544988885)
                ·
                  refine ⟨136978039209205559648177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5844396339592770544988885 136978039209205559648177)
                  ·
                    rfl

theorem cell22_1200437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_1200437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200437 prefixEnd_1200437 := by exact prefixLift 1200437
  have htrace : WordTrace (prefixWord ++ tailWord_1200437) baseStart_1200437 baseEnd_1200437 := by
    simpa [prefixWord, tailWord_1200437, baseEnd_1200437] using wordTrace_append hprefix tailTrace_1200437
  have hstable : (prefixWord ++ tailWord_1200437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200437).length < 2 ^ (prefixWord ++ tailWord_1200437).sum := by decide
  have hdescent : baseEnd_1200437 < baseStart_1200437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200441 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_1200441 : Nat := 118140960795 + 1200441 * 2 ^ 59
def prefixEnd_1200441 : Nat := 4983230072969 + 3 ^ 40 * 1200441 * 2
def baseEnd_1200441 : Nat := 410935486909362001844519

theorem tailTrace_1200441 : CollatzResearch.WordTrace tailWord_1200441 prefixEnd_1200441 410935486909362001844519 := by
  unfold tailWord_1200441
  simp only [CollatzResearch.WordTrace]
  refine ⟨43783680244014750845513177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29189120162676500563675451 43783680244014750845513177)
  ·
    refine ⟨32837760183011063134134883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43783680244014750845513177 32837760183011063134134883)
    ·
      refine ⟨49256640274516594701202325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32837760183011063134134883 49256640274516594701202325)
      ·
        refine ⟨2308905012867965376618859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49256640274516594701202325 2308905012867965376618859)
        ·
          refine ⟨3463357519301948064928289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308905012867965376618859 3463357519301948064928289)
          ·
            refine ⟨2597518139476461048696217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463357519301948064928289 2597518139476461048696217)
            ·
              refine ⟨1948138604607345786522163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597518139476461048696217 1948138604607345786522163)
              ·
                refine ⟨2922207906911018679783245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948138604607345786522163 2922207906911018679783245)
                ·
                  refine ⟨1095827965091632004918717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2922207906911018679783245 1095827965091632004918717)
                  ·
                    refine ⟨410935486909362001844519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095827965091632004918717 410935486909362001844519)
                    ·
                      rfl

theorem cell22_1200441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_1200441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200441 prefixEnd_1200441 := by exact prefixLift 1200441
  have htrace : WordTrace (prefixWord ++ tailWord_1200441) baseStart_1200441 baseEnd_1200441 := by
    simpa [prefixWord, tailWord_1200441, baseEnd_1200441] using wordTrace_append hprefix tailTrace_1200441
  have hstable : (prefixWord ++ tailWord_1200441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200441).length < 2 ^ (prefixWord ++ tailWord_1200441).sum := by decide
  have hdescent : baseEnd_1200441 < baseStart_1200441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200484 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1200484 : Nat := 118140960795 + 1200484 * 2 ^ 59
def prefixEnd_1200484 : Nat := 4983230072969 + 3 ^ 40 * 1200484 * 2
def baseEnd_1200484 : Nat := 410950206688124223019387

theorem tailTrace_1200484 : CollatzResearch.WordTrace tailWord_1200484 prefixEnd_1200484 410950206688124223019387 := by
  unfold tailWord_1200484
  simp only [CollatzResearch.WordTrace]
  refine ⟨21892624291429484594664253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29190165721905979459552337 21892624291429484594664253)
  ·
    refine ⟨8209734109286056722999095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21892624291429484594664253 8209734109286056722999095)
    ·
      refine ⟨12314601163929085084498643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8209734109286056722999095 12314601163929085084498643)
      ·
        refine ⟨18471901745893627626747965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12314601163929085084498643 18471901745893627626747965)
        ·
          refine ⟨6926963154710110360030487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18471901745893627626747965 6926963154710110360030487)
          ·
            refine ⟨10390444732065165540045731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926963154710110360030487 10390444732065165540045731)
            ·
              refine ⟨15585667098097748310068597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390444732065165540045731 15585667098097748310068597)
              ·
                refine ⟨1461156290446663904068931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15585667098097748310068597 1461156290446663904068931)
                ·
                  refine ⟨2191734435669995856103397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461156290446663904068931 2191734435669995856103397)
                  ·
                    refine ⟨410950206688124223019387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191734435669995856103397 410950206688124223019387)
                    ·
                      rfl

theorem cell22_1200484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1200484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200484 prefixEnd_1200484 := by exact prefixLift 1200484
  have htrace : WordTrace (prefixWord ++ tailWord_1200484) baseStart_1200484 baseEnd_1200484 := by
    simpa [prefixWord, tailWord_1200484, baseEnd_1200484] using wordTrace_append hprefix tailTrace_1200484
  have hstable : (prefixWord ++ tailWord_1200484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200484).length < 2 ^ (prefixWord ++ tailWord_1200484).sum := by decide
  have hdescent : baseEnd_1200484 < baseStart_1200484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200580 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1200580 : Nat := 118140960795 + 1200580 * 2 ^ 59
def prefixEnd_1200580 : Nat := 4983230072969 + 3 ^ 40 * 1200580 * 2
def baseEnd_1200580 : Nat := 410983069450011972619093

theorem tailTrace_1200580 : CollatzResearch.WordTrace tailWord_1200580 prefixEnd_1200580 410983069450011972619093 := by
  unfold tailWord_1200580
  simp only [CollatzResearch.WordTrace]
  refine ⟨21894374995255588792411597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29192499993674118389882129 21894374995255588792411597)
  ·
    refine ⟨8210390623220845797154349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21894374995255588792411597 8210390623220845797154349)
    ·
      refine ⟨3078896483707817173932881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8210390623220845797154349 3078896483707817173932881)
      ·
        refine ⟨2309172362780862880449661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078896483707817173932881 2309172362780862880449661)
        ·
          refine ⟨865939636042823580168623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2309172362780862880449661 865939636042823580168623)
          ·
            refine ⟨1298909454064235370252935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865939636042823580168623 1298909454064235370252935)
            ·
              refine ⟨1948364181096353055379403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298909454064235370252935 1948364181096353055379403)
              ·
                refine ⟨2922546271644529583069105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948364181096353055379403 2922546271644529583069105)
                ·
                  refine ⟨2191909703733397187301829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922546271644529583069105 2191909703733397187301829)
                  ·
                    refine ⟨410983069450011972619093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191909703733397187301829 410983069450011972619093)
                    ·
                      rfl

theorem cell22_1200580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1200580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200580 prefixEnd_1200580 := by exact prefixLift 1200580
  have htrace : WordTrace (prefixWord ++ tailWord_1200580) baseStart_1200580 baseEnd_1200580 := by
    simpa [prefixWord, tailWord_1200580, baseEnd_1200580] using wordTrace_append hprefix tailTrace_1200580
  have hstable : (prefixWord ++ tailWord_1200580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200580).length < 2 ^ (prefixWord ++ tailWord_1200580).sum := by decide
  have hdescent : baseEnd_1200580 < baseStart_1200580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200587 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_1200587 : Nat := 118140960795 + 1200587 * 2 ^ 59
def prefixEnd_1200587 : Nat := 4983230072969 + 3 ^ 40 * 1200587 * 2
def baseEnd_1200587 : Nat := 410985465693066287694071

theorem tailTrace_1200587 : CollatzResearch.WordTrace tailWord_1200587 prefixEnd_1200587 410985465693066287694071 := by
  unfold tailWord_1200587
  simp only [CollatzResearch.WordTrace]
  refine ⟨43789005301485817780328015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29192670200990545186885343 43789005301485817780328015)
  ·
    refine ⟨65683507952228726670492023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43789005301485817780328015 65683507952228726670492023)
    ·
      refine ⟨98525261928343090005738035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65683507952228726670492023 98525261928343090005738035)
      ·
        refine ⟨147787892892514635008607053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98525261928343090005738035 147787892892514635008607053)
        ·
          refine ⟨55420459834692988128227645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147787892892514635008607053 55420459834692988128227645)
          ·
            refine ⟨20782672438009870548085367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55420459834692988128227645 20782672438009870548085367)
            ·
              refine ⟨31174008657014805822128051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20782672438009870548085367 31174008657014805822128051)
              ·
                refine ⟨46761012985522208733192077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31174008657014805822128051 46761012985522208733192077)
                ·
                  refine ⟨17535379869570828274947029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46761012985522208733192077 17535379869570828274947029)
                  ·
                    refine ⟨410985465693066287694071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17535379869570828274947029 410985465693066287694071)
                    ·
                      rfl

theorem cell22_1200587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_1200587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200587 prefixEnd_1200587 := by exact prefixLift 1200587
  have htrace : WordTrace (prefixWord ++ tailWord_1200587) baseStart_1200587 baseEnd_1200587 := by
    simpa [prefixWord, tailWord_1200587, baseEnd_1200587] using wordTrace_append hprefix tailTrace_1200587
  have hstable : (prefixWord ++ tailWord_1200587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200587).length < 2 ^ (prefixWord ++ tailWord_1200587).sum := by decide
  have hdescent : baseEnd_1200587 < baseStart_1200587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200621 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1200621 : Nat := 118140960795 + 1200621 * 2 ^ 59
def prefixEnd_1200621 : Nat := 4983230072969 + 3 ^ 40 * 1200621 * 2
def baseEnd_1200621 : Nat := 410997104587901532343967

theorem tailTrace_1200621 : CollatzResearch.WordTrace tailWord_1200621 prefixEnd_1200621 410997104587901532343967 := by
  unfold tailWord_1200621
  simp only [CollatzResearch.WordTrace]
  refine ⟨43790245383362641587065717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29193496922241761058043811 43790245383362641587065717)
  ·
    refine ⟨4105335504690247648787411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43790245383362641587065717 4105335504690247648787411)
    ·
      refine ⟨6158003257035371473181117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105335504690247648787411 6158003257035371473181117)
      ·
        refine ⟨2309251221388264302442919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6158003257035371473181117 2309251221388264302442919)
        ·
          refine ⟨3463876832082396453664379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2309251221388264302442919 3463876832082396453664379)
          ·
            refine ⟨5195815248123594680496569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463876832082396453664379 5195815248123594680496569)
            ·
              refine ⟨3896861436092696010372427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195815248123594680496569 3896861436092696010372427)
              ·
                refine ⟨5845292154139044015558641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896861436092696010372427 5845292154139044015558641)
                ·
                  refine ⟨4383969115604283011668981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845292154139044015558641 4383969115604283011668981)
                  ·
                    refine ⟨410997104587901532343967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4383969115604283011668981 410997104587901532343967)
                    ·
                      rfl

theorem cell22_1200621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1200621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200621 prefixEnd_1200621 := by exact prefixLift 1200621
  have htrace : WordTrace (prefixWord ++ tailWord_1200621) baseStart_1200621 baseEnd_1200621 := by
    simpa [prefixWord, tailWord_1200621, baseEnd_1200621] using wordTrace_append hprefix tailTrace_1200621
  have hstable : (prefixWord ++ tailWord_1200621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200621).length < 2 ^ (prefixWord ++ tailWord_1200621).sum := by decide
  have hdescent : baseEnd_1200621 < baseStart_1200621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200666 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_1200666 : Nat := 118140960795 + 1200666 * 2 ^ 59
def prefixEnd_1200666 : Nat := 4983230072969 + 3 ^ 40 * 1200666 * 2
def baseEnd_1200666 : Nat := 411012509007536414968829

theorem tailTrace_1200666 : CollatzResearch.WordTrace tailWord_1200666 prefixEnd_1200666 411012509007536414968829 := by
  unfold tailWord_1200666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947971667049903568113463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29194591112133076181635901 10947971667049903568113463)
  ·
    refine ⟨16421957500574855352170195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10947971667049903568113463 16421957500574855352170195)
    ·
      refine ⟨24632936250862283028255293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16421957500574855352170195 24632936250862283028255293)
      ·
        refine ⟨9237351094073356135595735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24632936250862283028255293 9237351094073356135595735)
        ·
          refine ⟨13856026641110034203393603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237351094073356135595735 13856026641110034203393603)
          ·
            refine ⟨20784039961665051305090405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856026641110034203393603 20784039961665051305090405)
            ·
              refine ⟨3897007492812197119704451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20784039961665051305090405 3897007492812197119704451)
              ·
                refine ⟨5845511239218295679556677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897007492812197119704451 5845511239218295679556677)
                ·
                  refine ⟨1096033357353430439916877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5845511239218295679556677 1096033357353430439916877)
                  ·
                    refine ⟨411012509007536414968829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096033357353430439916877 411012509007536414968829)
                    ·
                      rfl

theorem cell22_1200666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_1200666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200666 prefixEnd_1200666 := by exact prefixLift 1200666
  have htrace : WordTrace (prefixWord ++ tailWord_1200666) baseStart_1200666 baseEnd_1200666 := by
    simpa [prefixWord, tailWord_1200666, baseEnd_1200666] using wordTrace_append hprefix tailTrace_1200666
  have hstable : (prefixWord ++ tailWord_1200666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200666).length < 2 ^ (prefixWord ++ tailWord_1200666).sum := by decide
  have hdescent : baseEnd_1200666 < baseStart_1200666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1200784 : Nat := 118140960795 + 1200784 * 2 ^ 59
def prefixEnd_1200784 : Nat := 4983230072969 + 3 ^ 40 * 1200784 * 2
def baseEnd_1200784 : Nat := 411052902819023440518467

theorem tailTrace_1200784 : CollatzResearch.WordTrace tailWord_1200784 prefixEnd_1200784 411052902819023440518467 := by
  unfold tailWord_1200784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898095240886060212624703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29197460321181413616832937 21898095240886060212624703)
  ·
    refine ⟨32847142861329090318937055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21898095240886060212624703 32847142861329090318937055)
    ·
      refine ⟨49270714291993635478405583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32847142861329090318937055 49270714291993635478405583)
      ·
        refine ⟨73906071437990453217608375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49270714291993635478405583 73906071437990453217608375)
        ·
          refine ⟨110859107156985679826412563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73906071437990453217608375 110859107156985679826412563)
          ·
            refine ⟨166288660735478519739618845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110859107156985679826412563 166288660735478519739618845)
            ·
              refine ⟨62358247775804444902357067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166288660735478519739618845 62358247775804444902357067)
              ·
                refine ⟨93537371663706667353535601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62358247775804444902357067 93537371663706667353535601)
                ·
                  refine ⟨70153028747780000515151701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93537371663706667353535601 70153028747780000515151701)
                  ·
                    refine ⟨411052902819023440518467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70153028747780000515151701 411052902819023440518467)
                    ·
                      rfl

theorem cell22_1200784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1200784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200784 prefixEnd_1200784 := by exact prefixLift 1200784
  have htrace : WordTrace (prefixWord ++ tailWord_1200784) baseStart_1200784 baseEnd_1200784 := by
    simpa [prefixWord, tailWord_1200784, baseEnd_1200784] using wordTrace_append hprefix tailTrace_1200784
  have hstable : (prefixWord ++ tailWord_1200784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200784).length < 2 ^ (prefixWord ++ tailWord_1200784).sum := by decide
  have hdescent : baseEnd_1200784 < baseStart_1200784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200816 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1200816 : Nat := 118140960795 + 1200816 * 2 ^ 59
def prefixEnd_1200816 : Nat := 4983230072969 + 3 ^ 40 * 1200816 * 2
def baseEnd_1200816 : Nat := 411063857072986023718369

theorem tailTrace_1200816 : CollatzResearch.WordTrace tailWord_1200816 prefixEnd_1200816 411063857072986023718369 := by
  unfold tailWord_1200816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898678808828094945207151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29198238411770793260276201 21898678808828094945207151)
  ·
    refine ⟨32848018213242142417810727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21898678808828094945207151 32848018213242142417810727)
    ·
      refine ⟨49272027319863213626716091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32848018213242142417810727 49272027319863213626716091)
      ·
        refine ⟨73908040979794820440074137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49272027319863213626716091 73908040979794820440074137)
        ·
          refine ⟨55431030734846115330055603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73908040979794820440074137 55431030734846115330055603)
          ·
            refine ⟨83146546102269172995083405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55431030734846115330055603 83146546102269172995083405)
            ·
              refine ⟨31179954788350939873156277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83146546102269172995083405 31179954788350939873156277)
              ·
                refine ⟨2923120761407900613108401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31179954788350939873156277 2923120761407900613108401)
                ·
                  refine ⟨2192340571055925459831301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923120761407900613108401 2192340571055925459831301)
                  ·
                    refine ⟨411063857072986023718369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2192340571055925459831301 411063857072986023718369)
                    ·
                      rfl

theorem cell22_1200816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1200816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200816 prefixEnd_1200816 := by exact prefixLift 1200816
  have htrace : WordTrace (prefixWord ++ tailWord_1200816) baseStart_1200816 baseEnd_1200816 := by
    simpa [prefixWord, tailWord_1200816, baseEnd_1200816] using wordTrace_append hprefix tailTrace_1200816
  have hstable : (prefixWord ++ tailWord_1200816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200816).length < 2 ^ (prefixWord ++ tailWord_1200816).sum := by decide
  have hdescent : baseEnd_1200816 < baseStart_1200816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200831 : List Nat := [1, 1, 2, 2, 2, 6, 8]
def baseStart_1200831 : Nat := 118140960795 + 1200831 * 2 ^ 59
def prefixEnd_1200831 : Nat := 4983230072969 + 3 ^ 40 * 1200831 * 2
def baseEnd_1200831 : Nat := 15224777477019666096049

theorem tailTrace_1200831 : CollatzResearch.WordTrace tailWord_1200831 prefixEnd_1200831 15224777477019666096049 := by
  unfold tailWord_1200831
  simp only [CollatzResearch.WordTrace]
  refine ⟨43797904712601847452210347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29198603141734564968140231 43797904712601847452210347)
  ·
    refine ⟨65696857068902771178315521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43797904712601847452210347 65696857068902771178315521)
    ·
      refine ⟨49272642801677078383736641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65696857068902771178315521 49272642801677078383736641)
      ·
        refine ⟨36954482101257808787802481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49272642801677078383736641 36954482101257808787802481)
        ·
          refine ⟨27715861575943356590851861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36954482101257808787802481 27715861575943356590851861)
          ·
            refine ⟨1299181011372344840196181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27715861575943356590851861 1299181011372344840196181)
            ·
              refine ⟨15224777477019666096049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1299181011372344840196181 15224777477019666096049)
              ·
                rfl

theorem cell22_1200831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 8].length) (baseStart_1200831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200831 prefixEnd_1200831 := by exact prefixLift 1200831
  have htrace : WordTrace (prefixWord ++ tailWord_1200831) baseStart_1200831 baseEnd_1200831 := by
    simpa [prefixWord, tailWord_1200831, baseEnd_1200831] using wordTrace_append hprefix tailTrace_1200831
  have hstable : (prefixWord ++ tailWord_1200831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200831).length < 2 ^ (prefixWord ++ tailWord_1200831).sum := by decide
  have hdescent : baseEnd_1200831 < baseStart_1200831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200852 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1200852 : Nat := 118140960795 + 1200852 * 2 ^ 59
def prefixEnd_1200852 : Nat := 4983230072969 + 3 ^ 40 * 1200852 * 2
def baseEnd_1200852 : Nat := 411076180608693929818259

theorem tailTrace_1200852 : CollatzResearch.WordTrace tailWord_1200852 prefixEnd_1200852 411076180608693929818259 := by
  unfold tailWord_1200852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899335322762884019362405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29199113763683845359149873 21899335322762884019362405)
  ·
    refine ⟨4106125373018040753630451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21899335322762884019362405 4106125373018040753630451)
    ·
      refine ⟨6159188059527061130445677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4106125373018040753630451 6159188059527061130445677)
      ·
        refine ⟨2309695522322647923917129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6159188059527061130445677 2309695522322647923917129)
        ·
          refine ⟨1732271641741985942937847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2309695522322647923917129 1732271641741985942937847)
          ·
            refine ⟨2598407462612978914406771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732271641741985942937847 2598407462612978914406771)
            ·
              refine ⟨3897611193919468371610157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598407462612978914406771 3897611193919468371610157)
              ·
                refine ⟨1461604197719800639353809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897611193919468371610157 1461604197719800639353809)
                ·
                  refine ⟨1096203148289850479515357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461604197719800639353809 1096203148289850479515357)
                  ·
                    refine ⟨411076180608693929818259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096203148289850479515357 411076180608693929818259)
                    ·
                      rfl

theorem cell22_1200852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1200852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200852 prefixEnd_1200852 := by exact prefixLift 1200852
  have htrace : WordTrace (prefixWord ++ tailWord_1200852) baseStart_1200852 baseEnd_1200852 := by
    simpa [prefixWord, tailWord_1200852, baseEnd_1200852] using wordTrace_append hprefix tailTrace_1200852
  have hstable : (prefixWord ++ tailWord_1200852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200852).length < 2 ^ (prefixWord ++ tailWord_1200852).sum := by decide
  have hdescent : baseEnd_1200852 < baseStart_1200852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200880 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_1200880 : Nat := 118140960795 + 1200880 * 2 ^ 59
def prefixEnd_1200880 : Nat := 4983230072969 + 3 ^ 40 * 1200880 * 2
def baseEnd_1200880 : Nat := 411085765580911190118173

theorem tailTrace_1200880 : CollatzResearch.WordTrace tailWord_1200880 prefixEnd_1200880 411085765580911190118173 := by
  unfold tailWord_1200880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899845944712164410372047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29199794592949552547162729 21899845944712164410372047)
  ·
    refine ⟨32849768917068246615558071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21899845944712164410372047 32849768917068246615558071)
    ·
      refine ⟨49274653375602369923337107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32849768917068246615558071 49274653375602369923337107)
      ·
        refine ⟨73911980063403554885005661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49274653375602369923337107 73911980063403554885005661)
        ·
          refine ⟨27716992523776333081877123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73911980063403554885005661 27716992523776333081877123)
          ·
            refine ⟨41575488785664499622815685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27716992523776333081877123 41575488785664499622815685)
            ·
              refine ⟨7795404147312093679277941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41575488785664499622815685 7795404147312093679277941)
              ·
                refine ⟨730819138810508782432307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7795404147312093679277941 730819138810508782432307)
                ·
                  refine ⟨1096228708215763173648461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730819138810508782432307 1096228708215763173648461)
                  ·
                    refine ⟨411085765580911190118173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096228708215763173648461 411085765580911190118173)
                    ·
                      rfl

theorem cell22_1200880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_1200880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200880 prefixEnd_1200880 := by exact prefixLift 1200880
  have htrace : WordTrace (prefixWord ++ tailWord_1200880) baseStart_1200880 baseEnd_1200880 := by
    simpa [prefixWord, tailWord_1200880, baseEnd_1200880] using wordTrace_append hprefix tailTrace_1200880
  have hstable : (prefixWord ++ tailWord_1200880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200880).length < 2 ^ (prefixWord ++ tailWord_1200880).sum := by decide
  have hdescent : baseEnd_1200880 < baseStart_1200880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200893 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 5]
def baseStart_1200893 : Nat := 118140960795 + 1200893 * 2 ^ 59
def prefixEnd_1200893 : Nat := 4983230072969 + 3 ^ 40 * 1200893 * 2
def baseEnd_1200893 : Nat := 137030071915527829847711

theorem tailTrace_1200893 : CollatzResearch.WordTrace tailWord_1200893 prefixEnd_1200893 137030071915527829847711 := by
  unfold tailWord_1200893
  simp only [CollatzResearch.WordTrace]
  refine ⟨43800166038377232040967333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29200110692251488027311555 43800166038377232040967333)
  ·
    refine ⟨8212531132195731007681375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43800166038377232040967333 8212531132195731007681375)
    ·
      refine ⟨12318796698293596511522063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212531132195731007681375 12318796698293596511522063)
      ·
        refine ⟨18478195047440394767283095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12318796698293596511522063 18478195047440394767283095)
        ·
          refine ⟨27717292571160592150924643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18478195047440394767283095 27717292571160592150924643)
          ·
            refine ⟨41575938856740888226386965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27717292571160592150924643 41575938856740888226386965)
            ·
              refine ⟨1948872133909729135611889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41575938856740888226386965 1948872133909729135611889)
              ·
                refine ⟨1461654100432296851708917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948872133909729135611889 1461654100432296851708917)
                ·
                  refine ⟨137030071915527829847711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1461654100432296851708917 137030071915527829847711)
                  ·
                    rfl

theorem cell22_1200893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_1200893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200893 prefixEnd_1200893 := by exact prefixLift 1200893
  have htrace : WordTrace (prefixWord ++ tailWord_1200893) baseStart_1200893 baseEnd_1200893 := by
    simpa [prefixWord, tailWord_1200893, baseEnd_1200893] using wordTrace_append hprefix tailTrace_1200893
  have hstable : (prefixWord ++ tailWord_1200893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200893).length < 2 ^ (prefixWord ++ tailWord_1200893).sum := by decide
  have hdescent : baseEnd_1200893 < baseStart_1200893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200983 : List Nat := [1, 1, 3, 2, 4, 2, 1, 8]
def baseStart_1200983 : Nat := 118140960795 + 1200983 * 2 ^ 59
def prefixEnd_1200983 : Nat := 4983230072969 + 3 ^ 40 * 1200983 * 2
def baseEnd_1200983 : Nat := 45680113842872583865873

theorem tailTrace_1200983 : CollatzResearch.WordTrace tailWord_1200983 prefixEnd_1200983 45680113842872583865873 := by
  unfold tailWord_1200983
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803448608051177411743603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29202299072034118274495735 43803448608051177411743603)
  ·
    refine ⟨65705172912076766117615405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43803448608051177411743603 65705172912076766117615405)
    ·
      refine ⟨24639439842028787294105777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65705172912076766117615405 24639439842028787294105777)
      ·
        refine ⟨18479579881521590470579333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24639439842028787294105777 18479579881521590470579333)
        ·
          refine ⟨3464921227785298213233625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18479579881521590470579333 3464921227785298213233625)
          ·
            refine ⟨2598690920838973659925219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3464921227785298213233625 2598690920838973659925219)
            ·
              refine ⟨3898036381258460489887829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598690920838973659925219 3898036381258460489887829)
              ·
                refine ⟨45680113842872583865873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3898036381258460489887829 45680113842872583865873)
                ·
                  rfl

theorem cell22_1200983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 8].length) (baseStart_1200983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1200983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1200983 prefixEnd_1200983 := by exact prefixLift 1200983
  have htrace : WordTrace (prefixWord ++ tailWord_1200983) baseStart_1200983 baseEnd_1200983 := by
    simpa [prefixWord, tailWord_1200983, baseEnd_1200983] using wordTrace_append hprefix tailTrace_1200983
  have hstable : (prefixWord ++ tailWord_1200983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200983).length < 2 ^ (prefixWord ++ tailWord_1200983).sum := by decide
  have hdescent : baseEnd_1200983 < baseStart_1200983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201105 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_1201105 : Nat := 118140960795 + 1201105 * 2 ^ 59
def prefixEnd_1201105 : Nat := 4983230072969 + 3 ^ 40 * 1201105 * 2
def baseEnd_1201105 : Nat := 411162787679085603242483

theorem tailTrace_1201105 : CollatzResearch.WordTrace tailWord_1201105 prefixEnd_1201105 411162787679085603242483 := by
  unfold tailWord_1201105
  simp only [CollatzResearch.WordTrace]
  refine ⟨43807898313609192247684769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29205265542406128165123179 43807898313609192247684769)
  ·
    refine ⟨32855923735206894185763577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43807898313609192247684769 32855923735206894185763577)
    ·
      refine ⟨24641942801405170639322683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32855923735206894185763577 24641942801405170639322683)
      ·
        refine ⟨36962914202107755958984025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24641942801405170639322683 36962914202107755958984025)
        ·
          refine ⟨27722185651580816969238019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36962914202107755958984025 27722185651580816969238019)
          ·
            refine ⟨41583278477371225453857029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27722185651580816969238019 41583278477371225453857029)
            ·
              refine ⟨7796864714507104772598193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41583278477371225453857029 7796864714507104772598193)
              ·
                refine ⟨5847648535880328579448645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7796864714507104772598193 5847648535880328579448645)
                ·
                  refine ⟨1096434100477561608646621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5847648535880328579448645 1096434100477561608646621)
                  ·
                    refine ⟨411162787679085603242483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096434100477561608646621 411162787679085603242483)
                    ·
                      rfl

theorem cell22_1201105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_1201105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201105 prefixEnd_1201105 := by exact prefixLift 1201105
  have htrace : WordTrace (prefixWord ++ tailWord_1201105) baseStart_1201105 baseEnd_1201105 := by
    simpa [prefixWord, tailWord_1201105, baseEnd_1201105] using wordTrace_append hprefix tailTrace_1201105
  have hstable : (prefixWord ++ tailWord_1201105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201105).length < 2 ^ (prefixWord ++ tailWord_1201105).sum := by decide
  have hdescent : baseEnd_1201105 < baseStart_1201105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201240 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1201240 : Nat := 118140960795 + 1201240 * 2 ^ 59
def prefixEnd_1201240 : Nat := 4983230072969 + 3 ^ 40 * 1201240 * 2
def baseEnd_1201240 : Nat := 411209000937990251117069

theorem tailTrace_1201240 : CollatzResearch.WordTrace tailWord_1201240 prefixEnd_1201240 411209000937990251117069 := by
  unfold tailWord_1201240
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906411084060055151924587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29208548112080073535899449 21906411084060055151924587)
  ·
    refine ⟨32859616626090082727886881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906411084060055151924587 32859616626090082727886881)
    ·
      refine ⟨24644712469567562045915161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32859616626090082727886881 24644712469567562045915161)
      ·
        refine ⟨18483534352175671534436371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24644712469567562045915161 18483534352175671534436371)
        ·
          refine ⟨27725301528263507301654557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18483534352175671534436371 27725301528263507301654557)
          ·
            refine ⟨10396988073098815238120459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27725301528263507301654557 10396988073098815238120459)
            ·
              refine ⟨15595482109648222857180689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10396988073098815238120459 15595482109648222857180689)
              ·
                refine ⟨11696611582236167142885517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15595482109648222857180689 11696611582236167142885517)
                ·
                  refine ⟨4386229343338562678582069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11696611582236167142885517 4386229343338562678582069)
                  ·
                    refine ⟨411209000937990251117069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4386229343338562678582069 411209000937990251117069)
                    ·
                      rfl

theorem cell22_1201240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1201240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201240 prefixEnd_1201240 := by exact prefixLift 1201240
  have htrace : WordTrace (prefixWord ++ tailWord_1201240) baseStart_1201240 baseEnd_1201240 := by
    simpa [prefixWord, tailWord_1201240, baseEnd_1201240] using wordTrace_append hprefix tailTrace_1201240
  have hstable : (prefixWord ++ tailWord_1201240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201240).length < 2 ^ (prefixWord ++ tailWord_1201240).sum := by decide
  have hdescent : baseEnd_1201240 < baseStart_1201240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201246 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1201246 : Nat := 118140960795 + 1201246 * 2 ^ 59
def prefixEnd_1201246 : Nat := 4983230072969 + 3 ^ 40 * 1201246 * 2
def baseEnd_1201246 : Nat := 411211054860608235467051

theorem tailTrace_1201246 : CollatzResearch.WordTrace tailWord_1201246 prefixEnd_1201246 411211054860608235467051 := by
  unfold tailWord_1201246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476630125762296666070949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29208694004065582219045061 5476630125762296666070949)
  ·
    refine ⟨1026868148580430624888303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5476630125762296666070949 1026868148580430624888303)
    ·
      refine ⟨1540302222870645937332455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026868148580430624888303 1540302222870645937332455)
      ·
        refine ⟨2310453334305968905998683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540302222870645937332455 2310453334305968905998683)
        ·
          refine ⟨3465680001458953358998025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310453334305968905998683 3465680001458953358998025)
          ·
            refine ⟨2599260001094215019248519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465680001458953358998025 2599260001094215019248519)
            ·
              refine ⟨3898890001641322528872779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599260001094215019248519 3898890001641322528872779)
              ·
                refine ⟨5848335002461983793309169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898890001641322528872779 5848335002461983793309169)
                ·
                  refine ⟨4386251251846487844981877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848335002461983793309169 4386251251846487844981877)
                  ·
                    refine ⟨411211054860608235467051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4386251251846487844981877 411211054860608235467051)
                    ·
                      rfl

theorem cell22_1201246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1201246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201246 prefixEnd_1201246 := by exact prefixLift 1201246
  have htrace : WordTrace (prefixWord ++ tailWord_1201246) baseStart_1201246 baseEnd_1201246 := by
    simpa [prefixWord, tailWord_1201246, baseEnd_1201246] using wordTrace_append hprefix tailTrace_1201246
  have hstable : (prefixWord ++ tailWord_1201246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201246).length < 2 ^ (prefixWord ++ tailWord_1201246).sum := by decide
  have hdescent : baseEnd_1201246 < baseStart_1201246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201257 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_1201257 : Nat := 118140960795 + 1201257 * 2 ^ 59
def prefixEnd_1201257 : Nat := 4983230072969 + 3 ^ 40 * 1201257 * 2
def baseEnd_1201257 : Nat := 411214820385407873442017

theorem tailTrace_1201257 : CollatzResearch.WordTrace tailWord_1201257 prefixEnd_1201257 411214820385407873442017 := by
  unfold tailWord_1201257
  simp only [CollatzResearch.WordTrace]
  refine ⟨43813442209058522207218025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29208961472705681471478683 43813442209058522207218025)
  ·
    refine ⟨32860081656793891655413519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43813442209058522207218025 32860081656793891655413519)
    ·
      refine ⟨49290122485190837483120279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32860081656793891655413519 49290122485190837483120279)
      ·
        refine ⟨73935183727786256224680419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49290122485190837483120279 73935183727786256224680419)
        ·
          refine ⟨110902775591679384337020629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73935183727786256224680419 110902775591679384337020629)
          ·
            refine ⟨2599283802929985570398921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110902775591679384337020629 2599283802929985570398921)
            ·
              refine ⟨1949462852197489177799191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599283802929985570398921 1949462852197489177799191)
              ·
                refine ⟨2924194278296233766698787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949462852197489177799191 2924194278296233766698787)
                ·
                  refine ⟨4386291417444350650048181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924194278296233766698787 4386291417444350650048181)
                  ·
                    refine ⟨411214820385407873442017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4386291417444350650048181 411214820385407873442017)
                    ·
                      rfl

theorem cell22_1201257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_1201257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201257 prefixEnd_1201257 := by exact prefixLift 1201257
  have htrace : WordTrace (prefixWord ++ tailWord_1201257) baseStart_1201257 baseEnd_1201257 := by
    simpa [prefixWord, tailWord_1201257, baseEnd_1201257] using wordTrace_append hprefix tailTrace_1201257
  have hstable : (prefixWord ++ tailWord_1201257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201257).length < 2 ^ (prefixWord ++ tailWord_1201257).sum := by decide
  have hdescent : baseEnd_1201257 < baseStart_1201257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201272 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1201272 : Nat := 118140960795 + 1201272 * 2 ^ 59
def prefixEnd_1201272 : Nat := 4983230072969 + 3 ^ 40 * 1201272 * 2
def baseEnd_1201272 : Nat := 411219955191952834316971

theorem tailTrace_1201272 : CollatzResearch.WordTrace tailWord_1201272 prefixEnd_1201272 411219955191952834316971 := by
  unfold tailWord_1201272
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906994652002089884507035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29209326202669453179342713 21906994652002089884507035)
  ·
    refine ⟨32860491978003134826760553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906994652002089884507035 32860491978003134826760553)
    ·
      refine ⟨24645368983502351120070415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32860491978003134826760553 24645368983502351120070415)
      ·
        refine ⟨36968053475253526680105623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24645368983502351120070415 36968053475253526680105623)
        ·
          refine ⟨55452080212880290020158435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36968053475253526680105623 55452080212880290020158435)
          ·
            refine ⟨83178120319320435030237653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55452080212880290020158435 83178120319320435030237653)
            ·
              refine ⟨1949487194984072696021195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83178120319320435030237653 1949487194984072696021195)
              ·
                refine ⟨2924230792476109044031793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949487194984072696021195 2924230792476109044031793)
                ·
                  refine ⟨2193173094357081783023845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924230792476109044031793 2193173094357081783023845)
                  ·
                    refine ⟨411219955191952834316971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193173094357081783023845 411219955191952834316971)
                    ·
                      rfl

theorem cell22_1201272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1201272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201272 prefixEnd_1201272 := by exact prefixLift 1201272
  have htrace : WordTrace (prefixWord ++ tailWord_1201272) baseStart_1201272 baseEnd_1201272 := by
    simpa [prefixWord, tailWord_1201272, baseEnd_1201272] using wordTrace_append hprefix tailTrace_1201272
  have hstable : (prefixWord ++ tailWord_1201272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201272).length < 2 ^ (prefixWord ++ tailWord_1201272).sum := by decide
  have hdescent : baseEnd_1201272 < baseStart_1201272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201411 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 4]
def baseStart_1201411 : Nat := 118140960795 + 1201411 * 2 ^ 59
def prefixEnd_1201411 : Nat := 4983230072969 + 3 ^ 40 * 1201411 * 2
def baseEnd_1201411 : Nat := 137089179244200935030515

theorem tailTrace_1201411 : CollatzResearch.WordTrace tailWord_1201411 prefixEnd_1201411 137089179244200935030515 := by
  unfold tailWord_1201411
  simp only [CollatzResearch.WordTrace]
  refine ⟨43819059050500606508324087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29212706033667071005549391 43819059050500606508324087)
  ·
    refine ⟨65728588575750909762486131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43819059050500606508324087 65728588575750909762486131)
    ·
      refine ⟨98592882863626364643729197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65728588575750909762486131 98592882863626364643729197)
      ·
        refine ⟨36972331073859886741398449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98592882863626364643729197 36972331073859886741398449)
        ·
          refine ⟨27729248305394915056048837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36972331073859886741398449 27729248305394915056048837)
          ·
            refine ⟨5199234057261546573009157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27729248305394915056048837 5199234057261546573009157)
            ·
              refine ⟨974856385736539982439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5199234057261546573009157 974856385736539982439217)
              ·
                refine ⟨731142289302404986829413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974856385736539982439217 731142289302404986829413)
                ·
                  refine ⟨137089179244200935030515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731142289302404986829413 137089179244200935030515)
                  ·
                    rfl

theorem cell22_1201411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 4].length) (baseStart_1201411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201411 prefixEnd_1201411 := by exact prefixLift 1201411
  have htrace : WordTrace (prefixWord ++ tailWord_1201411) baseStart_1201411 baseEnd_1201411 := by
    simpa [prefixWord, tailWord_1201411, baseEnd_1201411] using wordTrace_append hprefix tailTrace_1201411
  have hstable : (prefixWord ++ tailWord_1201411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201411).length < 2 ^ (prefixWord ++ tailWord_1201411).sum := by decide
  have hdescent : baseEnd_1201411 < baseStart_1201411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201471 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 3, 3]
def baseStart_1201471 : Nat := 118140960795 + 1201471 * 2 ^ 59
def prefixEnd_1201471 : Nat := 4983230072969 + 3 ^ 40 * 1201471 * 2
def baseEnd_1201471 : Nat := 411288076958782648591361

theorem tailTrace_1201471 : CollatzResearch.WordTrace tailWord_1201471 prefixEnd_1201471 411288076958782648591361 := by
  unfold tailWord_1201471
  simp only [CollatzResearch.WordTrace]
  refine ⟨43821247430283236755508267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29214164953522157837005511 43821247430283236755508267)
  ·
    refine ⟨65731871145424855133262401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43821247430283236755508267 65731871145424855133262401)
    ·
      refine ⟨49298903359068641349946801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65731871145424855133262401 49298903359068641349946801)
      ·
        refine ⟨36974177519301481012460101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49298903359068641349946801 36974177519301481012460101)
        ·
          refine ⟨6932658284869027689836269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36974177519301481012460101 6932658284869027689836269)
          ·
            refine ⟨2599746856825885383688601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6932658284869027689836269 2599746856825885383688601)
            ·
              refine ⟨1949810142619414037766451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599746856825885383688601 1949810142619414037766451)
              ·
                refine ⟨2924715213929121056649677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949810142619414037766451 2924715213929121056649677)
                ·
                  refine ⟨1096768205223420396243629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2924715213929121056649677 1096768205223420396243629)
                  ·
                    refine ⟨411288076958782648591361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096768205223420396243629 411288076958782648591361)
                    ·
                      rfl

theorem cell22_1201471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_1201471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201471 prefixEnd_1201471 := by exact prefixLift 1201471
  have htrace : WordTrace (prefixWord ++ tailWord_1201471) baseStart_1201471 baseEnd_1201471 := by
    simpa [prefixWord, tailWord_1201471, baseEnd_1201471] using wordTrace_append hprefix tailTrace_1201471
  have hstable : (prefixWord ++ tailWord_1201471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201471).length < 2 ^ (prefixWord ++ tailWord_1201471).sum := by decide
  have hdescent : baseEnd_1201471 < baseStart_1201471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201529 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 6]
def baseStart_1201529 : Nat := 118140960795 + 1201529 * 2 ^ 59
def prefixEnd_1201529 : Nat := 4983230072969 + 3 ^ 40 * 1201529 * 2
def baseEnd_1201529 : Nat := 137102643848029943547061

theorem tailTrace_1201529 : CollatzResearch.WordTrace tailWord_1201529 prefixEnd_1201529 137102643848029943547061 := by
  unfold tailWord_1201529
  simp only [CollatzResearch.WordTrace]
  refine ⟨43823362864073112661119641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29215575242715408440746427 43823362864073112661119641)
  ·
    refine ⟨32867522148054834495839731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43823362864073112661119641 32867522148054834495839731)
    ·
      refine ⟨49301283222082251743759597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32867522148054834495839731 49301283222082251743759597)
      ·
        refine ⟨18487981208280844403909849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49301283222082251743759597 18487981208280844403909849)
        ·
          refine ⟨13865985906210633302932387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18487981208280844403909849 13865985906210633302932387)
          ·
            refine ⟨20798978859315949954398581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13865985906210633302932387 20798978859315949954398581)
            ·
              refine ⟨1949904268060870308224867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20798978859315949954398581 1949904268060870308224867)
              ·
                refine ⟨2924856402091305462337301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949904268060870308224867 2924856402091305462337301)
                ·
                  refine ⟨137102643848029943547061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2924856402091305462337301 137102643848029943547061)
                  ·
                    rfl

theorem cell22_1201529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_1201529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201529 prefixEnd_1201529 := by exact prefixLift 1201529
  have htrace : WordTrace (prefixWord ++ tailWord_1201529) baseStart_1201529 baseEnd_1201529 := by
    simpa [prefixWord, tailWord_1201529, baseEnd_1201529] using wordTrace_append hprefix tailTrace_1201529
  have hstable : (prefixWord ++ tailWord_1201529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201529).length < 2 ^ (prefixWord ++ tailWord_1201529).sum := by decide
  have hdescent : baseEnd_1201529 < baseStart_1201529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201698 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1201698 : Nat := 118140960795 + 1201698 * 2 ^ 59
def prefixEnd_1201698 : Nat := 4983230072969 + 3 ^ 40 * 1201698 * 2
def baseEnd_1201698 : Nat := 137121927899276574388555

theorem tailTrace_1201698 : CollatzResearch.WordTrace tailWord_1201698 prefixEnd_1201698 137121927899276574388555 := by
  unfold tailWord_1201698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10957381700115213631005437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29219684533640569682681165 10957381700115213631005437)
  ·
    refine ⟨4109018137543205111627039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10957381700115213631005437 4109018137543205111627039)
    ·
      refine ⟨6163527206314807667440559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109018137543205111627039 6163527206314807667440559)
      ·
        refine ⟨9245290809472211501160839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163527206314807667440559 9245290809472211501160839)
        ·
          refine ⟨13867936214208317251741259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245290809472211501160839 13867936214208317251741259)
          ·
            refine ⟨20801904321312475877611889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13867936214208317251741259 20801904321312475877611889)
            ·
              refine ⟨15601428240984356908208917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20801904321312475877611889 15601428240984356908208917)
              ·
                refine ⟨731316948796141730072293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15601428240984356908208917 731316948796141730072293)
                ·
                  refine ⟨137121927899276574388555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731316948796141730072293 137121927899276574388555)
                  ·
                    rfl

theorem cell22_1201698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1201698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201698 prefixEnd_1201698 := by exact prefixLift 1201698
  have htrace : WordTrace (prefixWord ++ tailWord_1201698) baseStart_1201698 baseEnd_1201698 := by
    simpa [prefixWord, tailWord_1201698, baseEnd_1201698] using wordTrace_append hprefix tailTrace_1201698
  have hstable : (prefixWord ++ tailWord_1201698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201698).length < 2 ^ (prefixWord ++ tailWord_1201698).sum := by decide
  have hdescent : baseEnd_1201698 < baseStart_1201698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201734 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1201734 : Nat := 118140960795 + 1201734 * 2 ^ 59
def prefixEnd_1201734 : Nat := 4983230072969 + 3 ^ 40 * 1201734 * 2
def baseEnd_1201734 : Nat := 411378107233537629265555

theorem tailTrace_1201734 : CollatzResearch.WordTrace tailWord_1201734 prefixEnd_1201734 411378107233537629265555 := by
  unfold tailWord_1201734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369713744635326021010383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29220559885553621781554837 1369713744635326021010383)
  ·
    refine ⟨2054570616952989031515575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1369713744635326021010383 2054570616952989031515575)
    ·
      refine ⟨3081855925429483547273363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054570616952989031515575 3081855925429483547273363)
      ·
        refine ⟨4622783888144225320910045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081855925429483547273363 4622783888144225320910045)
        ·
          refine ⟨1733543958054084495341267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4622783888144225320910045 1733543958054084495341267)
          ·
            refine ⟨2600315937081126743011901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733543958054084495341267 2600315937081126743011901)
            ·
              refine ⟨975118476405422528629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2600315937081126743011901 975118476405422528629463)
              ·
                refine ⟨1462677714608133792944195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975118476405422528629463 1462677714608133792944195)
                ·
                  refine ⟨2194016571912200689416293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462677714608133792944195 2194016571912200689416293)
                  ·
                    refine ⟨411378107233537629265555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194016571912200689416293 411378107233537629265555)
                    ·
                      rfl

theorem cell22_1201734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1201734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201734 prefixEnd_1201734 := by exact prefixLift 1201734
  have htrace : WordTrace (prefixWord ++ tailWord_1201734) baseStart_1201734 baseEnd_1201734 := by
    simpa [prefixWord, tailWord_1201734, baseEnd_1201734] using wordTrace_append hprefix tailTrace_1201734
  have hstable : (prefixWord ++ tailWord_1201734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201734).length < 2 ^ (prefixWord ++ tailWord_1201734).sum := by decide
  have hdescent : baseEnd_1201734 < baseStart_1201734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201822 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1201822 : Nat := 118140960795 + 1201822 * 2 ^ 59
def prefixEnd_1201822 : Nat := 4983230072969 + 3 ^ 40 * 1201822 * 2
def baseEnd_1201822 : Nat := 137136077143978244355095

theorem tailTrace_1201822 : CollatzResearch.WordTrace tailWord_1201822 prefixEnd_1201822 137136077143978244355095 := by
  unfold tailWord_1201822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479256181501452962691965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29222699634674415801023813 5479256181501452962691965)
  ·
    refine ⟨2054721068063044861009487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5479256181501452962691965 2054721068063044861009487)
    ·
      refine ⟨3082081602094567291514231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054721068063044861009487 3082081602094567291514231)
      ·
        refine ⟨4623122403141850937271347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082081602094567291514231 4623122403141850937271347)
        ·
          refine ⟨6934683604712776405907021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623122403141850937271347 6934683604712776405907021)
          ·
            refine ⟨2600506351767291152215133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6934683604712776405907021 2600506351767291152215133)
            ·
              refine ⟨975189881912734182080675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2600506351767291152215133 975189881912734182080675)
              ·
                refine ⟨1462784822869101273121013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975189881912734182080675 1462784822869101273121013)
                ·
                  refine ⟨137136077143978244355095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462784822869101273121013 137136077143978244355095)
                  ·
                    rfl

theorem cell22_1201822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1201822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201822 prefixEnd_1201822 := by exact prefixLift 1201822
  have htrace : WordTrace (prefixWord ++ tailWord_1201822) baseStart_1201822 baseEnd_1201822 := by
    simpa [prefixWord, tailWord_1201822, baseEnd_1201822] using wordTrace_append hprefix tailTrace_1201822
  have hstable : (prefixWord ++ tailWord_1201822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201822).length < 2 ^ (prefixWord ++ tailWord_1201822).sum := by decide
  have hdescent : baseEnd_1201822 < baseStart_1201822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201850 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_1201850 : Nat := 118140960795 + 1201850 * 2 ^ 59
def prefixEnd_1201850 : Nat := 4983230072969 + 3 ^ 40 * 1201850 * 2
def baseEnd_1201850 : Nat := 137139272134717331121733

theorem tailTrace_1201850 : CollatzResearch.WordTrace tailWord_1201850 prefixEnd_1201850 137139272134717331121733 := by
  unfold tailWord_1201850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958767673977546120888751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29223380463940122989036669 10958767673977546120888751)
  ·
    refine ⟨16438151510966319181333127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958767673977546120888751 16438151510966319181333127)
    ·
      refine ⟨24657227266449478771999691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16438151510966319181333127 24657227266449478771999691)
      ·
        refine ⟨36985840899674218157999537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24657227266449478771999691 36985840899674218157999537)
        ·
          refine ⟨27739380674755663618499653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36985840899674218157999537 27739380674755663618499653)
          ·
            refine ⟨5201133876516686928468685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27739380674755663618499653 5201133876516686928468685)
            ·
              refine ⟨1950425203693757598175757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5201133876516686928468685 1950425203693757598175757)
              ·
                refine ⟨731409451385159099315909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950425203693757598175757 731409451385159099315909)
                ·
                  refine ⟨137139272134717331121733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731409451385159099315909 137139272134717331121733)
                  ·
                    rfl

theorem cell22_1201850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_1201850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201850 prefixEnd_1201850 := by exact prefixLift 1201850
  have htrace : WordTrace (prefixWord ++ tailWord_1201850) baseStart_1201850 baseEnd_1201850 := by
    simpa [prefixWord, tailWord_1201850, baseEnd_1201850] using wordTrace_append hprefix tailTrace_1201850
  have hstable : (prefixWord ++ tailWord_1201850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201850).length < 2 ^ (prefixWord ++ tailWord_1201850).sum := by decide
  have hdescent : baseEnd_1201850 < baseStart_1201850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201863 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1201863 : Nat := 118140960795 + 1201863 * 2 ^ 59
def prefixEnd_1201863 : Nat := 4983230072969 + 3 ^ 40 * 1201863 * 2
def baseEnd_1201863 : Nat := 411422266569824292790159

theorem tailTrace_1201863 : CollatzResearch.WordTrace tailWord_1201863 prefixEnd_1201863 411422266569824292790159 := by
  unfold tailWord_1201863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43835544844863087703778243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29223696563242058469185495 43835544844863087703778243)
  ·
    refine ⟨65753317267294631555667365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43835544844863087703778243 65753317267294631555667365)
    ·
      refine ⟨12328746987617743416687631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65753317267294631555667365 12328746987617743416687631)
      ·
        refine ⟨18493120481426615125031447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12328746987617743416687631 18493120481426615125031447)
        ·
          refine ⟨27739680722139922687547171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18493120481426615125031447 27739680722139922687547171)
          ·
            refine ⟨41609521083209884031320757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27739680722139922687547171 41609521083209884031320757)
            ·
              refine ⟨3900892601550926627936321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41609521083209884031320757 3900892601550926627936321)
              ·
                refine ⟨2925669451163194970952241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900892601550926627936321 2925669451163194970952241)
                ·
                  refine ⟨2194252088372396228214181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925669451163194970952241 2194252088372396228214181)
                  ·
                    refine ⟨411422266569824292790159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194252088372396228214181 411422266569824292790159)
                    ·
                      rfl

theorem cell22_1201863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1201863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201863 prefixEnd_1201863 := by exact prefixLift 1201863
  have htrace : WordTrace (prefixWord ++ tailWord_1201863) baseStart_1201863 baseEnd_1201863 := by
    simpa [prefixWord, tailWord_1201863, baseEnd_1201863] using wordTrace_append hprefix tailTrace_1201863
  have hstable : (prefixWord ++ tailWord_1201863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201863).length < 2 ^ (prefixWord ++ tailWord_1201863).sum := by decide
  have hdescent : baseEnd_1201863 < baseStart_1201863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201882 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_1201882 : Nat := 118140960795 + 1201882 * 2 ^ 59
def prefixEnd_1201882 : Nat := 4983230072969 + 3 ^ 40 * 1201882 * 2
def baseEnd_1201882 : Nat := 411428770658114576565101

theorem tailTrace_1201882 : CollatzResearch.WordTrace tailWord_1201882 prefixEnd_1201882 411428770658114576565101 := by
  unfold tailWord_1201882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10959059457948563487179975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29224158554529502632479933 10959059457948563487179975)
  ·
    refine ⟨16438589186922845230769963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10959059457948563487179975 16438589186922845230769963)
    ·
      refine ⟨24657883780384267846154945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16438589186922845230769963 24657883780384267846154945)
      ·
        refine ⟨18493412835288200884616209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24657883780384267846154945 18493412835288200884616209)
        ·
          refine ⟨13870059626466150663462157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18493412835288200884616209 13870059626466150663462157)
          ·
            refine ⟨5201272359924806498798309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13870059626466150663462157 5201272359924806498798309)
            ·
              refine ⟨975238567485901218524683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5201272359924806498798309 975238567485901218524683)
              ·
                refine ⟨1462857851228851827787025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975238567485901218524683 1462857851228851827787025)
                ·
                  refine ⟨1097143388421638870840269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462857851228851827787025 1097143388421638870840269)
                  ·
                    refine ⟨411428770658114576565101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097143388421638870840269 411428770658114576565101)
                    ·
                      rfl

theorem cell22_1201882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_1201882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201882 prefixEnd_1201882 := by exact prefixLift 1201882
  have htrace : WordTrace (prefixWord ++ tailWord_1201882) baseStart_1201882 baseEnd_1201882 := by
    simpa [prefixWord, tailWord_1201882, baseEnd_1201882] using wordTrace_append hprefix tailTrace_1201882
  have hstable : (prefixWord ++ tailWord_1201882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201882).length < 2 ^ (prefixWord ++ tailWord_1201882).sum := by decide
  have hdescent : baseEnd_1201882 < baseStart_1201882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201923 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 5]
def baseStart_1201923 : Nat := 118140960795 + 1201923 * 2 ^ 59
def prefixEnd_1201923 : Nat := 4983230072969 + 3 ^ 40 * 1201923 * 2
def baseEnd_1201923 : Nat := 137147601932001378763325

theorem tailTrace_1201923 : CollatzResearch.WordTrace tailWord_1201923 prefixEnd_1201923 137147601932001378763325 := by
  unfold tailWord_1201923
  simp only [CollatzResearch.WordTrace]
  refine ⟨43837733224645717950962423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29225155483097145300641615 43837733224645717950962423)
  ·
    refine ⟨65756599836968576926443635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43837733224645717950962423 65756599836968576926443635)
    ·
      refine ⟨98634899755452865389665453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65756599836968576926443635 98634899755452865389665453)
      ·
        refine ⟨36988087408294824521124545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98634899755452865389665453 36988087408294824521124545)
        ·
          refine ⟨27741065556221118390843409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36988087408294824521124545 27741065556221118390843409)
          ·
            refine ⟨20805799167165838793132557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27741065556221118390843409 20805799167165838793132557)
            ·
              refine ⟨7802174687687189547424709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20805799167165838793132557 7802174687687189547424709)
              ·
                refine ⟨1462907753941348040142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7802174687687189547424709 1462907753941348040142133)
                ·
                  refine ⟨137147601932001378763325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462907753941348040142133 137147601932001378763325)
                  ·
                    rfl

theorem cell22_1201923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 5].length) (baseStart_1201923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201923 prefixEnd_1201923 := by exact prefixLift 1201923
  have htrace : WordTrace (prefixWord ++ tailWord_1201923) baseStart_1201923 baseEnd_1201923 := by
    simpa [prefixWord, tailWord_1201923, baseEnd_1201923] using wordTrace_append hprefix tailTrace_1201923
  have hstable : (prefixWord ++ tailWord_1201923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201923).length < 2 ^ (prefixWord ++ tailWord_1201923).sum := by decide
  have hdescent : baseEnd_1201923 < baseStart_1201923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201974 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1201974 : Nat := 118140960795 + 1201974 * 2 ^ 59
def prefixEnd_1201974 : Nat := 4983230072969 + 3 ^ 40 * 1201974 * 2
def baseEnd_1201974 : Nat := 137153421379419001088273

theorem tailTrace_1201974 : CollatzResearch.WordTrace tailWord_1201974 prefixEnd_1201974 137153421379419001088273 := by
  unfold tailWord_1201974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739974584216309603816811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29226395564973969107379317 2739974584216309603816811)
  ·
    refine ⟨4109961876324464405725217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739974584216309603816811 4109961876324464405725217)
    ·
      refine ⟨3082471407243348304293913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4109961876324464405725217 3082471407243348304293913)
      ·
        refine ⟨2311853555432511228220435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3082471407243348304293913 2311853555432511228220435)
        ·
          refine ⟨3467780333148766842330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311853555432511228220435 3467780333148766842330653)
          ·
            refine ⟨1300417624930787565873995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3467780333148766842330653 1300417624930787565873995)
            ·
              refine ⟨1950626437396181348810993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300417624930787565873995 1950626437396181348810993)
              ·
                refine ⟨1462969828047136011608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950626437396181348810993 1462969828047136011608245)
                ·
                  refine ⟨137153421379419001088273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462969828047136011608245 137153421379419001088273)
                  ·
                    rfl

theorem cell22_1201974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1201974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1201974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1201974 prefixEnd_1201974 := by exact prefixLift 1201974
  have htrace : WordTrace (prefixWord ++ tailWord_1201974) baseStart_1201974 baseEnd_1201974 := by
    simpa [prefixWord, tailWord_1201974, baseEnd_1201974] using wordTrace_append hprefix tailTrace_1201974
  have hstable : (prefixWord ++ tailWord_1201974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201974).length < 2 ^ (prefixWord ++ tailWord_1201974).sum := by decide
  have hdescent : baseEnd_1201974 < baseStart_1201974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202019 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 4]
def baseStart_1202019 : Nat := 118140960795 + 1202019 * 2 ^ 59
def prefixEnd_1202019 : Nat := 4983230072969 + 3 ^ 40 * 1202019 * 2
def baseEnd_1202019 : Nat := 137158556185963961963227

theorem tailTrace_1202019 : CollatzResearch.WordTrace tailWord_1202019 prefixEnd_1202019 137158556185963961963227 := by
  unfold tailWord_1202019
  simp only [CollatzResearch.WordTrace]
  refine ⟨43841234632297926346457111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29227489754865284230971407 43841234632297926346457111)
  ·
    refine ⟨65761851948446889519685667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43841234632297926346457111 65761851948446889519685667)
    ·
      refine ⟨98642777922670334279528501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65761851948446889519685667 98642777922670334279528501)
      ·
        refine ⟨9247760430250343838705797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98642777922670334279528501 9247760430250343838705797)
        ·
          refine ⟨1733955080671939469757337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9247760430250343838705797 1733955080671939469757337)
          ·
            refine ⟨1300466310503954602318003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733955080671939469757337 1300466310503954602318003)
            ·
              refine ⟨1950699465755931903477005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300466310503954602318003 1950699465755931903477005)
              ·
                refine ⟨731512299658474463803877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950699465755931903477005 731512299658474463803877)
                ·
                  refine ⟨137158556185963961963227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731512299658474463803877 137158556185963961963227)
                  ·
                    rfl

theorem cell22_1202019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 4].length) (baseStart_1202019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202019 prefixEnd_1202019 := by exact prefixLift 1202019
  have htrace : WordTrace (prefixWord ++ tailWord_1202019) baseStart_1202019 baseEnd_1202019 := by
    simpa [prefixWord, tailWord_1202019, baseEnd_1202019] using wordTrace_append hprefix tailTrace_1202019
  have hstable : (prefixWord ++ tailWord_1202019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202019).length < 2 ^ (prefixWord ++ tailWord_1202019).sum := by decide
  have hdescent : baseEnd_1202019 < baseStart_1202019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202030 : List Nat := [4, 1, 2, 3, 1, 1, 10]
def baseStart_1202030 : Nat := 118140960795 + 1202030 * 2 ^ 59
def prefixEnd_1202030 : Nat := 4983230072969 + 3 ^ 40 * 1202030 * 2
def baseEnd_1202030 : Nat := 15239979040099686069061

theorem tailTrace_1202030 : CollatzResearch.WordTrace tailWord_1202030 prefixEnd_1202030 15239979040099686069061 := by
  unfold tailWord_1202030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480204479407259403138443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29227757223505383483405029 5480204479407259403138443)
  ·
    refine ⟨8220306719110889104707665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5480204479407259403138443 8220306719110889104707665)
    ·
      refine ⟨6165230039333166828530749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8220306719110889104707665 6165230039333166828530749)
      ·
        refine ⟨2311961264749937560699031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6165230039333166828530749 2311961264749937560699031)
        ·
          refine ⟨3467941897124906341048547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311961264749937560699031 3467941897124906341048547)
          ·
            refine ⟨5201912845687359511572821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467941897124906341048547 5201912845687359511572821)
            ·
              refine ⟨15239979040099686069061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5201912845687359511572821 15239979040099686069061)
              ·
                rfl

theorem cell22_1202030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 10].length) (baseStart_1202030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202030 prefixEnd_1202030 := by exact prefixLift 1202030
  have htrace : WordTrace (prefixWord ++ tailWord_1202030) baseStart_1202030 baseEnd_1202030 := by
    simpa [prefixWord, tailWord_1202030, baseEnd_1202030] using wordTrace_append hprefix tailTrace_1202030
  have hstable : (prefixWord ++ tailWord_1202030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202030).length < 2 ^ (prefixWord ++ tailWord_1202030).sum := by decide
  have hdescent : baseEnd_1202030 < baseStart_1202030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202043 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_1202043 : Nat := 118140960795 + 1202043 * 2 ^ 59
def prefixEnd_1202043 : Nat := 4983230072969 + 3 ^ 40 * 1202043 * 2
def baseEnd_1202043 : Nat := 411483884248363823289607

theorem tailTrace_1202043 : CollatzResearch.WordTrace tailWord_1202043 prefixEnd_1202043 411483884248363823289607 := by
  unfold tailWord_1202043
  simp only [CollatzResearch.WordTrace]
  refine ⟨43842109984210978445330783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29228073322807318963553855 43842109984210978445330783)
  ·
    refine ⟨65763164976316467667996175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43842109984210978445330783 65763164976316467667996175)
    ·
      refine ⟨98644747464474701501994263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65763164976316467667996175 98644747464474701501994263)
      ·
        refine ⟨147967121196712052252991395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98644747464474701501994263 147967121196712052252991395)
        ·
          refine ⟨221950681795068078379487093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147967121196712052252991395 221950681795068078379487093)
          ·
            refine ⟨20807876418287632348076915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221950681795068078379487093 20807876418287632348076915)
            ·
              refine ⟨31211814627431448522115373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20807876418287632348076915 31211814627431448522115373)
              ·
                refine ⟨11704430485286793195793265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31211814627431448522115373 11704430485286793195793265)
                ·
                  refine ⟨8778322863965094896844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11704430485286793195793265 8778322863965094896844949)
                  ·
                    refine ⟨411483884248363823289607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8778322863965094896844949 411483884248363823289607)
                    ·
                      rfl

theorem cell22_1202043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_1202043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202043 prefixEnd_1202043 := by exact prefixLift 1202043
  have htrace : WordTrace (prefixWord ++ tailWord_1202043) baseStart_1202043 baseEnd_1202043 := by
    simpa [prefixWord, tailWord_1202043, baseEnd_1202043] using wordTrace_append hprefix tailTrace_1202043
  have hstable : (prefixWord ++ tailWord_1202043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202043).length < 2 ^ (prefixWord ++ tailWord_1202043).sum := by decide
  have hdescent : baseEnd_1202043 < baseStart_1202043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202105 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_1202105 : Nat := 118140960795 + 1202105 * 2 ^ 59
def prefixEnd_1202105 : Nat := 4983230072969 + 3 ^ 40 * 1202105 * 2
def baseEnd_1202105 : Nat := 411505108115416328239417

theorem tailTrace_1202105 : CollatzResearch.WordTrace tailWord_1202105 prefixEnd_1202105 411505108115416328239417 := by
  unfold tailWord_1202105
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844371309986363034087769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29229580873324242022725179 43844371309986363034087769)
  ·
    refine ⟨32883278482489772275565827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43844371309986363034087769 32883278482489772275565827)
    ·
      refine ⟨49324917723734658413348741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32883278482489772275565827 49324917723734658413348741)
      ·
        refine ⟨9248422073200248452502889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49324917723734658413348741 9248422073200248452502889)
        ·
          refine ⟨6936316554900186339377167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248422073200248452502889 6936316554900186339377167)
          ·
            refine ⟨10404474832350279509065751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936316554900186339377167 10404474832350279509065751)
            ·
              refine ⟨15606712248525419263598627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10404474832350279509065751 15606712248525419263598627)
              ·
                refine ⟨23410068372788128895397941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15606712248525419263598627 23410068372788128895397941)
                ·
                  refine ⟨2194693909948887083943557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23410068372788128895397941 2194693909948887083943557)
                  ·
                    refine ⟨411505108115416328239417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2194693909948887083943557 411505108115416328239417)
                    ·
                      rfl

theorem cell22_1202105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_1202105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202105 prefixEnd_1202105 := by exact prefixLift 1202105
  have htrace : WordTrace (prefixWord ++ tailWord_1202105) baseStart_1202105 baseEnd_1202105 := by
    simpa [prefixWord, tailWord_1202105, baseEnd_1202105] using wordTrace_append hprefix tailTrace_1202105
  have hstable : (prefixWord ++ tailWord_1202105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202105).length < 2 ^ (prefixWord ++ tailWord_1202105).sum := by decide
  have hdescent : baseEnd_1202105 < baseStart_1202105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202120 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_1202120 : Nat := 118140960795 + 1202120 * 2 ^ 59
def prefixEnd_1202120 : Nat := 4983230072969 + 3 ^ 40 * 1202120 * 2
def baseEnd_1202120 : Nat := 137170080973987096371457

theorem tailTrace_1202120 : CollatzResearch.WordTrace tailWord_1202120 prefixEnd_1202120 137170080973987096371457 := by
  unfold tailWord_1202120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21922459202466010297941907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29229945603288013730589209 21922459202466010297941907)
  ·
    refine ⟨32883688803699015446912861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21922459202466010297941907 32883688803699015446912861)
    ·
      refine ⟨12331383301387130792592323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32883688803699015446912861 12331383301387130792592323)
      ·
        refine ⟨18497074952080696188888485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12331383301387130792592323 18497074952080696188888485)
        ·
          refine ⟨3468201553515130535416591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18497074952080696188888485 3468201553515130535416591)
          ·
            refine ⟨5202302330272695803124887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468201553515130535416591 5202302330272695803124887)
            ·
              refine ⟨7803453495409043704687331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202302330272695803124887 7803453495409043704687331)
              ·
                refine ⟨11705180243113565557030997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803453495409043704687331 11705180243113565557030997)
                ·
                  refine ⟨137170080973987096371457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11705180243113565557030997 137170080973987096371457)
                  ·
                    rfl

theorem cell22_1202120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_1202120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202120 prefixEnd_1202120 := by exact prefixLift 1202120
  have htrace : WordTrace (prefixWord ++ tailWord_1202120) baseStart_1202120 baseEnd_1202120 := by
    simpa [prefixWord, tailWord_1202120, baseEnd_1202120] using wordTrace_append hprefix tailTrace_1202120
  have hstable : (prefixWord ++ tailWord_1202120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202120).length < 2 ^ (prefixWord ++ tailWord_1202120).sum := by decide
  have hdescent : baseEnd_1202120 < baseStart_1202120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202135 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_1202135 : Nat := 118140960795 + 1202135 * 2 ^ 59
def prefixEnd_1202135 : Nat := 4983230072969 + 3 ^ 40 * 1202135 * 2
def baseEnd_1202135 : Nat := 411515377728506249989325

theorem tailTrace_1202135 : CollatzResearch.WordTrace tailWord_1202135 prefixEnd_1202135 411515377728506249989325 := by
  unfold tailWord_1202135
  simp only [CollatzResearch.WordTrace]
  refine ⟨43845465499877678157679859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29230310333251785438453239 43845465499877678157679859)
  ·
    refine ⟨65768198249816517236519789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43845465499877678157679859 65768198249816517236519789)
    ·
      refine ⟨24663074343681193963694921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65768198249816517236519789 24663074343681193963694921)
      ·
        refine ⟨18497305757760895472771191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24663074343681193963694921 18497305757760895472771191)
        ·
          refine ⟨27745958636641343209156787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18497305757760895472771191 27745958636641343209156787)
          ·
            refine ⟨41618937954962014813735181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27745958636641343209156787 41618937954962014813735181)
            ·
              refine ⟨15607101733110755555150693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41618937954962014813735181 15607101733110755555150693)
              ·
                refine ⟨2926331574958266666590755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15607101733110755555150693 2926331574958266666590755)
                ·
                  refine ⟨4389497362437399999886133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926331574958266666590755 4389497362437399999886133)
                  ·
                    refine ⟨411515377728506249989325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4389497362437399999886133 411515377728506249989325)
                    ·
                      rfl

theorem cell22_1202135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_1202135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202135 prefixEnd_1202135 := by exact prefixLift 1202135
  have htrace : WordTrace (prefixWord ++ tailWord_1202135) baseStart_1202135 baseEnd_1202135 := by
    simpa [prefixWord, tailWord_1202135, baseEnd_1202135] using wordTrace_append hprefix tailTrace_1202135
  have hstable : (prefixWord ++ tailWord_1202135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202135).length < 2 ^ (prefixWord ++ tailWord_1202135).sum := by decide
  have hdescent : baseEnd_1202135 < baseStart_1202135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202199 : List Nat := [1, 1, 3, 5, 3, 1, 8]
def baseStart_1202199 : Nat := 118140960795 + 1202199 * 2 ^ 59
def prefixEnd_1202199 : Nat := 4983230072969 + 3 ^ 40 * 1202199 * 2
def baseEnd_1202199 : Nat := 15242121712460422829227

theorem tailTrace_1202199 : CollatzResearch.WordTrace tailWord_1202199 prefixEnd_1202199 15242121712460422829227 := by
  unfold tailWord_1202199
  simp only [CollatzResearch.WordTrace]
  refine ⟨43847799771645817088009651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29231866514430544725339767 43847799771645817088009651)
  ·
    refine ⟨65771699657468725632014477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43847799771645817088009651 65771699657468725632014477)
    ·
      refine ⟨24664387371550772112005429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65771699657468725632014477 24664387371550772112005429)
      ·
        refine ⟨2312286316082884885500509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24664387371550772112005429 2312286316082884885500509)
        ·
          refine ⟨867107368531081832062691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2312286316082884885500509 867107368531081832062691)
          ·
            refine ⟨1300661052796622748094037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867107368531081832062691 1300661052796622748094037)
            ·
              refine ⟨15242121712460422829227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1300661052796622748094037 15242121712460422829227)
              ·
                rfl

theorem cell22_1202199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 8].length) (baseStart_1202199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202199 prefixEnd_1202199 := by exact prefixLift 1202199
  have htrace : WordTrace (prefixWord ++ tailWord_1202199) baseStart_1202199 baseEnd_1202199 := by
    simpa [prefixWord, tailWord_1202199, baseEnd_1202199] using wordTrace_append hprefix tailTrace_1202199
  have hstable : (prefixWord ++ tailWord_1202199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202199).length < 2 ^ (prefixWord ++ tailWord_1202199).sum := by decide
  have hdescent : baseEnd_1202199 < baseStart_1202199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202255 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 8]
def baseStart_1202255 : Nat := 118140960795 + 1202255 * 2 ^ 59
def prefixEnd_1202255 : Nat := 4983230072969 + 3 ^ 40 * 1202255 * 2
def baseEnd_1202255 : Nat := 137185485393621978996319

theorem tailTrace_1202255 : CollatzResearch.WordTrace tailWord_1202255 prefixEnd_1202255 137185485393621978996319 := by
  unfold tailWord_1202255
  simp only [CollatzResearch.WordTrace]
  refine ⟨43849842259442938652048219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29233228172961959101365479 43849842259442938652048219)
  ·
    refine ⟨65774763389164407978072329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43849842259442938652048219 65774763389164407978072329)
    ·
      refine ⟨49331072541873305983554247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65774763389164407978072329 49331072541873305983554247)
      ·
        refine ⟨73996608812809958975331371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49331072541873305983554247 73996608812809958975331371)
        ·
          refine ⟨110994913219214938462997057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73996608812809958975331371 110994913219214938462997057)
          ·
            refine ⟨83246184914411203847247793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110994913219214938462997057 83246184914411203847247793)
            ·
              refine ⟨62434638685808402885435845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83246184914411203847247793 62434638685808402885435845)
              ·
                refine ⟨11706494753589075541019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62434638685808402885435845 11706494753589075541019221)
                ·
                  refine ⟨137185485393621978996319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11706494753589075541019221 137185485393621978996319)
                  ·
                    rfl

theorem cell22_1202255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_1202255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202255 prefixEnd_1202255 := by exact prefixLift 1202255
  have htrace : WordTrace (prefixWord ++ tailWord_1202255) baseStart_1202255 baseEnd_1202255 := by
    simpa [prefixWord, tailWord_1202255, baseEnd_1202255] using wordTrace_append hprefix tailTrace_1202255
  have hstable : (prefixWord ++ tailWord_1202255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202255).length < 2 ^ (prefixWord ++ tailWord_1202255).sum := by decide
  have hdescent : baseEnd_1202255 < baseStart_1202255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202287 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_1202287 : Nat := 118140960795 + 1202287 * 2 ^ 59
def prefixEnd_1202287 : Nat := 4983230072969 + 3 ^ 40 * 1202287 * 2
def baseEnd_1202287 : Nat := 411567410434828520188859

theorem tailTrace_1202287 : CollatzResearch.WordTrace tailWord_1202287 prefixEnd_1202287 411567410434828520188859 := by
  unfold tailWord_1202287
  simp only [CollatzResearch.WordTrace]
  refine ⟨43851009395327008117213115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29234006263551338744808743 43851009395327008117213115)
  ·
    refine ⟨65776514092990512175819673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43851009395327008117213115 65776514092990512175819673)
    ·
      refine ⟨49332385569742884131864755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65776514092990512175819673 49332385569742884131864755)
      ·
        refine ⟨73998578354614326197797133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49332385569742884131864755 73998578354614326197797133)
        ·
          refine ⟨27749466882980372324173925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73998578354614326197797133 27749466882980372324173925)
          ·
            refine ⟨5203025040558819810782611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27749466882980372324173925 5203025040558819810782611)
            ·
              refine ⟨7804537560838229716173917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203025040558819810782611 7804537560838229716173917)
              ·
                refine ⟨2926701585314336143565219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7804537560838229716173917 2926701585314336143565219)
                ·
                  refine ⟨4390052377971504215347829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926701585314336143565219 4390052377971504215347829)
                  ·
                    refine ⟨411567410434828520188859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4390052377971504215347829 411567410434828520188859)
                    ·
                      rfl

theorem cell22_1202287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_1202287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202287 prefixEnd_1202287 := by exact prefixLift 1202287
  have htrace : WordTrace (prefixWord ++ tailWord_1202287) baseStart_1202287 baseEnd_1202287 := by
    simpa [prefixWord, tailWord_1202287, baseEnd_1202287] using wordTrace_append hprefix tailTrace_1202287
  have hstable : (prefixWord ++ tailWord_1202287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202287).length < 2 ^ (prefixWord ++ tailWord_1202287).sum := by decide
  have hdescent : baseEnd_1202287 < baseStart_1202287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202362 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_1202362 : Nat := 118140960795 + 1202362 * 2 ^ 59
def prefixEnd_1202362 : Nat := 4983230072969 + 3 ^ 40 * 1202362 * 2
def baseEnd_1202362 : Nat := 137197694822517774854543

theorem tailTrace_1202362 : CollatzResearch.WordTrace tailWord_1202362 prefixEnd_1202362 137197694822517774854543 := by
  unfold tailWord_1202362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963436217513823981548335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29235829913370197284128893 10963436217513823981548335)
  ·
    refine ⟨16445154326270735972322503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963436217513823981548335 16445154326270735972322503)
    ·
      refine ⟨24667731489406103958483755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445154326270735972322503 24667731489406103958483755)
      ·
        refine ⟨37001597234109155937725633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24667731489406103958483755 37001597234109155937725633)
        ·
          refine ⟨27751197925581866953294225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37001597234109155937725633 27751197925581866953294225)
          ·
            refine ⟨20813398444186400214970669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27751197925581866953294225 20813398444186400214970669)
            ·
              refine ⟨7805024416569900080614001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20813398444186400214970669 7805024416569900080614001)
              ·
                refine ⟨5853768312427425060460501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7805024416569900080614001 5853768312427425060460501)
                ·
                  refine ⟨137197694822517774854543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5853768312427425060460501 137197694822517774854543)
                  ·
                    rfl

theorem cell22_1202362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_1202362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202362 prefixEnd_1202362 := by exact prefixLift 1202362
  have htrace : WordTrace (prefixWord ++ tailWord_1202362) baseStart_1202362 baseEnd_1202362 := by
    simpa [prefixWord, tailWord_1202362, baseEnd_1202362] using wordTrace_append hprefix tailTrace_1202362
  have hstable : (prefixWord ++ tailWord_1202362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202362).length < 2 ^ (prefixWord ++ tailWord_1202362).sum := by decide
  have hdescent : baseEnd_1202362 < baseStart_1202362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202377 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1202377 : Nat := 118140960795 + 1202377 * 2 ^ 59
def prefixEnd_1202377 : Nat := 4983230072969 + 3 ^ 40 * 1202377 * 2
def baseEnd_1202377 : Nat := 411598219274098285438583

theorem tailTrace_1202377 : CollatzResearch.WordTrace tailWord_1202377 prefixEnd_1202377 411598219274098285438583 := by
  unfold tailWord_1202377
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854291965000953487989385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29236194643333968991992923 43854291965000953487989385)
  ·
    refine ⟨32890718973750715115992039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43854291965000953487989385 32890718973750715115992039)
    ·
      refine ⟨49336078460626072673988059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890718973750715115992039 49336078460626072673988059)
      ·
        refine ⟨74004117690939109010982089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49336078460626072673988059 74004117690939109010982089)
        ·
          refine ⟨55503088268204331758236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74004117690939109010982089 55503088268204331758236567)
          ·
            refine ⟨83254632402306497637354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55503088268204331758236567 83254632402306497637354851)
            ·
              refine ⟨124881948603459746456032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83254632402306497637354851 124881948603459746456032277)
              ·
                refine ⟨5853841340787175615126513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124881948603459746456032277 5853841340787175615126513)
                ·
                  refine ⟨4390381005590381711344885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5853841340787175615126513 4390381005590381711344885)
                  ·
                    refine ⟨411598219274098285438583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4390381005590381711344885 411598219274098285438583)
                    ·
                      rfl

theorem cell22_1202377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1202377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202377 prefixEnd_1202377 := by exact prefixLift 1202377
  have htrace : WordTrace (prefixWord ++ tailWord_1202377) baseStart_1202377 baseEnd_1202377 := by
    simpa [prefixWord, tailWord_1202377, baseEnd_1202377] using wordTrace_append hprefix tailTrace_1202377
  have hstable : (prefixWord ++ tailWord_1202377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202377).length < 2 ^ (prefixWord ++ tailWord_1202377).sum := by decide
  have hdescent : baseEnd_1202377 < baseStart_1202377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202383 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 1, 3]
def baseStart_1202383 : Nat := 118140960795 + 1202383 * 2 ^ 59
def prefixEnd_1202383 : Nat := 4983230072969 + 3 ^ 40 * 1202383 * 2
def baseEnd_1202383 : Nat := 411600273196716269788565

theorem tailTrace_1202383 : CollatzResearch.WordTrace tailWord_1202383 prefixEnd_1202383 411600273196716269788565 := by
  unfold tailWord_1202383
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854510802979216512707803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29236340535319477675138535 43854510802979216512707803)
  ·
    refine ⟨65781766204468824769061705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43854510802979216512707803 65781766204468824769061705)
    ·
      refine ⟨49336324653351618576796279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65781766204468824769061705 49336324653351618576796279)
      ·
        refine ⟨74004486980027427865194419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49336324653351618576796279 74004486980027427865194419)
        ·
          refine ⟨111006730470041141797791629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74004486980027427865194419 111006730470041141797791629)
          ·
            refine ⟨41627523926265428174171861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111006730470041141797791629 41627523926265428174171861)
            ·
              refine ⟨975645092021845972832153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41627523926265428174171861 975645092021845972832153)
              ·
                refine ⟨731733819016384479624115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975645092021845972832153 731733819016384479624115)
                ·
                  refine ⟨1097600728524576719436173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731733819016384479624115 1097600728524576719436173)
                  ·
                    refine ⟨411600273196716269788565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097600728524576719436173 411600273196716269788565)
                    ·
                      rfl

theorem cell22_1202383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_1202383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202383 prefixEnd_1202383 := by exact prefixLift 1202383
  have htrace : WordTrace (prefixWord ++ tailWord_1202383) baseStart_1202383 baseEnd_1202383 := by
    simpa [prefixWord, tailWord_1202383, baseEnd_1202383] using wordTrace_append hprefix tailTrace_1202383
  have hstable : (prefixWord ++ tailWord_1202383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202383).length < 2 ^ (prefixWord ++ tailWord_1202383).sum := by decide
  have hdescent : baseEnd_1202383 < baseStart_1202383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202441 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 4]
def baseStart_1202441 : Nat := 118140960795 + 1202441 * 2 ^ 59
def prefixEnd_1202441 : Nat := 4983230072969 + 3 ^ 40 * 1202441 * 2
def baseEnd_1202441 : Nat := 137206709260674483946129

theorem tailTrace_1202441 : CollatzResearch.WordTrace tailWord_1202441 prefixEnd_1202441 137206709260674483946129 := by
  unfold tailWord_1202441
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856626236769092418319177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29237750824512728278879451 43856626236769092418319177)
  ·
    refine ⟨32892469677576819313739383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43856626236769092418319177 32892469677576819313739383)
    ·
      refine ⟨49338704516365228970609075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32892469677576819313739383 49338704516365228970609075)
      ·
        refine ⟨74008056774547843455913613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49338704516365228970609075 74008056774547843455913613)
        ·
          refine ⟨27753021290455441295967605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74008056774547843455913613 27753021290455441295967605)
          ·
            refine ⟨2601845745980197621496963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27753021290455441295967605 2601845745980197621496963)
            ·
              refine ⟨3902768618970296432245445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601845745980197621496963 3902768618970296432245445)
              ·
                refine ⟨731769116056930581046021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3902768618970296432245445 731769116056930581046021)
                ·
                  refine ⟨137206709260674483946129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731769116056930581046021 137206709260674483946129)
                  ·
                    rfl

theorem cell22_1202441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_1202441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202441 prefixEnd_1202441 := by exact prefixLift 1202441
  have htrace : WordTrace (prefixWord ++ tailWord_1202441) baseStart_1202441 baseEnd_1202441 := by
    simpa [prefixWord, tailWord_1202441, baseEnd_1202441] using wordTrace_append hprefix tailTrace_1202441
  have hstable : (prefixWord ++ tailWord_1202441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202441).length < 2 ^ (prefixWord ++ tailWord_1202441).sum := by decide
  have hdescent : baseEnd_1202441 < baseStart_1202441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202456 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1202456 : Nat := 118140960795 + 1202456 * 2 ^ 59
def prefixEnd_1202456 : Nat := 4983230072969 + 3 ^ 40 * 1202456 * 2
def baseEnd_1202456 : Nat := 411625262588568412713341

theorem tailTrace_1202456 : CollatzResearch.WordTrace tailWord_1202456 prefixEnd_1202456 411625262588568412713341 := by
  unfold tailWord_1202456
  simp only [CollatzResearch.WordTrace]
  refine ⟨21928586665857374990057611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29238115554476499986743481 21928586665857374990057611)
  ·
    refine ⟨32892879998786062485086417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21928586665857374990057611 32892879998786062485086417)
    ·
      refine ⟨24669659999089546863814813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32892879998786062485086417 24669659999089546863814813)
      ·
        refine ⟨9251122499658580073930555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24669659999089546863814813 9251122499658580073930555)
        ·
          refine ⟨13876683749487870110895833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9251122499658580073930555 13876683749487870110895833)
          ·
            refine ⟨10407512812115902583171875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13876683749487870110895833 10407512812115902583171875)
            ·
              refine ⟨15611269218173853874757813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407512812115902583171875 15611269218173853874757813)
              ·
                refine ⟨1463556489203798800758545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15611269218173853874757813 1463556489203798800758545)
                ·
                  refine ⟨1097667366902849100568909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463556489203798800758545 1097667366902849100568909)
                  ·
                    refine ⟨411625262588568412713341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097667366902849100568909 411625262588568412713341)
                    ·
                      rfl

theorem cell22_1202456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1202456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202456 prefixEnd_1202456 := by exact prefixLift 1202456
  have htrace : WordTrace (prefixWord ++ tailWord_1202456) baseStart_1202456 baseEnd_1202456 := by
    simpa [prefixWord, tailWord_1202456, baseEnd_1202456] using wordTrace_append hprefix tailTrace_1202456
  have hstable : (prefixWord ++ tailWord_1202456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202456).length < 2 ^ (prefixWord ++ tailWord_1202456).sum := by decide
  have hdescent : baseEnd_1202456 < baseStart_1202456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202477 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1202477 : Nat := 118140960795 + 1202477 * 2 ^ 59
def prefixEnd_1202477 : Nat := 4983230072969 + 3 ^ 40 * 1202477 * 2
def baseEnd_1202477 : Nat := 411632451317731357938277

theorem tailTrace_1202477 : CollatzResearch.WordTrace tailWord_1202477 prefixEnd_1202477 411632451317731357938277 := by
  unfold tailWord_1202477
  simp only [CollatzResearch.WordTrace]
  refine ⟨43857939264638670566629685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29238626176425780377753123 43857939264638670566629685)
  ·
    refine ⟨4111681806059875365621533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43857939264638670566629685 4111681806059875365621533)
    ·
      refine ⟨1541880677272453262108075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4111681806059875365621533 1541880677272453262108075)
      ·
        refine ⟨2312821015908679893162113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541880677272453262108075 2312821015908679893162113)
        ·
          refine ⟨1734615761931509919871585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312821015908679893162113 1734615761931509919871585)
          ·
            refine ⟨1300961821448632439903689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734615761931509919871585 1300961821448632439903689)
            ·
              refine ⟨975721366086474329927767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300961821448632439903689 975721366086474329927767)
              ·
                refine ⟨1463582049129711494891651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975721366086474329927767 1463582049129711494891651)
                ·
                  refine ⟨2195373073694567242337477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463582049129711494891651 2195373073694567242337477)
                  ·
                    refine ⟨411632451317731357938277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195373073694567242337477 411632451317731357938277)
                    ·
                      rfl

theorem cell22_1202477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1202477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202477 prefixEnd_1202477 := by exact prefixLift 1202477
  have htrace : WordTrace (prefixWord ++ tailWord_1202477) baseStart_1202477 baseEnd_1202477 := by
    simpa [prefixWord, tailWord_1202477, baseEnd_1202477] using wordTrace_append hprefix tailTrace_1202477
  have hstable : (prefixWord ++ tailWord_1202477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202477).length < 2 ^ (prefixWord ++ tailWord_1202477).sum := by decide
  have hdescent : baseEnd_1202477 < baseStart_1202477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202526 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1202526 : Nat := 118140960795 + 1202526 * 2 ^ 59
def prefixEnd_1202526 : Nat := 4983230072969 + 3 ^ 40 * 1202526 * 2
def baseEnd_1202526 : Nat := 137216408339703854487709

theorem tailTrace_1202526 : CollatzResearch.WordTrace tailWord_1202526 prefixEnd_1202526 137216408339703854487709 := by
  unfold tailWord_1202526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482465805182643991895429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29239817627640767956775621 5482465805182643991895429)
  ·
    refine ⟨1027962338471745748480393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5482465805182643991895429 1027962338471745748480393)
    ·
      refine ⟨770971753853809311360295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1027962338471745748480393 770971753853809311360295)
      ·
        refine ⟨1156457630780713967040443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770971753853809311360295 1156457630780713967040443)
        ·
          refine ⟨1734686446171070950560665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156457630780713967040443 1734686446171070950560665)
          ·
            refine ⟨1301014834628303212920499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734686446171070950560665 1301014834628303212920499)
            ·
              refine ⟨1951522251942454819380749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301014834628303212920499 1951522251942454819380749)
              ·
                refine ⟨731820844478420557267781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951522251942454819380749 731820844478420557267781)
                ·
                  refine ⟨137216408339703854487709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731820844478420557267781 137216408339703854487709)
                  ·
                    rfl

theorem cell22_1202526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1202526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202526 prefixEnd_1202526 := by exact prefixLift 1202526
  have htrace : WordTrace (prefixWord ++ tailWord_1202526) baseStart_1202526 baseEnd_1202526 := by
    simpa [prefixWord, tailWord_1202526, baseEnd_1202526] using wordTrace_append hprefix tailTrace_1202526
  have hstable : (prefixWord ++ tailWord_1202526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202526).length < 2 ^ (prefixWord ++ tailWord_1202526).sum := by decide
  have hdescent : baseEnd_1202526 < baseStart_1202526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202535 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1202535 : Nat := 118140960795 + 1202535 * 2 ^ 59
def prefixEnd_1202535 : Nat := 4983230072969 + 3 ^ 40 * 1202535 * 2
def baseEnd_1202535 : Nat := 411652305903038539988099

theorem tailTrace_1202535 : CollatzResearch.WordTrace tailWord_1202535 prefixEnd_1202535 411652305903038539988099 := by
  unfold tailWord_1202535
  simp only [CollatzResearch.WordTrace]
  refine ⟨43860054698428546472241059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29240036465619030981494039 43860054698428546472241059)
  ·
    refine ⟨65790082047642819708361589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43860054698428546472241059 65790082047642819708361589)
    ·
      refine ⟨6167820191966514347658899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65790082047642819708361589 6167820191966514347658899)
      ·
        refine ⟨9251730287949771521488349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6167820191966514347658899 9251730287949771521488349)
        ·
          refine ⟨3469398857981164320558131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9251730287949771521488349 3469398857981164320558131)
          ·
            refine ⟨5204098286971746480837197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469398857981164320558131 5204098286971746480837197)
            ·
              refine ⟨1951536857614404930313949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5204098286971746480837197 1951536857614404930313949)
              ·
                refine ⟨731826321605401848867731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951536857614404930313949 731826321605401848867731)
                ·
                  refine ⟨1097739482408102773301597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731826321605401848867731 1097739482408102773301597)
                  ·
                    refine ⟨411652305903038539988099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097739482408102773301597 411652305903038539988099)
                    ·
                      rfl

theorem cell22_1202535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1202535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202535 prefixEnd_1202535 := by exact prefixLift 1202535
  have htrace : WordTrace (prefixWord ++ tailWord_1202535) baseStart_1202535 baseEnd_1202535 := by
    simpa [prefixWord, tailWord_1202535, baseEnd_1202535] using wordTrace_append hprefix tailTrace_1202535
  have hstable : (prefixWord ++ tailWord_1202535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202535).length < 2 ^ (prefixWord ++ tailWord_1202535).sum := by decide
  have hdescent : baseEnd_1202535 < baseStart_1202535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202591 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_1202591 : Nat := 118140960795 + 1202591 * 2 ^ 59
def prefixEnd_1202591 : Nat := 4983230072969 + 3 ^ 40 * 1202591 * 2
def baseEnd_1202591 : Nat := 411671475847473060587927

theorem tailTrace_1202591 : CollatzResearch.WordTrace tailWord_1202591 prefixEnd_1202591 411671475847473060587927 := by
  unfold tailWord_1202591
  simp only [CollatzResearch.WordTrace]
  refine ⟨43862097186225668036279627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29241398124150445357519751 43862097186225668036279627)
  ·
    refine ⟨65793145779338502054419441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43862097186225668036279627 65793145779338502054419441)
    ·
      refine ⟨49344859334503876540814581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65793145779338502054419441 49344859334503876540814581)
      ·
        refine ⟨4626080562609738425701367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49344859334503876540814581 4626080562609738425701367)
        ·
          refine ⟨6939120843914607638552051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626080562609738425701367 6939120843914607638552051)
          ·
            refine ⟨10408681265871911457828077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939120843914607638552051 10408681265871911457828077)
            ·
              refine ⟨3903255474701966796685529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10408681265871911457828077 3903255474701966796685529)
              ·
                refine ⟨2927441606026475097514147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903255474701966796685529 2927441606026475097514147)
                ·
                  refine ⟨4391162409039712646271221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927441606026475097514147 4391162409039712646271221)
                  ·
                    refine ⟨411671475847473060587927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4391162409039712646271221 411671475847473060587927)
                    ·
                      rfl

theorem cell22_1202591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_1202591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202591 prefixEnd_1202591 := by exact prefixLift 1202591
  have htrace : WordTrace (prefixWord ++ tailWord_1202591) baseStart_1202591 baseEnd_1202591 := by
    simpa [prefixWord, tailWord_1202591, baseEnd_1202591] using wordTrace_append hprefix tailTrace_1202591
  have hstable : (prefixWord ++ tailWord_1202591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202591).length < 2 ^ (prefixWord ++ tailWord_1202591).sum := by decide
  have hdescent : baseEnd_1202591 < baseStart_1202591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202621 : List Nat := [1, 4, 1, 2, 2, 2, 3, 7]
def baseStart_1202621 : Nat := 118140960795 + 1202621 * 2 ^ 59
def prefixEnd_1202621 : Nat := 4983230072969 + 3 ^ 40 * 1202621 * 2
def baseEnd_1202621 : Nat := 45742416162284775815315

theorem tailTrace_1202621 : CollatzResearch.WordTrace tailWord_1202621 prefixEnd_1202621 45742416162284775815315 := by
  unfold tailWord_1202621
  simp only [CollatzResearch.WordTrace]
  refine ⟨43863191376116983159871717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29242127584077988773247811 43863191376116983159871717)
  ·
    refine ⟨8224348383021934342475947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43863191376116983159871717 8224348383021934342475947)
    ·
      refine ⟨12336522574532901513713921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8224348383021934342475947 12336522574532901513713921)
      ·
        refine ⟨9252391930899676135285441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12336522574532901513713921 9252391930899676135285441)
        ·
          refine ⟨6939293948174757101464081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252391930899676135285441 6939293948174757101464081)
          ·
            refine ⟨5204470461131067826098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6939293948174757101464081 5204470461131067826098061)
            ·
              refine ⟨1951676422924150434786773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5204470461131067826098061 1951676422924150434786773)
              ·
                refine ⟨45742416162284775815315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1951676422924150434786773 45742416162284775815315)
                ·
                  rfl

theorem cell22_1202621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 7].length) (baseStart_1202621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202621 prefixEnd_1202621 := by exact prefixLift 1202621
  have htrace : WordTrace (prefixWord ++ tailWord_1202621) baseStart_1202621 baseEnd_1202621 := by
    simpa [prefixWord, tailWord_1202621, baseEnd_1202621] using wordTrace_append hprefix tailTrace_1202621
  have hstable : (prefixWord ++ tailWord_1202621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202621).length < 2 ^ (prefixWord ++ tailWord_1202621).sum := by decide
  have hdescent : baseEnd_1202621 < baseStart_1202621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202653 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1202653 : Nat := 118140960795 + 1202653 * 2 ^ 59
def prefixEnd_1202653 : Nat := 4983230072969 + 3 ^ 40 * 1202653 * 2
def baseEnd_1202653 : Nat := 411692699714525565537737

theorem tailTrace_1202653 : CollatzResearch.WordTrace tailWord_1202653 prefixEnd_1202653 411692699714525565537737 := by
  unfold tailWord_1202653
  simp only [CollatzResearch.WordTrace]
  refine ⟨43864358512001052625036613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29242905674667368416691075 43864358512001052625036613)
  ·
    refine ⟨8224567221000197367194365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43864358512001052625036613 8224567221000197367194365)
    ·
      refine ⟨3084212707875074012697887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8224567221000197367194365 3084212707875074012697887)
      ·
        refine ⟨4626319061812611019046831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084212707875074012697887 4626319061812611019046831)
        ·
          refine ⟨6939478592718916528570247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626319061812611019046831 6939478592718916528570247)
          ·
            refine ⟨10409217889078374792855371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939478592718916528570247 10409217889078374792855371)
            ·
              refine ⟨15613826833617562189283057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10409217889078374792855371 15613826833617562189283057)
              ·
                refine ⟨11710370125213171641962293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15613826833617562189283057 11710370125213171641962293)
                ·
                  refine ⟨1097847199238734841433965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11710370125213171641962293 1097847199238734841433965)
                  ·
                    refine ⟨411692699714525565537737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097847199238734841433965 411692699714525565537737)
                    ·
                      rfl

theorem cell22_1202653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1202653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202653 prefixEnd_1202653 := by exact prefixLift 1202653
  have htrace : WordTrace (prefixWord ++ tailWord_1202653) baseStart_1202653 baseEnd_1202653 := by
    simpa [prefixWord, tailWord_1202653, baseEnd_1202653] using wordTrace_append hprefix tailTrace_1202653
  have hstable : (prefixWord ++ tailWord_1202653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202653).length < 2 ^ (prefixWord ++ tailWord_1202653).sum := by decide
  have hdescent : baseEnd_1202653 < baseStart_1202653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202670 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1202670 : Nat := 118140960795 + 1202670 * 2 ^ 59
def prefixEnd_1202670 : Nat := 4983230072969 + 3 ^ 40 * 1202670 * 2
def baseEnd_1202670 : Nat := 411698519161943187862685

theorem tailTrace_1202670 : CollatzResearch.WordTrace tailWord_1202670 prefixEnd_1202670 411698519161943187862685 := by
  unfold tailWord_1202670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483122319117433066050683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29243319035292976352270309 5483122319117433066050683)
  ·
    refine ⟨8224683478676149599076025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483122319117433066050683 8224683478676149599076025)
    ·
      refine ⟨6168512609007112199307019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8224683478676149599076025 6168512609007112199307019)
      ·
        refine ⟨9252768913510668298960529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168512609007112199307019 9252768913510668298960529)
        ·
          refine ⟨6939576685133001224220397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252768913510668298960529 6939576685133001224220397)
          ·
            refine ⟨2602341256924875459082649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6939576685133001224220397 2602341256924875459082649)
            ·
              refine ⟨1951755942693656594311987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602341256924875459082649 1951755942693656594311987)
              ·
                refine ⟨2927633914040484891467981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951755942693656594311987 2927633914040484891467981)
                ·
                  refine ⟨1097862717765181834300493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2927633914040484891467981 1097862717765181834300493)
                  ·
                    refine ⟨411698519161943187862685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097862717765181834300493 411698519161943187862685)
                    ·
                      rfl

theorem cell22_1202670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1202670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202670 prefixEnd_1202670 := by exact prefixLift 1202670
  have htrace : WordTrace (prefixWord ++ tailWord_1202670) baseStart_1202670 baseEnd_1202670 := by
    simpa [prefixWord, tailWord_1202670, baseEnd_1202670] using wordTrace_append hprefix tailTrace_1202670
  have hstable : (prefixWord ++ tailWord_1202670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202670).length < 2 ^ (prefixWord ++ tailWord_1202670).sum := by decide
  have hdescent : baseEnd_1202670 < baseStart_1202670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202681 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_1202681 : Nat := 118140960795 + 1202681 * 2 ^ 59
def prefixEnd_1202681 : Nat := 4983230072969 + 3 ^ 40 * 1202681 * 2
def baseEnd_1202681 : Nat := 411702284686742825837651

theorem tailTrace_1202681 : CollatzResearch.WordTrace tailWord_1202681 prefixEnd_1202681 411702284686742825837651 := by
  unfold tailWord_1202681
  simp only [CollatzResearch.WordTrace]
  refine ⟨43865379755899613407055897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29243586503933075604703931 43865379755899613407055897)
  ·
    refine ⟨32899034816924710055291923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43865379755899613407055897 32899034816924710055291923)
    ·
      refine ⟨49348552225387065082937885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32899034816924710055291923 49348552225387065082937885)
      ·
        refine ⟨18505707084520149406101707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49348552225387065082937885 18505707084520149406101707)
        ·
          refine ⟨27758560626780224109152561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18505707084520149406101707 27758560626780224109152561)
          ·
            refine ⟨20818920470085168081864421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27758560626780224109152561 20818920470085168081864421)
            ·
              refine ⟨3903547588140969015349579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20818920470085168081864421 3903547588140969015349579)
              ·
                refine ⟨5855321382211453523024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903547588140969015349579 5855321382211453523024369)
                ·
                  refine ⟨4391491036658590142268277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855321382211453523024369 4391491036658590142268277)
                  ·
                    refine ⟨411702284686742825837651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4391491036658590142268277 411702284686742825837651)
                    ·
                      rfl

theorem cell22_1202681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_1202681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202681 prefixEnd_1202681 := by exact prefixLift 1202681
  have htrace : WordTrace (prefixWord ++ tailWord_1202681) baseStart_1202681 baseEnd_1202681 := by
    simpa [prefixWord, tailWord_1202681, baseEnd_1202681] using wordTrace_append hprefix tailTrace_1202681
  have hstable : (prefixWord ++ tailWord_1202681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202681).length < 2 ^ (prefixWord ++ tailWord_1202681).sum := by decide
  have hdescent : baseEnd_1202681 < baseStart_1202681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202734 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1202734 : Nat := 118140960795 + 1202734 * 2 ^ 59
def prefixEnd_1202734 : Nat := 4983230072969 + 3 ^ 40 * 1202734 * 2
def baseEnd_1202734 : Nat := 137240142556622784754163

theorem tailTrace_1202734 : CollatzResearch.WordTrace tailWord_1202734 prefixEnd_1202734 137240142556622784754163 := by
  unfold tailWord_1202734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483414103088450432341907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29244875216471735639156837 5483414103088450432341907)
  ·
    refine ⟨8225121154632675648512861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483414103088450432341907 8225121154632675648512861)
    ·
      refine ⟨3084420432987253368192323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8225121154632675648512861 3084420432987253368192323)
      ·
        refine ⟨4626630649480880052288485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084420432987253368192323 4626630649480880052288485)
        ·
          refine ⟨867493246777665009804091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4626630649480880052288485 867493246777665009804091)
          ·
            refine ⟨1301239870166497514706137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867493246777665009804091 1301239870166497514706137)
            ·
              refine ⟨975929902624873136029603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301239870166497514706137 975929902624873136029603)
              ·
                refine ⟨1463894853937309704044405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975929902624873136029603 1463894853937309704044405)
                ·
                  refine ⟨137240142556622784754163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1463894853937309704044405 137240142556622784754163)
                  ·
                    rfl

theorem cell22_1202734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1202734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202734 prefixEnd_1202734 := by exact prefixLift 1202734
  have htrace : WordTrace (prefixWord ++ tailWord_1202734) baseStart_1202734 baseEnd_1202734 := by
    simpa [prefixWord, tailWord_1202734, baseEnd_1202734] using wordTrace_append hprefix tailTrace_1202734
  have hstable : (prefixWord ++ tailWord_1202734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202734).length < 2 ^ (prefixWord ++ tailWord_1202734).sum := by decide
  have hdescent : baseEnd_1202734 < baseStart_1202734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202801 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 11]
def baseStart_1202801 : Nat := 118140960795 + 1202801 * 2 ^ 59
def prefixEnd_1202801 : Nat := 4983230072969 + 3 ^ 40 * 1202801 * 2
def baseEnd_1202801 : Nat := 137247787713034170945761

theorem tailTrace_1202801 : CollatzResearch.WordTrace tailWord_1202801 prefixEnd_1202801 137247787713034170945761 := by
  unfold tailWord_1202801
  simp only [CollatzResearch.WordTrace]
  refine ⟨43869756515464873901424257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29246504343643249267616171 43869756515464873901424257)
  ·
    refine ⟨32902317386598655426068193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43869756515464873901424257 32902317386598655426068193)
    ·
      refine ⟨24676738039948991569551145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32902317386598655426068193 24676738039948991569551145)
      ·
        refine ⟨18507553529961743677163359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24676738039948991569551145 18507553529961743677163359)
        ·
          refine ⟨27761330294942615515745039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18507553529961743677163359 27761330294942615515745039)
          ·
            refine ⟨41641995442413923273617559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27761330294942615515745039 41641995442413923273617559)
            ·
              refine ⟨62462993163620884910426339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41641995442413923273617559 62462993163620884910426339)
              ·
                refine ⟨93694489745431327365639509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62462993163620884910426339 93694489745431327365639509)
                ·
                  refine ⟨137247787713034170945761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 93694489745431327365639509 137247787713034170945761)
                  ·
                    rfl

theorem cell22_1202801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_1202801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202801 prefixEnd_1202801 := by exact prefixLift 1202801
  have htrace : WordTrace (prefixWord ++ tailWord_1202801) baseStart_1202801 baseEnd_1202801 := by
    simpa [prefixWord, tailWord_1202801, baseEnd_1202801] using wordTrace_append hprefix tailTrace_1202801
  have hstable : (prefixWord ++ tailWord_1202801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202801).length < 2 ^ (prefixWord ++ tailWord_1202801).sum := by decide
  have hdescent : baseEnd_1202801 < baseStart_1202801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202863 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 6]
def baseStart_1202863 : Nat := 118140960795 + 1202863 * 2 ^ 59
def prefixEnd_1202863 : Nat := 4983230072969 + 3 ^ 40 * 1202863 * 2
def baseEnd_1202863 : Nat := 137254862335385005929031

theorem tailTrace_1202863 : CollatzResearch.WordTrace tailWord_1202863 prefixEnd_1202863 137254862335385005929031 := by
  unfold tailWord_1202863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43872017841240258490181243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29248011894160172326787495 43872017841240258490181243)
  ·
    refine ⟨65808026761860387735271865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43872017841240258490181243 65808026761860387735271865)
    ·
      refine ⟨49356020071395290801453899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65808026761860387735271865 49356020071395290801453899)
      ·
        refine ⟨74034030107092936202180849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49356020071395290801453899 74034030107092936202180849)
        ·
          refine ⟨55525522580319702151635637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74034030107092936202180849 55525522580319702151635637)
          ·
            refine ⟨5205517741904972076715841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55525522580319702151635637 5205517741904972076715841)
            ·
              refine ⟨3904138306428729057536881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5205517741904972076715841 3904138306428729057536881)
              ·
                refine ⟨2928103729821546793152661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904138306428729057536881 2928103729821546793152661)
                ·
                  refine ⟨137254862335385005929031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2928103729821546793152661 137254862335385005929031)
                  ·
                    rfl

theorem cell22_1202863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_1202863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202863 prefixEnd_1202863 := by exact prefixLift 1202863
  have htrace : WordTrace (prefixWord ++ tailWord_1202863) baseStart_1202863 baseEnd_1202863 := by
    simpa [prefixWord, tailWord_1202863, baseEnd_1202863] using wordTrace_append hprefix tailTrace_1202863
  have hstable : (prefixWord ++ tailWord_1202863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202863).length < 2 ^ (prefixWord ++ tailWord_1202863).sum := by decide
  have hdescent : baseEnd_1202863 < baseStart_1202863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202897 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 4]
def baseStart_1202897 : Nat := 118140960795 + 1202897 * 2 ^ 59
def prefixEnd_1202897 : Nat := 4983230072969 + 3 ^ 40 * 1202897 * 2
def baseEnd_1202897 : Nat := 137258741966996754145663

theorem tailTrace_1202897 : CollatzResearch.WordTrace tailWord_1202897 prefixEnd_1202897 137258741966996754145663 := by
  unfold tailWord_1202897
  simp only [CollatzResearch.WordTrace]
  refine ⟨43873257923117082296918945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29248838615411388197945963 43873257923117082296918945)
  ·
    refine ⟨32904943442337811722689209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43873257923117082296918945 32904943442337811722689209)
    ·
      refine ⟨24678707581753358792016907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32904943442337811722689209 24678707581753358792016907)
      ·
        refine ⟨37018061372630038188025361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24678707581753358792016907 37018061372630038188025361)
        ·
          refine ⟨27763546029472528641019021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37018061372630038188025361 27763546029472528641019021)
          ·
            refine ⟨10411329761052198240382133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27763546029472528641019021 10411329761052198240382133)
            ·
              refine ⟨976062165098643585035825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10411329761052198240382133 976062165098643585035825)
              ·
                refine ⟨732046623823982688776869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976062165098643585035825 732046623823982688776869)
                ·
                  refine ⟨137258741966996754145663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732046623823982688776869 137258741966996754145663)
                  ·
                    rfl

theorem cell22_1202897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_1202897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202897 prefixEnd_1202897 := by exact prefixLift 1202897
  have htrace : WordTrace (prefixWord ++ tailWord_1202897) baseStart_1202897 baseEnd_1202897 := by
    simpa [prefixWord, tailWord_1202897, baseEnd_1202897] using wordTrace_append hprefix tailTrace_1202897
  have hstable : (prefixWord ++ tailWord_1202897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202897).length < 2 ^ (prefixWord ++ tailWord_1202897).sum := by decide
  have hdescent : baseEnd_1202897 < baseStart_1202897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202933 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1202933 : Nat := 118140960795 + 1202933 * 2 ^ 59
def prefixEnd_1202933 : Nat := 4983230072969 + 3 ^ 40 * 1202933 * 2
def baseEnd_1202933 : Nat := 411788549436698168536879

theorem tailTrace_1202933 : CollatzResearch.WordTrace tailWord_1202933 prefixEnd_1202933 411788549436698168536879 := by
  unfold tailWord_1202933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43874570950986660445229453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29249713967324440296819635 43874570950986660445229453)
  ·
    refine ⟨16452964106619997666961045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43874570950986660445229453 16452964106619997666961045)
    ·
      refine ⟨771232692497812390638799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16452964106619997666961045 771232692497812390638799)
      ·
        refine ⟨1156849038746718585958199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771232692497812390638799 1156849038746718585958199)
        ·
          refine ⟨1735273558120077878937299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156849038746718585958199 1735273558120077878937299)
          ·
            refine ⟨2602910337180116818405949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735273558120077878937299 2602910337180116818405949)
            ·
              refine ⟨976091376442543806902231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2602910337180116818405949 976091376442543806902231)
              ·
                refine ⟨1464137064663815710353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976091376442543806902231 1464137064663815710353347)
                ·
                  refine ⟨2196205596995723565530021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464137064663815710353347 2196205596995723565530021)
                  ·
                    refine ⟨411788549436698168536879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2196205596995723565530021 411788549436698168536879)
                    ·
                      rfl

theorem cell22_1202933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1202933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202933 prefixEnd_1202933 := by exact prefixLift 1202933
  have htrace : WordTrace (prefixWord ++ tailWord_1202933) baseStart_1202933 baseEnd_1202933 := by
    simpa [prefixWord, tailWord_1202933, baseEnd_1202933] using wordTrace_append hprefix tailTrace_1202933
  have hstable : (prefixWord ++ tailWord_1202933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202933).length < 2 ^ (prefixWord ++ tailWord_1202933).sum := by decide
  have hdescent : baseEnd_1202933 < baseStart_1202933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202953 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 7]
def baseStart_1202953 : Nat := 118140960795 + 1202953 * 2 ^ 59
def prefixEnd_1202953 : Nat := 4983230072969 + 3 ^ 40 * 1202953 * 2
def baseEnd_1202953 : Nat := 137265131948474927678939

theorem tailTrace_1202953 : CollatzResearch.WordTrace tailWord_1202953 prefixEnd_1202953 137265131948474927678939 := by
  unfold tailWord_1202953
  simp only [CollatzResearch.WordTrace]
  refine ⟨43875300410914203860957513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29250200273942802573971675 43875300410914203860957513)
  ·
    refine ⟨32906475308185652895718135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43875300410914203860957513 32906475308185652895718135)
    ·
      refine ⟨49359712962278479343577203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32906475308185652895718135 49359712962278479343577203)
      ·
        refine ⟨74039569443417719015365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49359712962278479343577203 74039569443417719015365805)
        ·
          refine ⟨27764838541281644630762177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74039569443417719015365805 27764838541281644630762177)
          ·
            refine ⟨20823628905961233473071633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27764838541281644630762177 20823628905961233473071633)
            ·
              refine ⟨15617721679470925104803725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20823628905961233473071633 15617721679470925104803725)
              ·
                refine ⟨5856645629801596914301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15617721679470925104803725 5856645629801596914301397)
                ·
                  refine ⟨137265131948474927678939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5856645629801596914301397 137265131948474927678939)
                  ·
                    rfl

theorem cell22_1202953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_1202953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202953 prefixEnd_1202953 := by exact prefixLift 1202953
  have htrace : WordTrace (prefixWord ++ tailWord_1202953) baseStart_1202953 baseEnd_1202953 := by
    simpa [prefixWord, tailWord_1202953, baseEnd_1202953] using wordTrace_append hprefix tailTrace_1202953
  have hstable : (prefixWord ++ tailWord_1202953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202953).length < 2 ^ (prefixWord ++ tailWord_1202953).sum := by decide
  have hdescent : baseEnd_1202953 < baseStart_1202953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202970 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_1202970 : Nat := 118140960795 + 1202970 * 2 ^ 59
def prefixEnd_1202970 : Nat := 4983230072969 + 3 ^ 40 * 1202970 * 2
def baseEnd_1202970 : Nat := 137267071764280801787255

theorem tailTrace_1202970 : CollatzResearch.WordTrace tailWord_1202970 prefixEnd_1202970 137267071764280801787255 := by
  unfold tailWord_1202970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968980112963153941081591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29250613634568410509550909 10968980112963153941081591)
  ·
    refine ⟨16453470169444730911622387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968980112963153941081591 16453470169444730911622387)
    ·
      refine ⟨24680205254167096367433581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16453470169444730911622387 24680205254167096367433581)
      ·
        refine ⟨9255076970312661137787593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24680205254167096367433581 9255076970312661137787593)
        ·
          refine ⟨6941307727734495853340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9255076970312661137787593 6941307727734495853340695)
          ·
            refine ⟨10411961591601743780011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6941307727734495853340695 10411961591601743780011043)
            ·
              refine ⟨15617942387402615670016565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10411961591601743780011043 15617942387402615670016565)
              ·
                refine ⟨1464182098818995219064053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15617942387402615670016565 1464182098818995219064053)
                ·
                  refine ⟨137267071764280801787255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464182098818995219064053 137267071764280801787255)
                  ·
                    rfl

theorem cell22_1202970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_1202970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1202970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1202970 prefixEnd_1202970 := by exact prefixLift 1202970
  have htrace : WordTrace (prefixWord ++ tailWord_1202970) baseStart_1202970 baseEnd_1202970 := by
    simpa [prefixWord, tailWord_1202970, baseEnd_1202970] using wordTrace_append hprefix tailTrace_1202970
  have hstable : (prefixWord ++ tailWord_1202970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202970).length < 2 ^ (prefixWord ++ tailWord_1202970).sum := by decide
  have hdescent : baseEnd_1202970 < baseStart_1202970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203021 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1203021 : Nat := 118140960795 + 1203021 * 2 ^ 59
def prefixEnd_1203021 : Nat := 4983230072969 + 3 ^ 40 * 1203021 * 2
def baseEnd_1203021 : Nat := 137272891211698424112203

theorem tailTrace_1203021 : CollatzResearch.WordTrace tailWord_1203021 prefixEnd_1203021 137272891211698424112203 := by
  unfold tailWord_1203021
  simp only [CollatzResearch.WordTrace]
  refine ⟨43877780574667851474432917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29251853716445234316288611 43877780574667851474432917)
  ·
    refine ⟨2056770964437555537864043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43877780574667851474432917 2056770964437555537864043)
    ·
      refine ⟨3085156446656333306796065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056770964437555537864043 3085156446656333306796065)
      ·
        refine ⟨2313867334992249980097049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085156446656333306796065 2313867334992249980097049)
        ·
          refine ⟨1735400501244187485072787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2313867334992249980097049 1735400501244187485072787)
          ·
            refine ⟨2603100751866281227609181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735400501244187485072787 2603100751866281227609181)
            ·
              refine ⟨976162781949855460353443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2603100751866281227609181 976162781949855460353443)
              ·
                refine ⟨1464244172924783190530165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976162781949855460353443 1464244172924783190530165)
                ·
                  refine ⟨137272891211698424112203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464244172924783190530165 137272891211698424112203)
                  ·
                    rfl

theorem cell22_1203021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1203021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203021 prefixEnd_1203021 := by exact prefixLift 1203021
  have htrace : WordTrace (prefixWord ++ tailWord_1203021) baseStart_1203021 baseEnd_1203021 := by
    simpa [prefixWord, tailWord_1203021, baseEnd_1203021] using wordTrace_append hprefix tailTrace_1203021
  have hstable : (prefixWord ++ tailWord_1203021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203021).length < 2 ^ (prefixWord ++ tailWord_1203021).sum := by decide
  have hdescent : baseEnd_1203021 < baseStart_1203021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203045 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1203045 : Nat := 118140960795 + 1203045 * 2 ^ 59
def prefixEnd_1203045 : Nat := 4983230072969 + 3 ^ 40 * 1203045 * 2
def baseEnd_1203045 : Nat := 411826889325567209736535

theorem tailTrace_1203045 : CollatzResearch.WordTrace tailWord_1203045 prefixEnd_1203045 411826889325567209736535 := by
  unfold tailWord_1203045
  simp only [CollatzResearch.WordTrace]
  refine ⟨43878655926580903573306589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29252437284387269048871059 43878655926580903573306589)
  ·
    refine ⟨16454495972467838839989971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43878655926580903573306589 16454495972467838839989971)
    ·
      refine ⟨24681743958701758259984957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16454495972467838839989971 24681743958701758259984957)
      ·
        refine ⟨9255653984513159347494359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24681743958701758259984957 9255653984513159347494359)
        ·
          refine ⟨13883480976769739021241539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255653984513159347494359 13883480976769739021241539)
          ·
            refine ⟨20825221465154608531862309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13883480976769739021241539 20825221465154608531862309)
            ·
              refine ⟨3904729024716489099724183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20825221465154608531862309 3904729024716489099724183)
              ·
                refine ⟨5857093537074733649586275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904729024716489099724183 5857093537074733649586275)
                ·
                  refine ⟨8785640305612100474379413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857093537074733649586275 8785640305612100474379413)
                  ·
                    refine ⟨411826889325567209736535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8785640305612100474379413 411826889325567209736535)
                    ·
                      rfl

theorem cell22_1203045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1203045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203045 prefixEnd_1203045 := by exact prefixLift 1203045
  have htrace : WordTrace (prefixWord ++ tailWord_1203045) baseStart_1203045 baseEnd_1203045 := by
    simpa [prefixWord, tailWord_1203045, baseEnd_1203045] using wordTrace_append hprefix tailTrace_1203045
  have hstable : (prefixWord ++ tailWord_1203045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203045).length < 2 ^ (prefixWord ++ tailWord_1203045).sum := by decide
  have hdescent : baseEnd_1203045 < baseStart_1203045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203047 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1203047 : Nat := 118140960795 + 1203047 * 2 ^ 59
def prefixEnd_1203047 : Nat := 4983230072969 + 3 ^ 40 * 1203047 * 2
def baseEnd_1203047 : Nat := 411827573966439871186529

theorem tailTrace_1203047 : CollatzResearch.WordTrace tailWord_1203047 prefixEnd_1203047 411827573966439871186529 := by
  unfold tailWord_1203047
  simp only [CollatzResearch.WordTrace]
  refine ⟨43878728872573657914879395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29252485915049105276586263 43878728872573657914879395)
  ·
    refine ⟨65818093308860486872319093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43878728872573657914879395 65818093308860486872319093)
    ·
      refine ⟨6170446247705670644279915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65818093308860486872319093 6170446247705670644279915)
      ·
        refine ⟨9255669371558505966419873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170446247705670644279915 9255669371558505966419873)
        ·
          refine ⟨6941752028668879474814905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9255669371558505966419873 6941752028668879474814905)
          ·
            refine ⟨5206314021501659606111179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6941752028668879474814905 5206314021501659606111179)
            ·
              refine ⟨7809471032252489409166769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206314021501659606111179 7809471032252489409166769)
              ·
                refine ⟨5857103274189367056875077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7809471032252489409166769 5857103274189367056875077)
                ·
                  refine ⟨1098206863910506323164077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5857103274189367056875077 1098206863910506323164077)
                  ·
                    refine ⟨411827573966439871186529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098206863910506323164077 411827573966439871186529)
                    ·
                      rfl

theorem cell22_1203047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1203047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203047 prefixEnd_1203047 := by exact prefixLift 1203047
  have htrace : WordTrace (prefixWord ++ tailWord_1203047) baseStart_1203047 baseEnd_1203047 := by
    simpa [prefixWord, tailWord_1203047, baseEnd_1203047] using wordTrace_append hprefix tailTrace_1203047
  have hstable : (prefixWord ++ tailWord_1203047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203047).length < 2 ^ (prefixWord ++ tailWord_1203047).sum := by decide
  have hdescent : baseEnd_1203047 < baseStart_1203047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203081 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_1203081 : Nat := 118140960795 + 1203081 * 2 ^ 59
def prefixEnd_1203081 : Nat := 4983230072969 + 3 ^ 40 * 1203081 * 2
def baseEnd_1203081 : Nat := 411839212861275115836425

theorem tailTrace_1203081 : CollatzResearch.WordTrace tailWord_1203081 prefixEnd_1203081 411839212861275115836425 := by
  unfold tailWord_1203081
  simp only [CollatzResearch.WordTrace]
  refine ⟨43879968954450481721617097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29253312636300321147744731 43879968954450481721617097)
  ·
    refine ⟨32909976715837861291212823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43879968954450481721617097 32909976715837861291212823)
    ·
      refine ⟨49364965073756791936819235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32909976715837861291212823 49364965073756791936819235)
      ·
        refine ⟨74047447610635187905228853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49364965073756791936819235 74047447610635187905228853)
        ·
          refine ⟨6941948213497048866115205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74047447610635187905228853 6941948213497048866115205)
          ·
            refine ⟨1301615290030696662396601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6941948213497048866115205 1301615290030696662396601)
            ·
              refine ⟨976211467523022496797451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301615290030696662396601 976211467523022496797451)
              ·
                refine ⟨1464317201284533745196177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976211467523022496797451 1464317201284533745196177)
                ·
                  refine ⟨1098237900963400308897133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1464317201284533745196177 1098237900963400308897133)
                  ·
                    refine ⟨411839212861275115836425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098237900963400308897133 411839212861275115836425)
                    ·
                      rfl

theorem cell22_1203081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_1203081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203081 prefixEnd_1203081 := by exact prefixLift 1203081
  have htrace : WordTrace (prefixWord ++ tailWord_1203081) baseStart_1203081 baseEnd_1203081 := by
    simpa [prefixWord, tailWord_1203081, baseEnd_1203081] using wordTrace_append hprefix tailTrace_1203081
  have hstable : (prefixWord ++ tailWord_1203081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203081).length < 2 ^ (prefixWord ++ tailWord_1203081).sum := by decide
  have hdescent : baseEnd_1203081 < baseStart_1203081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203124 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1203124 : Nat := 118140960795 + 1203124 * 2 ^ 59
def prefixEnd_1203124 : Nat := 4983230072969 + 3 ^ 40 * 1203124 * 2
def baseEnd_1203124 : Nat := 411853932640037337011293

theorem tailTrace_1203124 : CollatzResearch.WordTrace tailWord_1203124 prefixEnd_1203124 411853932640037337011293 := by
  unfold tailWord_1203124
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940768646647350032716213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29254358195529800043621617 21940768646647350032716213)
  ·
    refine ⟨2056947060623189065567145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21940768646647350032716213 2056947060623189065567145)
    ·
      refine ⟨1542710295467391799175359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056947060623189065567145 1542710295467391799175359)
      ·
        refine ⟨2314065443201087698763039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542710295467391799175359 2314065443201087698763039)
        ·
          refine ⟨3471098164801631548144559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314065443201087698763039 3471098164801631548144559)
          ·
            refine ⟨5206647247202447322216839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471098164801631548144559 5206647247202447322216839)
            ·
              refine ⟨7809970870803670983325259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206647247202447322216839 7809970870803670983325259)
              ·
                refine ⟨11714956306205506474987889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809970870803670983325259 11714956306205506474987889)
                ·
                  refine ⟨8786217229654129856240917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11714956306205506474987889 8786217229654129856240917)
                  ·
                    refine ⟨411853932640037337011293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8786217229654129856240917 411853932640037337011293)
                    ·
                      rfl

theorem cell22_1203124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1203124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203124 prefixEnd_1203124 := by exact prefixLift 1203124
  have htrace : WordTrace (prefixWord ++ tailWord_1203124) baseStart_1203124 baseEnd_1203124 := by
    simpa [prefixWord, tailWord_1203124, baseEnd_1203124] using wordTrace_append hprefix tailTrace_1203124
  have hstable : (prefixWord ++ tailWord_1203124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203124).length < 2 ^ (prefixWord ++ tailWord_1203124).sum := by decide
  have hdescent : baseEnd_1203124 < baseStart_1203124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203152 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_1203152 : Nat := 118140960795 + 1203152 * 2 ^ 59
def prefixEnd_1203152 : Nat := 4983230072969 + 3 ^ 40 * 1203152 * 2
def baseEnd_1203152 : Nat := 411863517612254597311207

theorem tailTrace_1203152 : CollatzResearch.WordTrace tailWord_1203152 prefixEnd_1203152 411863517612254597311207 := by
  unfold tailWord_1203152
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941279268596630423725855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29255039024795507231634473 21941279268596630423725855)
  ·
    refine ⟨32911918902894945635588783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21941279268596630423725855 32911918902894945635588783)
    ·
      refine ⟨49367878354342418453383175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32911918902894945635588783 49367878354342418453383175)
      ·
        refine ⟨74051817531513627680074763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49367878354342418453383175 74051817531513627680074763)
        ·
          refine ⟨111077726297270441520112145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74051817531513627680074763 111077726297270441520112145)
          ·
            refine ⟨83308294722952831140084109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111077726297270441520112145 83308294722952831140084109)
            ·
              refine ⟨31240610521107311677531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83308294722952831140084109 31240610521107311677531541)
              ·
                refine ⟨1464403618176905234884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31240610521107311677531541 1464403618176905234884291)
                ·
                  refine ⟨2196605427265357852326437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464403618176905234884291 2196605427265357852326437)
                  ·
                    refine ⟨411863517612254597311207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2196605427265357852326437 411863517612254597311207)
                    ·
                      rfl

theorem cell22_1203152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_1203152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203152 prefixEnd_1203152 := by exact prefixLift 1203152
  have htrace : WordTrace (prefixWord ++ tailWord_1203152) baseStart_1203152 baseEnd_1203152 := by
    simpa [prefixWord, tailWord_1203152, baseEnd_1203152] using wordTrace_append hprefix tailTrace_1203152
  have hstable : (prefixWord ++ tailWord_1203152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203152).length < 2 ^ (prefixWord ++ tailWord_1203152).sum := by decide
  have hdescent : baseEnd_1203152 < baseStart_1203152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203173 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 5]
def baseStart_1203173 : Nat := 118140960795 + 1203173 * 2 ^ 59
def prefixEnd_1203173 : Nat := 4983230072969 + 3 ^ 40 * 1203173 * 2
def baseEnd_1203173 : Nat := 137290235447139180845381

theorem tailTrace_1203173 : CollatzResearch.WordTrace tailWord_1203173 prefixEnd_1203173 137290235447139180845381 := by
  unfold tailWord_1203173
  simp only [CollatzResearch.WordTrace]
  refine ⟨43883324470117181433966173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29255549646744787622644115 43883324470117181433966173)
  ·
    refine ⟨16456246676293943037737315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43883324470117181433966173 16456246676293943037737315)
    ·
      refine ⟨24684370014440914556605973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16456246676293943037737315 24684370014440914556605973)
      ·
        refine ⟨1157079844426917869840905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24684370014440914556605973 1157079844426917869840905)
        ·
          refine ⟨867809883320188402380679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1157079844426917869840905 867809883320188402380679)
          ·
            refine ⟨1301714824980282603571019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867809883320188402380679 1301714824980282603571019)
            ·
              refine ⟨1952572237470423905356529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301714824980282603571019 1952572237470423905356529)
              ·
                refine ⟨1464429178102817929017397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952572237470423905356529 1464429178102817929017397)
                ·
                  refine ⟨137290235447139180845381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464429178102817929017397 137290235447139180845381)
                  ·
                    rfl

theorem cell22_1203173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_1203173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203173 prefixEnd_1203173 := by exact prefixLift 1203173
  have htrace : WordTrace (prefixWord ++ tailWord_1203173) baseStart_1203173 baseEnd_1203173 := by
    simpa [prefixWord, tailWord_1203173, baseEnd_1203173] using wordTrace_append hprefix tailTrace_1203173
  have hstable : (prefixWord ++ tailWord_1203173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203173).length < 2 ^ (prefixWord ++ tailWord_1203173).sum := by decide
  have hdescent : baseEnd_1203173 < baseStart_1203173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203195 : List Nat := [1, 1, 1, 1, 1, 3, 3, 11]
def baseStart_1203195 : Nat := 118140960795 + 1203195 * 2 ^ 59
def prefixEnd_1203195 : Nat := 4983230072969 + 3 ^ 40 * 1203195 * 2
def baseEnd_1203195 : Nat := 45764248599001868720675

theorem tailTrace_1203195 : CollatzResearch.WordTrace tailWord_1203195 prefixEnd_1203195 45764248599001868720675 := by
  unfold tailWord_1203195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43884126876037479191267039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29256084584024986127511359 43884126876037479191267039)
  ·
    refine ⟨65826190314056218786900559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43884126876037479191267039 65826190314056218786900559)
    ·
      refine ⟨98739285471084328180350839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65826190314056218786900559 98739285471084328180350839)
      ·
        refine ⟨148108928206626492270526259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98739285471084328180350839 148108928206626492270526259)
        ·
          refine ⟨222163392309939738405789389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148108928206626492270526259 222163392309939738405789389)
          ·
            refine ⟨83311272116227401902171021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222163392309939738405789389 83311272116227401902171021)
            ·
              refine ⟨31241727043585275713314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83311272116227401902171021 31241727043585275713314133)
              ·
                refine ⟨45764248599001868720675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31241727043585275713314133 45764248599001868720675)
                ·
                  rfl

theorem cell22_1203195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_1203195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203195 prefixEnd_1203195 := by exact prefixLift 1203195
  have htrace : WordTrace (prefixWord ++ tailWord_1203195) baseStart_1203195 baseEnd_1203195 := by
    simpa [prefixWord, tailWord_1203195, baseEnd_1203195] using wordTrace_append hprefix tailTrace_1203195
  have hstable : (prefixWord ++ tailWord_1203195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203195).length < 2 ^ (prefixWord ++ tailWord_1203195).sum := by decide
  have hdescent : baseEnd_1203195 < baseStart_1203195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203212 : List Nat := [2, 2, 1, 2, 3, 3, 1, 8]
def baseStart_1203212 : Nat := 118140960795 + 1203212 * 2 ^ 59
def prefixEnd_1203212 : Nat := 4983230072969 + 3 ^ 40 * 1203212 * 2
def baseEnd_1203212 : Nat := 45764895204270493423447

theorem tailTrace_1203212 : CollatzResearch.WordTrace tailWord_1203212 prefixEnd_1203212 45764895204270493423447 := by
  unfold tailWord_1203212
  simp only [CollatzResearch.WordTrace]
  refine ⟨21942373458487945547317945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29256497944650594063090593 21942373458487945547317945)
  ·
    refine ⟨16456780093865959160488459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21942373458487945547317945 16456780093865959160488459)
    ·
      refine ⟨24685170140798938740732689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16456780093865959160488459 24685170140798938740732689)
      ·
        refine ⟨18513877605599204055549517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24685170140798938740732689 18513877605599204055549517)
        ·
          refine ⟨6942704102099701520831069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18513877605599204055549517 6942704102099701520831069)
          ·
            refine ⟨2603514038287388070311651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6942704102099701520831069 2603514038287388070311651)
            ·
              refine ⟨3905271057431082105467477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603514038287388070311651 3905271057431082105467477)
              ·
                refine ⟨45764895204270493423447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3905271057431082105467477 45764895204270493423447)
                ·
                  rfl

theorem cell22_1203212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_1203212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203212 prefixEnd_1203212 := by exact prefixLift 1203212
  have htrace : WordTrace (prefixWord ++ tailWord_1203212) baseStart_1203212 baseEnd_1203212 := by
    simpa [prefixWord, tailWord_1203212, baseEnd_1203212] using wordTrace_append hprefix tailTrace_1203212
  have hstable : (prefixWord ++ tailWord_1203212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203212).length < 2 ^ (prefixWord ++ tailWord_1203212).sum := by decide
  have hdescent : baseEnd_1203212 < baseStart_1203212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203229 : List Nat := [1, 4, 2, 2, 3, 2, 8]
def baseStart_1203229 : Nat := 118140960795 + 1203229 * 2 ^ 59
def prefixEnd_1203229 : Nat := 4983230072969 + 3 ^ 40 * 1203229 * 2
def baseEnd_1203229 : Nat := 15255180603179706042073

theorem tailTrace_1203229 : CollatzResearch.WordTrace tailWord_1203229 prefixEnd_1203229 15255180603179706042073 := by
  unfold tailWord_1203229
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885366957914302998004741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29256911305276201998669827 43885366957914302998004741)
  ·
    refine ⟨8228506304608931812125889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43885366957914302998004741 8228506304608931812125889)
    ·
      refine ⟨6171379728456698859094417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8228506304608931812125889 6171379728456698859094417)
      ·
        refine ⟨4628534796342524144320813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6171379728456698859094417 4628534796342524144320813)
        ·
          refine ⟨1735700548628446554120305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4628534796342524144320813 1735700548628446554120305)
          ·
            refine ⟨1301775411471334915590229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735700548628446554120305 1301775411471334915590229)
            ·
              refine ⟨15255180603179706042073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1301775411471334915590229 15255180603179706042073)
              ·
                rfl

theorem cell22_1203229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 8].length) (baseStart_1203229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203229 prefixEnd_1203229 := by exact prefixLift 1203229
  have htrace : WordTrace (prefixWord ++ tailWord_1203229) baseStart_1203229 baseEnd_1203229 := by
    simpa [prefixWord, tailWord_1203229, baseEnd_1203229] using wordTrace_append hprefix tailTrace_1203229
  have hstable : (prefixWord ++ tailWord_1203229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203229).length < 2 ^ (prefixWord ++ tailWord_1203229).sum := by decide
  have hdescent : baseEnd_1203229 < baseStart_1203229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203351 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 4, 3]
def baseStart_1203351 : Nat := 118140960795 + 1203351 * 2 ^ 59
def prefixEnd_1203351 : Nat := 4983230072969 + 3 ^ 40 * 1203351 * 2
def baseEnd_1203351 : Nat := 411931639379084411585597

theorem tailTrace_1203351 : CollatzResearch.WordTrace tailWord_1203351 prefixEnd_1203351 411931639379084411585597 := by
  unfold tailWord_1203351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43889816663472317833945907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29259877775648211889297271 43889816663472317833945907)
  ·
    refine ⟨65834724995208476750918861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43889816663472317833945907 65834724995208476750918861)
    ·
      refine ⟨24688021873203178781594573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65834724995208476750918861 24688021873203178781594573)
      ·
        refine ⟨9258008202451192043097965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24688021873203178781594573 9258008202451192043097965)
        ·
          refine ⟨3471753075919197016161737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9258008202451192043097965 3471753075919197016161737)
          ·
            refine ⟨2603814806939397762121303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471753075919197016161737 2603814806939397762121303)
            ·
              refine ⟨3905722210409096643181955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2603814806939397762121303 3905722210409096643181955)
              ·
                refine ⟨5858583315613644964772933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905722210409096643181955 5858583315613644964772933)
                ·
                  refine ⟨1098484371677558430894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5858583315613644964772933 1098484371677558430894925)
                  ·
                    refine ⟨411931639379084411585597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098484371677558430894925 411931639379084411585597)
                    ·
                      rfl

theorem cell22_1203351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_1203351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203351 prefixEnd_1203351 := by exact prefixLift 1203351
  have htrace : WordTrace (prefixWord ++ tailWord_1203351) baseStart_1203351 baseEnd_1203351 := by
    simpa [prefixWord, tailWord_1203351, baseEnd_1203351] using wordTrace_append hprefix tailTrace_1203351
  have hstable : (prefixWord ++ tailWord_1203351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203351).length < 2 ^ (prefixWord ++ tailWord_1203351).sum := by decide
  have hdescent : baseEnd_1203351 < baseStart_1203351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203409 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 5]
def baseStart_1203409 : Nat := 118140960795 + 1203409 * 2 ^ 59
def prefixEnd_1203409 : Nat := 4983230072969 + 3 ^ 40 * 1203409 * 2
def baseEnd_1203409 : Nat := 137317164654797197878473

theorem tailTrace_1203409 : CollatzResearch.WordTrace tailWord_1203409 prefixEnd_1203409 137317164654797197878473 := by
  unfold tailWord_1203409
  simp only [CollatzResearch.WordTrace]
  refine ⟨43891932097262193739557281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29261288064841462493038187 43891932097262193739557281)
  ·
    refine ⟨32918949072946645304667961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43891932097262193739557281 32918949072946645304667961)
    ·
      refine ⟨24689211804709983978500971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32918949072946645304667961 24689211804709983978500971)
      ·
        refine ⟨37033817707064975967751457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24689211804709983978500971 37033817707064975967751457)
        ·
          refine ⟨27775363280298731975813593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37033817707064975967751457 27775363280298731975813593)
          ·
            refine ⟨20831522460224048981860195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27775363280298731975813593 20831522460224048981860195)
            ·
              refine ⟨31247283690336073472790293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20831522460224048981860195 31247283690336073472790293)
              ·
                refine ⟨1464716422984503444037045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31247283690336073472790293 1464716422984503444037045)
                ·
                  refine ⟨137317164654797197878473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464716422984503444037045 137317164654797197878473)
                  ·
                    rfl

theorem cell22_1203409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_1203409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203409 prefixEnd_1203409 := by exact prefixLift 1203409
  have htrace : WordTrace (prefixWord ++ tailWord_1203409) baseStart_1203409 baseEnd_1203409 := by
    simpa [prefixWord, tailWord_1203409, baseEnd_1203409] using wordTrace_append hprefix tailTrace_1203409
  have hstable : (prefixWord ++ tailWord_1203409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203409).length < 2 ^ (prefixWord ++ tailWord_1203409).sum := by decide
  have hdescent : baseEnd_1203409 < baseStart_1203409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203413 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1203413 : Nat := 118140960795 + 1203413 * 2 ^ 59
def prefixEnd_1203413 : Nat := 4983230072969 + 3 ^ 40 * 1203413 * 2
def baseEnd_1203413 : Nat := 411952863246136916535407

theorem tailTrace_1203413 : CollatzResearch.WordTrace tailWord_1203413 prefixEnd_1203413 411952863246136916535407 := by
  unfold tailWord_1203413
  simp only [CollatzResearch.WordTrace]
  refine ⟨43892077989247702422702893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29261385326165134948468595 43892077989247702422702893)
  ·
    refine ⟨16459529245967888408513585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43892077989247702422702893 16459529245967888408513585)
    ·
      refine ⟨12344646934475916306385189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16459529245967888408513585 12344646934475916306385189)
      ·
        refine ⟨2314621300214234307447223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12344646934475916306385189 2314621300214234307447223)
        ·
          refine ⟨3471931950321351461170835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314621300214234307447223 3471931950321351461170835)
          ·
            refine ⟨5207897925482027191756253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471931950321351461170835 5207897925482027191756253)
            ·
              refine ⟨1952961722055760196908595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5207897925482027191756253 1952961722055760196908595)
              ·
                refine ⟨2929442583083640295362893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952961722055760196908595 2929442583083640295362893)
                ·
                  refine ⟨1098540968656365110761085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2929442583083640295362893 1098540968656365110761085)
                  ·
                    refine ⟨411952863246136916535407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098540968656365110761085 411952863246136916535407)
                    ·
                      rfl

theorem cell22_1203413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1203413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203413 prefixEnd_1203413 := by exact prefixLift 1203413
  have htrace : WordTrace (prefixWord ++ tailWord_1203413) baseStart_1203413 baseEnd_1203413 := by
    simpa [prefixWord, tailWord_1203413, baseEnd_1203413] using wordTrace_append hprefix tailTrace_1203413
  have hstable : (prefixWord ++ tailWord_1203413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203413).length < 2 ^ (prefixWord ++ tailWord_1203413).sum := by decide
  have hdescent : baseEnd_1203413 < baseStart_1203413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203464 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1203464 : Nat := 118140960795 + 1203464 * 2 ^ 59
def prefixEnd_1203464 : Nat := 4983230072969 + 3 ^ 40 * 1203464 * 2
def baseEnd_1203464 : Nat := 411970321588389783510251

theorem tailTrace_1203464 : CollatzResearch.WordTrace tailWord_1203464 prefixEnd_1203464 411970321588389783510251 := by
  unfold tailWord_1203464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21946969056031469066404723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29262625408041958755206297 21946969056031469066404723)
  ·
    refine ⟨32920453584047203599607085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21946969056031469066404723 32920453584047203599607085)
    ·
      refine ⟨12345170094017701349852657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32920453584047203599607085 12345170094017701349852657)
      ·
        refine ⟨9258877570513276012389493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12345170094017701349852657 9258877570513276012389493)
        ·
          refine ⟨868019772235619626161515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9258877570513276012389493 868019772235619626161515)
          ·
            refine ⟨1302029658353429439242273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868019772235619626161515 1302029658353429439242273)
            ·
              refine ⟨976522243765072079431705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302029658353429439242273 976522243765072079431705)
              ·
                refine ⟨732391682823804059573779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976522243765072079431705 732391682823804059573779)
                ·
                  refine ⟨1098587524235706089360669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732391682823804059573779 1098587524235706089360669)
                  ·
                    refine ⟨411970321588389783510251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098587524235706089360669 411970321588389783510251)
                    ·
                      rfl

theorem cell22_1203464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1203464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203464 prefixEnd_1203464 := by exact prefixLift 1203464
  have htrace : WordTrace (prefixWord ++ tailWord_1203464) baseStart_1203464 baseEnd_1203464 := by
    simpa [prefixWord, tailWord_1203464, baseEnd_1203464] using wordTrace_append hprefix tailTrace_1203464
  have hstable : (prefixWord ++ tailWord_1203464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203464).length < 2 ^ (prefixWord ++ tailWord_1203464).sum := by decide
  have hdescent : baseEnd_1203464 < baseStart_1203464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203529 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1203529 : Nat := 118140960795 + 1203529 * 2 ^ 59
def prefixEnd_1203529 : Nat := 4983230072969 + 3 ^ 40 * 1203529 * 2
def baseEnd_1203529 : Nat := 411992572416751280635051

theorem tailTrace_1203529 : CollatzResearch.WordTrace tailWord_1203529 prefixEnd_1203529 411992572416751280635051 := by
  unfold tailWord_1203529
  simp only [CollatzResearch.WordTrace]
  refine ⟨43896308856827454233925641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29264205904551636155950427 43896308856827454233925641)
  ·
    refine ⟨32922231642620590675444231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43896308856827454233925641 32922231642620590675444231)
    ·
      refine ⟨49383347463930886013166347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32922231642620590675444231 49383347463930886013166347)
      ·
        refine ⟨74075021195896329019749521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49383347463930886013166347 74075021195896329019749521)
        ·
          refine ⟨55556265896922246764812141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74075021195896329019749521 55556265896922246764812141)
          ·
            refine ⟨20833599711345842536804553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55556265896922246764812141 20833599711345842536804553)
            ·
              refine ⟨15625199783509381902603415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20833599711345842536804553 15625199783509381902603415)
              ·
                refine ⟨23437799675264072853905123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15625199783509381902603415 23437799675264072853905123)
                ·
                  refine ⟨35156699512896109280857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23437799675264072853905123 35156699512896109280857685)
                  ·
                    refine ⟨411992572416751280635051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35156699512896109280857685 411992572416751280635051)
                    ·
                      rfl

theorem cell22_1203529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1203529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203529 prefixEnd_1203529 := by exact prefixLift 1203529
  have htrace : WordTrace (prefixWord ++ tailWord_1203529) baseStart_1203529 baseEnd_1203529 := by
    simpa [prefixWord, tailWord_1203529, baseEnd_1203529] using wordTrace_append hprefix tailTrace_1203529
  have hstable : (prefixWord ++ tailWord_1203529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203529).length < 2 ^ (prefixWord ++ tailWord_1203529).sum := by decide
  have hdescent : baseEnd_1203529 < baseStart_1203529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203640 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_1203640 : Nat := 118140960795 + 1203640 * 2 ^ 59
def prefixEnd_1203640 : Nat := 4983230072969 + 3 ^ 40 * 1203640 * 2
def baseEnd_1203640 : Nat := 137343523328394663703237

theorem tailTrace_1203640 : CollatzResearch.WordTrace tailWord_1203640 prefixEnd_1203640 137343523328394663703237 := by
  unfold tailWord_1203640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21950178679712660095608187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29266904906283546794144249 21950178679712660095608187)
  ·
    refine ⟨32925268019568990143412281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21950178679712660095608187 32925268019568990143412281)
    ·
      refine ⟨24693951014676742607559211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32925268019568990143412281 24693951014676742607559211)
      ·
        refine ⟨37040926522015113911338817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24693951014676742607559211 37040926522015113911338817)
        ·
          refine ⟨27780694891511335433504113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37040926522015113911338817 27780694891511335433504113)
          ·
            refine ⟨20835521168633501575128085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27780694891511335433504113 20835521168633501575128085)
            ·
              refine ⟨976665054779695386334129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20835521168633501575128085 976665054779695386334129)
              ·
                refine ⟨732498791084771539750597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976665054779695386334129 732498791084771539750597)
                ·
                  refine ⟨137343523328394663703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732498791084771539750597 137343523328394663703237)
                  ·
                    rfl

theorem cell22_1203640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_1203640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203640 prefixEnd_1203640 := by exact prefixLift 1203640
  have htrace : WordTrace (prefixWord ++ tailWord_1203640) baseStart_1203640 baseEnd_1203640 := by
    simpa [prefixWord, tailWord_1203640, baseEnd_1203640] using wordTrace_append hprefix tailTrace_1203640
  have hstable : (prefixWord ++ tailWord_1203640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203640).length < 2 ^ (prefixWord ++ tailWord_1203640).sum := by decide
  have hdescent : baseEnd_1203640 < baseStart_1203640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203651 : List Nat := [1, 1, 1, 3, 1, 1, 7, 7]
def baseStart_1203651 : Nat := 118140960795 + 1203651 * 2 ^ 59
def prefixEnd_1203651 : Nat := 4983230072969 + 3 ^ 40 * 1203651 * 2
def baseEnd_1203651 : Nat := 45781592834442625453853

theorem tailTrace_1203651 : CollatzResearch.WordTrace tailWord_1203651 prefixEnd_1203651 45781592834442625453853 := by
  unfold tailWord_1203651
  simp only [CollatzResearch.WordTrace]
  refine ⟨43900758562385469069866807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29267172374923646046577871 43900758562385469069866807)
  ·
    refine ⟨65851137843578203604800211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43900758562385469069866807 65851137843578203604800211)
    ·
      refine ⟨98776706765367305407200317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65851137843578203604800211 98776706765367305407200317)
      ·
        refine ⟨37041265037012739527700119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98776706765367305407200317 37041265037012739527700119)
        ·
          refine ⟨55561897555519109291550179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37041265037012739527700119 55561897555519109291550179)
          ·
            refine ⟨83342846333278663937325269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55561897555519109291550179 83342846333278663937325269)
            ·
              refine ⟨1953347960936218686031061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83342846333278663937325269 1953347960936218686031061)
              ·
                refine ⟨45781592834442625453853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1953347960936218686031061 45781592834442625453853)
                ·
                  rfl

theorem cell22_1203651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 7].length) (baseStart_1203651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203651 prefixEnd_1203651 := by exact prefixLift 1203651
  have htrace : WordTrace (prefixWord ++ tailWord_1203651) baseStart_1203651 baseEnd_1203651 := by
    simpa [prefixWord, tailWord_1203651, baseEnd_1203651] using wordTrace_append hprefix tailTrace_1203651
  have hstable : (prefixWord ++ tailWord_1203651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203651).length < 2 ^ (prefixWord ++ tailWord_1203651).sum := by decide
  have hdescent : baseEnd_1203651 < baseStart_1203651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203670 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1203670 : Nat := 118140960795 + 1203670 * 2 ^ 59
def prefixEnd_1203670 : Nat := 4983230072969 + 3 ^ 40 * 1203670 * 2
def baseEnd_1203670 : Nat := 412040839598273912859619

theorem tailTrace_1203670 : CollatzResearch.WordTrace tailWord_1203670 prefixEnd_1203670 412040839598273912859619 := by
  unfold tailWord_1203670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743840721832289707175529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29267634366211090209872309 2743840721832289707175529)
  ·
    refine ⟨2057880541374217280381647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2743840721832289707175529 2057880541374217280381647)
    ·
      refine ⟨3086820812061325920572471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2057880541374217280381647 3086820812061325920572471)
      ·
        refine ⟨4630231218091988880858707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086820812061325920572471 4630231218091988880858707)
        ·
          refine ⟨6945346827137983321288061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630231218091988880858707 6945346827137983321288061)
          ·
            refine ⟨2604505060176743745483023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6945346827137983321288061 2604505060176743745483023)
            ·
              refine ⟨3906757590265115618224535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604505060176743745483023 3906757590265115618224535)
              ·
                refine ⟨5860136385397673427336803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906757590265115618224535 5860136385397673427336803)
                ·
                  refine ⟨8790204578096510141005205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5860136385397673427336803 8790204578096510141005205)
                  ·
                    refine ⟨412040839598273912859619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8790204578096510141005205 412040839598273912859619)
                    ·
                      rfl

theorem cell22_1203670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1203670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203670 prefixEnd_1203670 := by exact prefixLift 1203670
  have htrace : WordTrace (prefixWord ++ tailWord_1203670) baseStart_1203670 baseEnd_1203670 := by
    simpa [prefixWord, tailWord_1203670, baseEnd_1203670] using wordTrace_append hprefix tailTrace_1203670
  have hstable : (prefixWord ++ tailWord_1203670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203670).length < 2 ^ (prefixWord ++ tailWord_1203670).sum := by decide
  have hdescent : baseEnd_1203670 < baseStart_1203670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203711 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_1203711 : Nat := 118140960795 + 1203711 * 2 ^ 59
def prefixEnd_1203711 : Nat := 4983230072969 + 3 ^ 40 * 1203711 * 2
def baseEnd_1203711 : Nat := 412054874736163472584493

theorem tailTrace_1203711 : CollatzResearch.WordTrace tailWord_1203711 prefixEnd_1203711 412054874736163472584493 := by
  unfold tailWord_1203711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43902946942168099317050987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29268631294778732878033991 43902946942168099317050987)
  ·
    refine ⟨65854420413252148975576481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43902946942168099317050987 65854420413252148975576481)
    ·
      refine ⟨49390815309939111731682361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65854420413252148975576481 49390815309939111731682361)
      ·
        refine ⟨37043111482454333798761771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49390815309939111731682361 37043111482454333798761771)
        ·
          refine ⟨55564667223681500698142657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37043111482454333798761771 55564667223681500698142657)
          ·
            refine ⟨41673500417761125523606993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55564667223681500698142657 41673500417761125523606993)
            ·
              refine ⟨31255125313320844142705245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41673500417761125523606993 31255125313320844142705245)
              ·
                refine ⟨11720671992495316553514467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31255125313320844142705245 11720671992495316553514467)
                ·
                  refine ⟨17581007988742974830271701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11720671992495316553514467 17581007988742974830271701)
                  ·
                    refine ⟨412054874736163472584493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17581007988742974830271701 412054874736163472584493)
                    ·
                      rfl

theorem cell22_1203711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_1203711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203711 prefixEnd_1203711 := by exact prefixLift 1203711
  have htrace : WordTrace (prefixWord ++ tailWord_1203711) baseStart_1203711 baseEnd_1203711 := by
    simpa [prefixWord, tailWord_1203711, baseEnd_1203711] using wordTrace_append hprefix tailTrace_1203711
  have hstable : (prefixWord ++ tailWord_1203711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203711).length < 2 ^ (prefixWord ++ tailWord_1203711).sum := by decide
  have hdescent : baseEnd_1203711 < baseStart_1203711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203833 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1203833 : Nat := 118140960795 + 1203833 * 2 ^ 59
def prefixEnd_1203833 : Nat := 4983230072969 + 3 ^ 40 * 1203833 * 2
def baseEnd_1203833 : Nat := 412096637829395821034119

theorem tailTrace_1203833 : CollatzResearch.WordTrace tailWord_1203833 prefixEnd_1203833 412096637829395821034119 := by
  unfold tailWord_1203833
  simp only [CollatzResearch.WordTrace]
  refine ⟨43907396647726114152992153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29271597765150742768661435 43907396647726114152992153)
  ·
    refine ⟨32930547485794585614744115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43907396647726114152992153 32930547485794585614744115)
    ·
      refine ⟨49395821228691878422116173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32930547485794585614744115 49395821228691878422116173)
      ·
        refine ⟨18523432960759454408293565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49395821228691878422116173 18523432960759454408293565)
        ·
          refine ⟨6946287360284795403110087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18523432960759454408293565 6946287360284795403110087)
          ·
            refine ⟨10419431040427193104665131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946287360284795403110087 10419431040427193104665131)
            ·
              refine ⟨15629146560640789656997697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419431040427193104665131 15629146560640789656997697)
              ·
                refine ⟨11721859920480592242748273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15629146560640789656997697 11721859920480592242748273)
                ·
                  refine ⟨8791394940360444182061205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11721859920480592242748273 8791394940360444182061205)
                  ·
                    refine ⟨412096637829395821034119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8791394940360444182061205 412096637829395821034119)
                    ·
                      rfl

theorem cell22_1203833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1203833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203833 prefixEnd_1203833 := by exact prefixLift 1203833
  have htrace : WordTrace (prefixWord ++ tailWord_1203833) baseStart_1203833 baseEnd_1203833 := by
    simpa [prefixWord, tailWord_1203833, baseEnd_1203833] using wordTrace_append hprefix tailTrace_1203833
  have hstable : (prefixWord ++ tailWord_1203833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203833).length < 2 ^ (prefixWord ++ tailWord_1203833).sum := by decide
  have hdescent : baseEnd_1203833 < baseStart_1203833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203835 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 3, 3]
def baseStart_1203835 : Nat := 118140960795 + 1203835 * 2 ^ 59
def prefixEnd_1203835 : Nat := 4983230072969 + 3 ^ 40 * 1203835 * 2
def baseEnd_1203835 : Nat := 412097322470268482484113

theorem tailTrace_1203835 : CollatzResearch.WordTrace tailWord_1203835 prefixEnd_1203835 412097322470268482484113 := by
  unfold tailWord_1203835
  simp only [CollatzResearch.WordTrace]
  refine ⟨43907469593718868494564959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29271646395812578996376639 43907469593718868494564959)
  ·
    refine ⟨65861204390578302741847439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43907469593718868494564959 65861204390578302741847439)
    ·
      refine ⟨98791806585867454112771159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65861204390578302741847439 98791806585867454112771159)
      ·
        refine ⟨148187709878801181169156739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98791806585867454112771159 148187709878801181169156739)
        ·
          refine ⟨222281564818201771753735109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148187709878801181169156739 222281564818201771753735109)
          ·
            refine ⟨41677793403412832203825333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222281564818201771753735109 41677793403412832203825333)
            ·
              refine ⟨3907293131569953019108625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41677793403412832203825333 3907293131569953019108625)
              ·
                refine ⟨2930469848677464764331469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907293131569953019108625 2930469848677464764331469)
                ·
                  refine ⟨1098926193254049286624301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2930469848677464764331469 1098926193254049286624301)
                  ·
                    refine ⟨412097322470268482484113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098926193254049286624301 412097322470268482484113)
                    ·
                      rfl

theorem cell22_1203835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].length) (baseStart_1203835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203835 prefixEnd_1203835 := by exact prefixLift 1203835
  have htrace : WordTrace (prefixWord ++ tailWord_1203835) baseStart_1203835 baseEnd_1203835 := by
    simpa [prefixWord, tailWord_1203835, baseEnd_1203835] using wordTrace_append hprefix tailTrace_1203835
  have hstable : (prefixWord ++ tailWord_1203835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203835).length < 2 ^ (prefixWord ++ tailWord_1203835).sum := by decide
  have hdescent : baseEnd_1203835 < baseStart_1203835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203933 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1203933 : Nat := 118140960795 + 1203933 * 2 ^ 59
def prefixEnd_1203933 : Nat := 4983230072969 + 3 ^ 40 * 1203933 * 2
def baseEnd_1203933 : Nat := 137376956624342964511271

theorem tailTrace_1203933 : CollatzResearch.WordTrace tailWord_1203933 prefixEnd_1203933 137376956624342964511271 := by
  unfold tailWord_1203933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43911043947363831231632453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29274029298242554154421635 43911043947363831231632453)
  ·
    refine ⟨8233320740130718355931085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43911043947363831231632453 8233320740130718355931085)
    ·
      refine ⟨3087495277549019383474157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8233320740130718355931085 3087495277549019383474157)
      ·
        refine ⟨1157810729080882268802809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3087495277549019383474157 1157810729080882268802809)
        ·
          refine ⟨868358046810661701602107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1157810729080882268802809 868358046810661701602107)
          ·
            refine ⟨1302537070215992552403161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868358046810661701602107 1302537070215992552403161)
            ·
              refine ⟨976902802661994414302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302537070215992552403161 976902802661994414302371)
              ·
                refine ⟨1465354203992991621453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976902802661994414302371 1465354203992991621453557)
                ·
                  refine ⟨137376956624342964511271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1465354203992991621453557 137376956624342964511271)
                  ·
                    rfl

theorem cell22_1203933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1203933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203933 prefixEnd_1203933 := by exact prefixLift 1203933
  have htrace : WordTrace (prefixWord ++ tailWord_1203933) baseStart_1203933 baseEnd_1203933 := by
    simpa [prefixWord, tailWord_1203933, baseEnd_1203933] using wordTrace_append hprefix tailTrace_1203933
  have hstable : (prefixWord ++ tailWord_1203933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203933).length < 2 ^ (prefixWord ++ tailWord_1203933).sum := by decide
  have hdescent : baseEnd_1203933 < baseStart_1203933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203940 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1203940 : Nat := 118140960795 + 1203940 * 2 ^ 59
def prefixEnd_1203940 : Nat := 4983230072969 + 3 ^ 40 * 1203940 * 2
def baseEnd_1203940 : Nat := 412133266116083208608791

theorem tailTrace_1203940 : CollatzResearch.WordTrace tailWord_1203940 prefixEnd_1203940 412133266116083208608791 := by
  unfold tailWord_1203940
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955649629169235713568637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29274199505558980951424849 21955649629169235713568637)
  ·
    refine ⟨8233368610938463392588239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21955649629169235713568637 8233368610938463392588239)
    ·
      refine ⟨12350052916407695088882359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233368610938463392588239 12350052916407695088882359)
      ·
        refine ⟨18525079374611542633323539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350052916407695088882359 18525079374611542633323539)
        ·
          refine ⟨27787619061917313949985309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18525079374611542633323539 27787619061917313949985309)
          ·
            refine ⟨10420357148218992731244491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27787619061917313949985309 10420357148218992731244491)
            ·
              refine ⟨15630535722328489096866737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10420357148218992731244491 15630535722328489096866737)
              ·
                refine ⟨11722901791746366822650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15630535722328489096866737 11722901791746366822650053)
                ·
                  refine ⟨2198044085952443779246885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11722901791746366822650053 2198044085952443779246885)
                  ·
                    refine ⟨412133266116083208608791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198044085952443779246885 412133266116083208608791)
                    ·
                      rfl

theorem cell22_1203940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1203940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1203940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1203940 prefixEnd_1203940 := by exact prefixLift 1203940
  have htrace : WordTrace (prefixWord ++ tailWord_1203940) baseStart_1203940 baseEnd_1203940 := by
    simpa [prefixWord, tailWord_1203940, baseEnd_1203940] using wordTrace_append hprefix tailTrace_1203940
  have hstable : (prefixWord ++ tailWord_1203940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203940).length < 2 ^ (prefixWord ++ tailWord_1203940).sum := by decide
  have hdescent : baseEnd_1203940 < baseStart_1203940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204004 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1204004 : Nat := 118140960795 + 1204004 * 2 ^ 59
def prefixEnd_1204004 : Nat := 4983230072969 + 3 ^ 40 * 1204004 * 2
def baseEnd_1204004 : Nat := 412155174624008375008595

theorem tailTrace_1204004 : CollatzResearch.WordTrace tailWord_1204004 prefixEnd_1204004 412155174624008375008595 := by
  unfold tailWord_1204004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956816765053305178733533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29275755686737740238311377 21956816765053305178733533)
  ·
    refine ⟨8233806286894989442025075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21956816765053305178733533 8233806286894989442025075)
    ·
      refine ⟨12350709430342484163037613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233806286894989442025075 12350709430342484163037613)
      ·
        refine ⟨4631516036378431561139105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12350709430342484163037613 4631516036378431561139105)
        ·
          refine ⟨3473637027283823670854329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631516036378431561139105 3473637027283823670854329)
          ·
            refine ⟨2605227770462867753140747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473637027283823670854329 2605227770462867753140747)
            ·
              refine ⟨3907841655694301629711121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605227770462867753140747 3907841655694301629711121)
              ·
                refine ⟨2930881241770726222283341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907841655694301629711121 2930881241770726222283341)
                ·
                  refine ⟨1099080465664022333356253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2930881241770726222283341 1099080465664022333356253)
                  ·
                    refine ⟨412155174624008375008595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099080465664022333356253 412155174624008375008595)
                    ·
                      rfl

theorem cell22_1204004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1204004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204004 prefixEnd_1204004 := by exact prefixLift 1204004
  have htrace : WordTrace (prefixWord ++ tailWord_1204004) baseStart_1204004 baseEnd_1204004 := by
    simpa [prefixWord, tailWord_1204004, baseEnd_1204004] using wordTrace_append hprefix tailTrace_1204004
  have hstable : (prefixWord ++ tailWord_1204004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204004).length < 2 ^ (prefixWord ++ tailWord_1204004).sum := by decide
  have hdescent : baseEnd_1204004 < baseStart_1204004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204038 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1204038 : Nat := 118140960795 + 1204038 * 2 ^ 59
def prefixEnd_1204038 : Nat := 4983230072969 + 3 ^ 40 * 1204038 * 2
def baseEnd_1204038 : Nat := 412166813518843619658491

theorem tailTrace_1204038 : CollatzResearch.WordTrace tailWord_1204038 prefixEnd_1204038 412166813518843619658491 := by
  unfold tailWord_1204038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372339800374482317631399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29276582407988956109469845 1372339800374482317631399)
  ·
    refine ⟨2058509700561723476447099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372339800374482317631399 2058509700561723476447099)
    ·
      refine ⟨3087764550842585214670649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058509700561723476447099 3087764550842585214670649)
      ·
        refine ⟨2315823413131938911002987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3087764550842585214670649 2315823413131938911002987)
        ·
          refine ⟨3473735119697908366504481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315823413131938911002987 3473735119697908366504481)
          ·
            refine ⟨2605301339773431274878361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473735119697908366504481 2605301339773431274878361)
            ·
              refine ⟨1953976004830073456158771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605301339773431274878361 1953976004830073456158771)
              ·
                refine ⟨2930964007245110184238157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953976004830073456158771 2930964007245110184238157)
                ·
                  refine ⟨1099111502716916319089309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2930964007245110184238157 1099111502716916319089309)
                  ·
                    refine ⟨412166813518843619658491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099111502716916319089309 412166813518843619658491)
                    ·
                      rfl

theorem cell22_1204038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1204038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204038 prefixEnd_1204038 := by exact prefixLift 1204038
  have htrace : WordTrace (prefixWord ++ tailWord_1204038) baseStart_1204038 baseEnd_1204038 := by
    simpa [prefixWord, tailWord_1204038, baseEnd_1204038] using wordTrace_append hprefix tailTrace_1204038
  have hstable : (prefixWord ++ tailWord_1204038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204038).length < 2 ^ (prefixWord ++ tailWord_1204038).sum := by decide
  have hdescent : baseEnd_1204038 < baseStart_1204038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204064 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_1204064 : Nat := 118140960795 + 1204064 * 2 ^ 59
def prefixEnd_1204064 : Nat := 4983230072969 + 3 ^ 40 * 1204064 * 2
def baseEnd_1204064 : Nat := 412175713850188218508411

theorem tailTrace_1204064 : CollatzResearch.WordTrace tailWord_1204064 prefixEnd_1204064 412175713850188218508411 := by
  unfold tailWord_1204064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957910954944620302325623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29277214606592827069767497 21957910954944620302325623)
  ·
    refine ⟨32936866432416930453488435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21957910954944620302325623 32936866432416930453488435)
    ·
      refine ⟨49405299648625395680232653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32936866432416930453488435 49405299648625395680232653)
      ·
        refine ⟨18526987368234523380087245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49405299648625395680232653 18526987368234523380087245)
        ·
          refine ⟨6947620263087946267532717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18526987368234523380087245 6947620263087946267532717)
          ·
            refine ⟨2605357598657979850324769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6947620263087946267532717 2605357598657979850324769)
            ·
              refine ⟨1954018198993484887743577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605357598657979850324769 1954018198993484887743577)
              ·
                refine ⟨1465513649245113665807683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954018198993484887743577 1465513649245113665807683)
                ·
                  refine ⟨2198270473867670498711525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465513649245113665807683 2198270473867670498711525)
                  ·
                    refine ⟨412175713850188218508411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198270473867670498711525 412175713850188218508411)
                    ·
                      rfl

theorem cell22_1204064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_1204064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204064 prefixEnd_1204064 := by exact prefixLift 1204064
  have htrace : WordTrace (prefixWord ++ tailWord_1204064) baseStart_1204064 baseEnd_1204064 := by
    simpa [prefixWord, tailWord_1204064, baseEnd_1204064] using wordTrace_append hprefix tailTrace_1204064
  have hstable : (prefixWord ++ tailWord_1204064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204064).length < 2 ^ (prefixWord ++ tailWord_1204064).sum := by decide
  have hdescent : baseEnd_1204064 < baseStart_1204064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204077 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1204077 : Nat := 118140960795 + 1204077 * 2 ^ 59
def prefixEnd_1204077 : Nat := 4983230072969 + 3 ^ 40 * 1204077 * 2
def baseEnd_1204077 : Nat := 412180164015860517933371

theorem tailTrace_1204077 : CollatzResearch.WordTrace tailWord_1204077 prefixEnd_1204077 412180164015860517933371 := by
  unfold tailWord_1204077
  simp only [CollatzResearch.WordTrace]
  refine ⟨43916296058842143824874485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29277530705894762549916323 43916296058842143824874485)
  ·
    refine ⟨4117152755516450983581983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43916296058842143824874485 4117152755516450983581983)
    ·
      refine ⟨6175729133274676475372975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117152755516450983581983 6175729133274676475372975)
      ·
        refine ⟨9263593699912014713059463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6175729133274676475372975 9263593699912014713059463)
        ·
          refine ⟨13895390549868022069589195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263593699912014713059463 13895390549868022069589195)
          ·
            refine ⟨20843085824802033104383793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895390549868022069589195 20843085824802033104383793)
            ·
              refine ⟨15632314368601524828287845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20843085824802033104383793 15632314368601524828287845)
              ·
                refine ⟨2931058944112785905303971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15632314368601524828287845 2931058944112785905303971)
                ·
                  refine ⟨4396588416169178857955957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931058944112785905303971 4396588416169178857955957)
                  ·
                    refine ⟨412180164015860517933371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4396588416169178857955957 412180164015860517933371)
                    ·
                      rfl

theorem cell22_1204077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1204077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204077 prefixEnd_1204077 := by exact prefixLift 1204077
  have htrace : WordTrace (prefixWord ++ tailWord_1204077) baseStart_1204077 baseEnd_1204077 := by
    simpa [prefixWord, tailWord_1204077, baseEnd_1204077] using wordTrace_append hprefix tailTrace_1204077
  have hstable : (prefixWord ++ tailWord_1204077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204077).length < 2 ^ (prefixWord ++ tailWord_1204077).sum := by decide
  have hdescent : baseEnd_1204077 < baseStart_1204077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204090 : List Nat := [3, 1, 1, 1, 1, 1, 14]
def baseStart_1204090 : Nat := 118140960795 + 1204090 * 2 ^ 59
def prefixEnd_1204090 : Nat := 4983230072969 + 3 ^ 40 * 1204090 * 2
def baseEnd_1204090 : Nat := 15266096821538252494753

theorem tailTrace_1204090 : CollatzResearch.WordTrace tailWord_1204090 prefixEnd_1204090 15266096821538252494753 := by
  unfold tailWord_1204090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10979192551948761761274431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29277846805196698030065149 10979192551948761761274431)
  ·
    refine ⟨16468788827923142641911647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10979192551948761761274431 16468788827923142641911647)
    ·
      refine ⟨24703183241884713962867471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16468788827923142641911647 24703183241884713962867471)
      ·
        refine ⟨37054774862827070944301207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24703183241884713962867471 37054774862827070944301207)
        ·
          refine ⟨55582162294240606416451811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37054774862827070944301207 55582162294240606416451811)
          ·
            refine ⟨83373243441360909624677717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55582162294240606416451811 83373243441360909624677717)
            ·
              refine ⟨15266096821538252494753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 83373243441360909624677717 15266096821538252494753)
              ·
                rfl

theorem cell22_1204090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 14].length) (baseStart_1204090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204090 prefixEnd_1204090 := by exact prefixLift 1204090
  have htrace : WordTrace (prefixWord ++ tailWord_1204090) baseStart_1204090 baseEnd_1204090 := by
    simpa [prefixWord, tailWord_1204090, baseEnd_1204090] using wordTrace_append hprefix tailTrace_1204090
  have hstable : (prefixWord ++ tailWord_1204090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204090).length < 2 ^ (prefixWord ++ tailWord_1204090).sum := by decide
  have hdescent : baseEnd_1204090 < baseStart_1204090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204229 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_1204229 : Nat := 118140960795 + 1204229 * 2 ^ 59
def prefixEnd_1204229 : Nat := 4983230072969 + 3 ^ 40 * 1204229 * 2
def baseEnd_1204229 : Nat := 412232196722182788132905

theorem tailTrace_1204229 : CollatzResearch.WordTrace tailWord_1204229 prefixEnd_1204229 412232196722182788132905 := by
  unfold tailWord_1204229
  simp only [CollatzResearch.WordTrace]
  refine ⟨43921839954291473784407741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29281226636194315856271827 43921839954291473784407741)
  ·
    refine ⟨16470689982859302669152903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43921839954291473784407741 16470689982859302669152903)
    ·
      refine ⟨24706034974288954003729355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16470689982859302669152903 24706034974288954003729355)
      ·
        refine ⟨37059052461433431005594033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24706034974288954003729355 37059052461433431005594033)
        ·
          refine ⟨27794289346075073254195525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37059052461433431005594033 27794289346075073254195525)
          ·
            refine ⟨5211429252389076235161661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27794289346075073254195525 5211429252389076235161661)
            ·
              refine ⟨1954285969645903588185623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5211429252389076235161661 1954285969645903588185623)
              ·
                refine ⟨2931428954468855382278435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954285969645903588185623 2931428954468855382278435)
                ·
                  refine ⟨4397143431703283073417653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931428954468855382278435 4397143431703283073417653)
                  ·
                    refine ⟨412232196722182788132905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4397143431703283073417653 412232196722182788132905)
                    ·
                      rfl

theorem cell22_1204229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_1204229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204229 prefixEnd_1204229 := by exact prefixLift 1204229
  have htrace : WordTrace (prefixWord ++ tailWord_1204229) baseStart_1204229 baseEnd_1204229 := by
    simpa [prefixWord, tailWord_1204229, baseEnd_1204229] using wordTrace_append hprefix tailTrace_1204229
  have hstable : (prefixWord ++ tailWord_1204229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204229).length < 2 ^ (prefixWord ++ tailWord_1204229).sum := by decide
  have hdescent : baseEnd_1204229 < baseStart_1204229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204280 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1204280 : Nat := 118140960795 + 1204280 * 2 ^ 59
def prefixEnd_1204280 : Nat := 4983230072969 + 3 ^ 40 * 1204280 * 2
def baseEnd_1204280 : Nat := 412249655064435655107749

theorem tailTrace_1204280 : CollatzResearch.WordTrace tailWord_1204280 prefixEnd_1204280 412249655064435655107749 := by
  unfold tailWord_1204280
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961850038553354747257147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29282466718071139663009529 21961850038553354747257147)
  ·
    refine ⟨32942775057830032120885721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961850038553354747257147 32942775057830032120885721)
    ·
      refine ⟨24707081293372524090664291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32942775057830032120885721 24707081293372524090664291)
      ·
        refine ⟨37060621940058786135996437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24707081293372524090664291 37060621940058786135996437)
        ·
          refine ⟨1737216653440255600124833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37060621940058786135996437 1737216653440255600124833)
          ·
            refine ⟨1302912490080191700093625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737216653440255600124833 1302912490080191700093625)
            ·
              refine ⟨977184367560143775070219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302912490080191700093625 977184367560143775070219)
              ·
                refine ⟨1465776551340215662605329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977184367560143775070219 1465776551340215662605329)
                ·
                  refine ⟨1099332413505161746953997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465776551340215662605329 1099332413505161746953997)
                  ·
                    refine ⟨412249655064435655107749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099332413505161746953997 412249655064435655107749)
                    ·
                      rfl

theorem cell22_1204280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1204280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204280 prefixEnd_1204280 := by exact prefixLift 1204280
  have htrace : WordTrace (prefixWord ++ tailWord_1204280) baseStart_1204280 baseEnd_1204280 := by
    simpa [prefixWord, tailWord_1204280, baseEnd_1204280] using wordTrace_append hprefix tailTrace_1204280
  have hstable : (prefixWord ++ tailWord_1204280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204280).length < 2 ^ (prefixWord ++ tailWord_1204280).sum := by decide
  have hdescent : baseEnd_1204280 < baseStart_1204280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204308 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1204308 : Nat := 118140960795 + 1204308 * 2 ^ 59
def prefixEnd_1204308 : Nat := 4983230072969 + 3 ^ 40 * 1204308 * 2
def baseEnd_1204308 : Nat := 412259240036652915407663

theorem tailTrace_1204308 : CollatzResearch.WordTrace tailWord_1204308 prefixEnd_1204308 412259240036652915407663 := by
  unfold tailWord_1204308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21962360660502635138266789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29283147547336846851022385 21962360660502635138266789)
  ·
    refine ⟨4117942623844244088425023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21962360660502635138266789 4117942623844244088425023)
    ·
      refine ⟨6176913935766366132637535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117942623844244088425023 6176913935766366132637535)
      ·
        refine ⟨9265370903649549198956303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176913935766366132637535 9265370903649549198956303)
        ·
          refine ⟨13898056355474323798434455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9265370903649549198956303 13898056355474323798434455)
          ·
            refine ⟨20847084533211485697651683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13898056355474323798434455 20847084533211485697651683)
            ·
              refine ⟨31270626799817228546477525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20847084533211485697651683 31270626799817228546477525)
              ·
                refine ⟨732905315620716294058067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31270626799817228546477525 732905315620716294058067)
                ·
                  refine ⟨1099357973431074441087101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732905315620716294058067 1099357973431074441087101)
                  ·
                    refine ⟨412259240036652915407663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099357973431074441087101 412259240036652915407663)
                    ·
                      rfl

theorem cell22_1204308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1204308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204308 prefixEnd_1204308 := by exact prefixLift 1204308
  have htrace : WordTrace (prefixWord ++ tailWord_1204308) baseStart_1204308 baseEnd_1204308 := by
    simpa [prefixWord, tailWord_1204308, baseEnd_1204308] using wordTrace_append hprefix tailTrace_1204308
  have hstable : (prefixWord ++ tailWord_1204308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204308).length < 2 ^ (prefixWord ++ tailWord_1204308).sum := by decide
  have hdescent : baseEnd_1204308 < baseStart_1204308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204325 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_1204325 : Nat := 118140960795 + 1204325 * 2 ^ 59
def prefixEnd_1204325 : Nat := 4983230072969 + 3 ^ 40 * 1204325 * 2
def baseEnd_1204325 : Nat := 412265059484070537732611

theorem tailTrace_1204325 : CollatzResearch.WordTrace tailWord_1204325 prefixEnd_1204325 412265059484070537732611 := by
  unfold tailWord_1204325
  simp only [CollatzResearch.WordTrace]
  refine ⟨43925341361943682179902429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29283560907962454786601619 43925341361943682179902429)
  ·
    refine ⟨16472003010728880817463411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43925341361943682179902429 16472003010728880817463411)
    ·
      refine ⟨24708004516093321226195117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16472003010728880817463411 24708004516093321226195117)
      ·
        refine ⟨9265501693534995459823169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24708004516093321226195117 9265501693534995459823169)
        ·
          refine ⟨6949126270151246594867377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9265501693534995459823169 6949126270151246594867377)
          ·
            refine ⟨5211844702613434946150533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949126270151246594867377 5211844702613434946150533)
            ·
              refine ⟨977220881740019052403225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5211844702613434946150533 977220881740019052403225)
              ·
                refine ⟨732915661305014289302419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977220881740019052403225 732915661305014289302419)
                ·
                  refine ⟨1099373491957521433953629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732915661305014289302419 1099373491957521433953629)
                  ·
                    refine ⟨412265059484070537732611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099373491957521433953629 412265059484070537732611)
                    ·
                      rfl

theorem cell22_1204325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_1204325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204325 prefixEnd_1204325 := by exact prefixLift 1204325
  have htrace : WordTrace (prefixWord ++ tailWord_1204325) baseStart_1204325 baseEnd_1204325 := by
    simpa [prefixWord, tailWord_1204325, baseEnd_1204325] using wordTrace_append hprefix tailTrace_1204325
  have hstable : (prefixWord ++ tailWord_1204325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204325).length < 2 ^ (prefixWord ++ tailWord_1204325).sum := by decide
  have hdescent : baseEnd_1204325 < baseStart_1204325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204349 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 8]
def baseStart_1204349 : Nat := 118140960795 + 1204349 * 2 ^ 59
def prefixEnd_1204349 : Nat := 4983230072969 + 3 ^ 40 * 1204349 * 2
def baseEnd_1204349 : Nat := 137424425058180825044179

theorem tailTrace_1204349 : CollatzResearch.WordTrace tailWord_1204349 prefixEnd_1204349 137424425058180825044179 := by
  unfold tailWord_1204349
  simp only [CollatzResearch.WordTrace]
  refine ⟨43926216713856734278776101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29284144475904489519184067 43926216713856734278776101)
  ·
    refine ⟨8236165633848137677270519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43926216713856734278776101 8236165633848137677270519)
    ·
      refine ⟨12354248450772206515905779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8236165633848137677270519 12354248450772206515905779)
      ·
        refine ⟨18531372676158309773858669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12354248450772206515905779 18531372676158309773858669)
        ·
          refine ⟨6949264753559366165197001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18531372676158309773858669 6949264753559366165197001)
          ·
            refine ⟨5211948565169524623897751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949264753559366165197001 5211948565169524623897751)
            ·
              refine ⟨7817922847754286935846627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211948565169524623897751 7817922847754286935846627)
              ·
                refine ⟨11726884271631430403769941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817922847754286935846627 11726884271631430403769941)
                ·
                  refine ⟨137424425058180825044179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11726884271631430403769941 137424425058180825044179)
                  ·
                    rfl

theorem cell22_1204349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_1204349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204349 prefixEnd_1204349 := by exact prefixLift 1204349
  have htrace : WordTrace (prefixWord ++ tailWord_1204349) baseStart_1204349 baseEnd_1204349 := by
    simpa [prefixWord, tailWord_1204349, baseEnd_1204349] using wordTrace_append hprefix tailTrace_1204349
  have hstable : (prefixWord ++ tailWord_1204349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204349).length < 2 ^ (prefixWord ++ tailWord_1204349).sum := by decide
  have hdescent : baseEnd_1204349 < baseStart_1204349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204372 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1204372 : Nat := 118140960795 + 1204372 * 2 ^ 59
def prefixEnd_1204372 : Nat := 4983230072969 + 3 ^ 40 * 1204372 * 2
def baseEnd_1204372 : Nat := 137427049514859360602489

theorem tailTrace_1204372 : CollatzResearch.WordTrace tailWord_1204372 prefixEnd_1204372 137427049514859360602489 := by
  unfold tailWord_1204372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963527796386704603431685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29284703728515606137908913 21963527796386704603431685)
  ·
    refine ⟨4118161461822507113143441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21963527796386704603431685 4118161461822507113143441)
    ·
      refine ⟨3088621096366880334857581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4118161461822507113143441 3088621096366880334857581)
      ·
        refine ⟨1158232911137580125571593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3088621096366880334857581 1158232911137580125571593)
        ·
          refine ⟨868674683353185094178695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158232911137580125571593 868674683353185094178695)
          ·
            refine ⟨1303012025029777641268043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868674683353185094178695 1303012025029777641268043)
            ·
              refine ⟨1954518037544666461902065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303012025029777641268043 1954518037544666461902065)
              ·
                refine ⟨1465888528158499846426549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954518037544666461902065 1465888528158499846426549)
                ·
                  refine ⟨137427049514859360602489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1465888528158499846426549 137427049514859360602489)
                  ·
                    rfl

theorem cell22_1204372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1204372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204372 prefixEnd_1204372 := by exact prefixLift 1204372
  have htrace : WordTrace (prefixWord ++ tailWord_1204372) baseStart_1204372 baseEnd_1204372 := by
    simpa [prefixWord, tailWord_1204372, baseEnd_1204372] using wordTrace_append hprefix tailTrace_1204372
  have hstable : (prefixWord ++ tailWord_1204372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204372).length < 2 ^ (prefixWord ++ tailWord_1204372).sum := by decide
  have hdescent : baseEnd_1204372 < baseStart_1204372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204383 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 4]
def baseStart_1204383 : Nat := 118140960795 + 1204383 * 2 ^ 59
def prefixEnd_1204383 : Nat := 4983230072969 + 3 ^ 40 * 1204383 * 2
def baseEnd_1204383 : Nat := 137428304689792573260811

theorem tailTrace_1204383 : CollatzResearch.WordTrace tailWord_1204383 prefixEnd_1204383 137428304689792573260811 := by
  unfold tailWord_1204383
  simp only [CollatzResearch.WordTrace]
  refine ⟨43927456795733558085513803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29284971197155705390342535 43927456795733558085513803)
  ·
    refine ⟨65891185193600337128270705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43927456795733558085513803 65891185193600337128270705)
    ·
      refine ⟨49418388895200252846203029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65891185193600337128270705 49418388895200252846203029)
      ·
        refine ⟨2316486979462511852165767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49418388895200252846203029 2316486979462511852165767)
        ·
          refine ⟨3474730469193767778248651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316486979462511852165767 3474730469193767778248651)
          ·
            refine ⟨5212095703790651667372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474730469193767778248651 5212095703790651667372977)
            ·
              refine ⟨3909071777842988750529733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212095703790651667372977 3909071777842988750529733)
              ·
                refine ⟨732950958345560390724325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3909071777842988750529733 732950958345560390724325)
                ·
                  refine ⟨137428304689792573260811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732950958345560390724325 137428304689792573260811)
                  ·
                    rfl

theorem cell22_1204383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 4].length) (baseStart_1204383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204383 prefixEnd_1204383 := by exact prefixLift 1204383
  have htrace : WordTrace (prefixWord ++ tailWord_1204383) baseStart_1204383 baseEnd_1204383 := by
    simpa [prefixWord, tailWord_1204383, baseEnd_1204383] using wordTrace_append hprefix tailTrace_1204383
  have hstable : (prefixWord ++ tailWord_1204383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204383).length < 2 ^ (prefixWord ++ tailWord_1204383).sum := by decide
  have hdescent : baseEnd_1204383 < baseStart_1204383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204409 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1204409 : Nat := 118140960795 + 1204409 * 2 ^ 59
def prefixEnd_1204409 : Nat := 4983230072969 + 3 ^ 40 * 1204409 * 2
def baseEnd_1204409 : Nat := 412293814400722318632353

theorem tailTrace_1204409 : CollatzResearch.WordTrace tailWord_1204409 prefixEnd_1204409 412293814400722318632353 := by
  unfold tailWord_1204409
  simp only [CollatzResearch.WordTrace]
  refine ⟨43928405093639364525960281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29285603395759576350640187 43928405093639364525960281)
  ·
    refine ⟨32946303820229523394470211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43928405093639364525960281 32946303820229523394470211)
    ·
      refine ⟨49419455730344285091705317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32946303820229523394470211 49419455730344285091705317)
      ·
        refine ⟨9266147949439553454694747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49419455730344285091705317 9266147949439553454694747)
        ·
          refine ⟨13899221924159330182042121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266147949439553454694747 13899221924159330182042121)
          ·
            refine ⟨10424416443119497636531591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13899221924159330182042121 10424416443119497636531591)
            ·
              refine ⟨15636624664679246454797387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10424416443119497636531591 15636624664679246454797387)
              ·
                refine ⟨23454936997018869682196081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15636624664679246454797387 23454936997018869682196081)
                ·
                  refine ⟨17591202747764152261647061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23454936997018869682196081 17591202747764152261647061)
                  ·
                    refine ⟨412293814400722318632353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17591202747764152261647061 412293814400722318632353)
                    ·
                      rfl

theorem cell22_1204409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1204409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204409 prefixEnd_1204409 := by exact prefixLift 1204409
  have htrace : WordTrace (prefixWord ++ tailWord_1204409) baseStart_1204409 baseEnd_1204409 := by
    simpa [prefixWord, tailWord_1204409, baseEnd_1204409] using wordTrace_append hprefix tailTrace_1204409
  have hstable : (prefixWord ++ tailWord_1204409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204409).length < 2 ^ (prefixWord ++ tailWord_1204409).sum := by decide
  have hdescent : baseEnd_1204409 < baseStart_1204409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204417 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 4]
def baseStart_1204417 : Nat := 118140960795 + 1204417 * 2 ^ 59
def prefixEnd_1204417 : Nat := 4983230072969 + 3 ^ 40 * 1204417 * 2
def baseEnd_1204417 : Nat := 137432184321404321477443

theorem tailTrace_1204417 : CollatzResearch.WordTrace tailWord_1204417 prefixEnd_1204417 137432184321404321477443 := by
  unfold tailWord_1204417
  simp only [CollatzResearch.WordTrace]
  refine ⟨43928696877610381892251505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29285797918406921261501003 43928696877610381892251505)
  ·
    refine ⟨32946522658207786419188629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43928696877610381892251505 32946522658207786419188629)
    ·
      refine ⟨1544368249603489988399467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32946522658207786419188629 1544368249603489988399467)
      ·
        refine ⟨2316552374405234982599201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544368249603489988399467 2316552374405234982599201)
        ·
          refine ⟨1737414280803926236949401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316552374405234982599201 1737414280803926236949401)
          ·
            refine ⟨1303060710602944677712051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737414280803926236949401 1303060710602944677712051)
            ·
              refine ⟨1954591065904417016568077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303060710602944677712051 1954591065904417016568077)
              ·
                refine ⟨732971649714156381213029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1954591065904417016568077 732971649714156381213029)
                ·
                  refine ⟨137432184321404321477443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732971649714156381213029 137432184321404321477443)
                  ·
                    rfl

theorem cell22_1204417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_1204417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204417 prefixEnd_1204417 := by exact prefixLift 1204417
  have htrace : WordTrace (prefixWord ++ tailWord_1204417) baseStart_1204417 baseEnd_1204417 := by
    simpa [prefixWord, tailWord_1204417, baseEnd_1204417] using wordTrace_append hprefix tailTrace_1204417
  have hstable : (prefixWord ++ tailWord_1204417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204417).length < 2 ^ (prefixWord ++ tailWord_1204417).sum := by decide
  have hdescent : baseEnd_1204417 < baseStart_1204417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204424 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1204424 : Nat := 118140960795 + 1204424 * 2 ^ 59
def prefixEnd_1204424 : Nat := 4983230072969 + 3 ^ 40 * 1204424 * 2
def baseEnd_1204424 : Nat := 412298949207267279507307

theorem tailTrace_1204424 : CollatzResearch.WordTrace tailWord_1204424 prefixEnd_1204424 412298949207267279507307 := by
  unfold tailWord_1204424
  simp only [CollatzResearch.WordTrace]
  refine ⟨21964476094292511043878163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29285968125723348058504217 21964476094292511043878163)
  ·
    refine ⟨32946714141438766565817245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21964476094292511043878163 32946714141438766565817245)
    ·
      refine ⟨12355017803039537462181467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32946714141438766565817245 12355017803039537462181467)
      ·
        refine ⟨18532526704559306193272201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12355017803039537462181467 18532526704559306193272201)
        ·
          refine ⟨13899395028419479644954151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18532526704559306193272201 13899395028419479644954151)
          ·
            refine ⟨20849092542629219467431227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13899395028419479644954151 20849092542629219467431227)
            ·
              refine ⟨31273638813943829201146841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20849092542629219467431227 31273638813943829201146841)
              ·
                refine ⟨23455229110457871900860131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31273638813943829201146841 23455229110457871900860131)
                ·
                  refine ⟨35182843665686807851290197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23455229110457871900860131 35182843665686807851290197)
                  ·
                    refine ⟨412298949207267279507307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35182843665686807851290197 412298949207267279507307)
                    ·
                      rfl

theorem cell22_1204424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1204424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204424 prefixEnd_1204424 := by exact prefixLift 1204424
  have htrace : WordTrace (prefixWord ++ tailWord_1204424) baseStart_1204424 baseEnd_1204424 := by
    simpa [prefixWord, tailWord_1204424, baseEnd_1204424] using wordTrace_append hprefix tailTrace_1204424
  have hstable : (prefixWord ++ tailWord_1204424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204424).length < 2 ^ (prefixWord ++ tailWord_1204424).sum := by decide
  have hdescent : baseEnd_1204424 < baseStart_1204424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204428 : List Nat := [2, 2, 1, 6, 1, 2, 8]
def baseStart_1204428 : Nat := 118140960795 + 1204428 * 2 ^ 59
def prefixEnd_1204428 : Nat := 4983230072969 + 3 ^ 40 * 1204428 * 2
def baseEnd_1204428 : Nat := 15270382166259726015085

theorem tailTrace_1204428 : CollatzResearch.WordTrace tailWord_1204428 prefixEnd_1204428 15270382166259726015085 := by
  unfold tailWord_1204428
  simp only [CollatzResearch.WordTrace]
  refine ⟨21964549040285265385450969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29286065387047020513934625 21964549040285265385450969)
  ·
    refine ⟨16473411780213949039088227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21964549040285265385450969 16473411780213949039088227)
    ·
      refine ⟨24710117670320923558632341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16473411780213949039088227 24710117670320923558632341)
      ·
        refine ⟨1158286765796293291810891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24710117670320923558632341 1158286765796293291810891)
        ·
          refine ⟨1737430148694439937716337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158286765796293291810891 1737430148694439937716337)
          ·
            refine ⟨1303072611520829953287253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737430148694439937716337 1303072611520829953287253)
            ·
              refine ⟨15270382166259726015085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1303072611520829953287253 15270382166259726015085)
              ·
                rfl

theorem cell22_1204428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 8].length) (baseStart_1204428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204428 prefixEnd_1204428 := by exact prefixLift 1204428
  have htrace : WordTrace (prefixWord ++ tailWord_1204428) baseStart_1204428 baseEnd_1204428 := by
    simpa [prefixWord, tailWord_1204428, baseEnd_1204428] using wordTrace_append hprefix tailTrace_1204428
  have hstable : (prefixWord ++ tailWord_1204428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204428).length < 2 ^ (prefixWord ++ tailWord_1204428).sum := by decide
  have hdescent : baseEnd_1204428 < baseStart_1204428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204531 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_1204531 : Nat := 118140960795 + 1204531 * 2 ^ 59
def prefixEnd_1204531 : Nat := 4983230072969 + 3 ^ 40 * 1204531 * 2
def baseEnd_1204531 : Nat := 412335577493954667081979

theorem tailTrace_1204531 : CollatzResearch.WordTrace tailWord_1204531 prefixEnd_1204531 412335577493954667081979 := by
  unfold tailWord_1204531
  simp only [CollatzResearch.WordTrace]
  refine ⟨43932854799197379361901447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29288569866131586241267631 43932854799197379361901447)
  ·
    refine ⟨65899282198796069042852171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43932854799197379361901447 65899282198796069042852171)
    ·
      refine ⟨98848923298194103564278257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65899282198796069042852171 98848923298194103564278257)
      ·
        refine ⟨74136692473645577673208693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98848923298194103564278257 74136692473645577673208693)
        ·
          refine ⟨6950314919404272906863315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74136692473645577673208693 6950314919404272906863315)
          ·
            refine ⟨10425472379106409360294973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950314919404272906863315 10425472379106409360294973)
            ·
              refine ⟨3909552142164903510110615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10425472379106409360294973 3909552142164903510110615)
              ·
                refine ⟨5864328213247355265165923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909552142164903510110615 5864328213247355265165923)
                ·
                  refine ⟨8796492319871032897748885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864328213247355265165923 8796492319871032897748885)
                  ·
                    refine ⟨412335577493954667081979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8796492319871032897748885 412335577493954667081979)
                    ·
                      rfl

theorem cell22_1204531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_1204531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204531 prefixEnd_1204531 := by exact prefixLift 1204531
  have htrace : WordTrace (prefixWord ++ tailWord_1204531) baseStart_1204531 baseEnd_1204531 := by
    simpa [prefixWord, tailWord_1204531, baseEnd_1204531] using wordTrace_append hprefix tailTrace_1204531
  have hstable : (prefixWord ++ tailWord_1204531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204531).length < 2 ^ (prefixWord ++ tailWord_1204531).sum := by decide
  have hdescent : baseEnd_1204531 < baseStart_1204531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204533 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1204533 : Nat := 118140960795 + 1204533 * 2 ^ 59
def prefixEnd_1204533 : Nat := 4983230072969 + 3 ^ 40 * 1204533 * 2
def baseEnd_1204533 : Nat := 412336262134827328531973

theorem tailTrace_1204533 : CollatzResearch.WordTrace tailWord_1204533 prefixEnd_1204533 412336262134827328531973 := by
  unfold tailWord_1204533
  simp only [CollatzResearch.WordTrace]
  refine ⟨43932927745190133703474253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29288618496793422468982835 43932927745190133703474253)
  ·
    refine ⟨16474847904446300138802845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43932927745190133703474253 16474847904446300138802845)
    ·
      refine ⟨6178067964167362552051067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16474847904446300138802845 6178067964167362552051067)
      ·
        refine ⟨9267101946251043828076601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6178067964167362552051067 9267101946251043828076601)
        ·
          refine ⟨6950326459688282871057451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9267101946251043828076601 6950326459688282871057451)
          ·
            refine ⟨10425489689532424306586177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950326459688282871057451 10425489689532424306586177)
            ·
              refine ⟨7819117267149318229939633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10425489689532424306586177 7819117267149318229939633)
              ·
                refine ⟨5864337950361988672454725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7819117267149318229939633 5864337950361988672454725)
                ·
                  refine ⟨1099563365692872876085261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5864337950361988672454725 1099563365692872876085261)
                  ·
                    refine ⟨412336262134827328531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099563365692872876085261 412336262134827328531973)
                    ·
                      rfl

theorem cell22_1204533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1204533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204533 prefixEnd_1204533 := by exact prefixLift 1204533
  have htrace : WordTrace (prefixWord ++ tailWord_1204533) baseStart_1204533 baseEnd_1204533 := by
    simpa [prefixWord, tailWord_1204533, baseEnd_1204533] using wordTrace_append hprefix tailTrace_1204533
  have hstable : (prefixWord ++ tailWord_1204533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204533).length < 2 ^ (prefixWord ++ tailWord_1204533).sum := by decide
  have hdescent : baseEnd_1204533 < baseStart_1204533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204537 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_1204537 : Nat := 118140960795 + 1204537 * 2 ^ 59
def prefixEnd_1204537 : Nat := 4983230072969 + 3 ^ 40 * 1204537 * 2
def baseEnd_1204537 : Nat := 412337631416572651431961

theorem tailTrace_1204537 : CollatzResearch.WordTrace tailWord_1204537 prefixEnd_1204537 412337631416572651431961 := by
  unfold tailWord_1204537
  simp only [CollatzResearch.WordTrace]
  refine ⟨43933073637175642386619865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29288715758117094924413243 43933073637175642386619865)
  ·
    refine ⟨32949805227881731789964899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43933073637175642386619865 32949805227881731789964899)
    ·
      refine ⟨49424707841822597684947349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32949805227881731789964899 49424707841822597684947349)
      ·
        refine ⟨2316783180085434266481907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49424707841822597684947349 2316783180085434266481907)
        ·
          refine ⟨3475174770128151399722861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316783180085434266481907 3475174770128151399722861)
          ·
            refine ⟨1303190538798056774896073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3475174770128151399722861 1303190538798056774896073)
            ·
              refine ⟨977392904098542581172055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303190538798056774896073 977392904098542581172055)
              ·
                refine ⟨1466089356147813871758083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977392904098542581172055 1466089356147813871758083)
                ·
                  refine ⟨2199134034221720807637125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466089356147813871758083 2199134034221720807637125)
                  ·
                    refine ⟨412337631416572651431961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199134034221720807637125 412337631416572651431961)
                    ·
                      rfl

theorem cell22_1204537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_1204537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204537 prefixEnd_1204537 := by exact prefixLift 1204537
  have htrace : WordTrace (prefixWord ++ tailWord_1204537) baseStart_1204537 baseEnd_1204537 := by
    simpa [prefixWord, tailWord_1204537, baseEnd_1204537] using wordTrace_append hprefix tailTrace_1204537
  have hstable : (prefixWord ++ tailWord_1204537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204537).length < 2 ^ (prefixWord ++ tailWord_1204537).sum := by decide
  have hdescent : baseEnd_1204537 < baseStart_1204537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204749 : List Nat := [1, 7, 1, 1, 1, 1, 4, 6]
def baseStart_1204749 : Nat := 118140960795 + 1204749 * 2 ^ 59
def prefixEnd_1204749 : Nat := 4983230072969 + 3 ^ 40 * 1204749 * 2
def baseEnd_1204749 : Nat := 45823355927674973903479

theorem tailTrace_1204749 : CollatzResearch.WordTrace tailWord_1204749 prefixEnd_1204749 45823355927674973903479 := by
  unfold tailWord_1204749
  simp only [CollatzResearch.WordTrace]
  refine ⟨43940805912407602593337301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29293870608271735062224867 43940805912407602593337301)
  ·
    refine ⟨1029862638572053185781343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43940805912407602593337301 1029862638572053185781343)
    ·
      refine ⟨1544793957858079778672015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029862638572053185781343 1544793957858079778672015)
      ·
        refine ⟨2317190936787119668008023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544793957858079778672015 2317190936787119668008023)
        ·
          refine ⟨3475786405180679502012035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317190936787119668008023 3475786405180679502012035)
          ·
            refine ⟨5213679607771019253018053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475786405180679502012035 5213679607771019253018053)
            ·
              refine ⟨977564926457066109940885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5213679607771019253018053 977564926457066109940885)
              ·
                refine ⟨45823355927674973903479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 977564926457066109940885 45823355927674973903479)
                ·
                  rfl

theorem cell22_1204749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 6].length) (baseStart_1204749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204749 prefixEnd_1204749 := by exact prefixLift 1204749
  have htrace : WordTrace (prefixWord ++ tailWord_1204749) baseStart_1204749 baseEnd_1204749 := by
    simpa [prefixWord, tailWord_1204749, baseEnd_1204749] using wordTrace_append hprefix tailTrace_1204749
  have hstable : (prefixWord ++ tailWord_1204749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204749).length < 2 ^ (prefixWord ++ tailWord_1204749).sum := by decide
  have hdescent : baseEnd_1204749 < baseStart_1204749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204764 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1204764 : Nat := 118140960795 + 1204764 * 2 ^ 59
def prefixEnd_1204764 : Nat := 4983230072969 + 3 ^ 40 * 1204764 * 2
def baseEnd_1204764 : Nat := 412415338155619726006265

theorem tailTrace_1204764 : CollatzResearch.WordTrace tailWord_1204764 prefixEnd_1204764 412415338155619726006265 := by
  unfold tailWord_1204764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21970676503676630077566673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29294235338235506770088897 21970676503676630077566673)
  ·
    refine ⟨16478007377757472558175005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21970676503676630077566673 16478007377757472558175005)
    ·
      refine ⟨6179252766659052209315627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16478007377757472558175005 6179252766659052209315627)
      ·
        refine ⟨9268879149988578313973441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6179252766659052209315627 9268879149988578313973441)
        ·
          refine ⟨6951659362491433735480081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9268879149988578313973441 6951659362491433735480081)
          ·
            refine ⟨5213744521868575301610061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951659362491433735480081 5213744521868575301610061)
            ·
              refine ⟨1955154195700715738103773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5213744521868575301610061 1955154195700715738103773)
              ·
                refine ⟨733182823387768401788915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955154195700715738103773 733182823387768401788915)
                ·
                  refine ⟨1099774235081652602683373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733182823387768401788915 1099774235081652602683373)
                  ·
                    refine ⟨412415338155619726006265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099774235081652602683373 412415338155619726006265)
                    ·
                      rfl

theorem cell22_1204764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1204764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204764 prefixEnd_1204764 := by exact prefixLift 1204764
  have htrace : WordTrace (prefixWord ++ tailWord_1204764) baseStart_1204764 baseEnd_1204764 := by
    simpa [prefixWord, tailWord_1204764, baseEnd_1204764] using wordTrace_append hprefix tailTrace_1204764
  have hstable : (prefixWord ++ tailWord_1204764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204764).length < 2 ^ (prefixWord ++ tailWord_1204764).sum := by decide
  have hdescent : baseEnd_1204764 < baseStart_1204764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204803 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_1204803 : Nat := 118140960795 + 1204803 * 2 ^ 59
def prefixEnd_1204803 : Nat := 4983230072969 + 3 ^ 40 * 1204803 * 2
def baseEnd_1204803 : Nat := 412428688652636624281145

theorem tailTrace_1204803 : CollatzResearch.WordTrace tailWord_1204803 prefixEnd_1204803 412428688652636624281145 := by
  unfold tailWord_1204803
  simp only [CollatzResearch.WordTrace]
  refine ⟨43942775454211969815803063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29295183636141313210535375 43942775454211969815803063)
  ·
    refine ⟨65914163181317954723704595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43942775454211969815803063 65914163181317954723704595)
    ·
      refine ⟨98871244771976932085556893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65914163181317954723704595 98871244771976932085556893)
      ·
        refine ⟨37076716789491349532083835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98871244771976932085556893 37076716789491349532083835)
        ·
          refine ⟨55615075184237024298125753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37076716789491349532083835 55615075184237024298125753)
          ·
            refine ⟨41711306388177768223594315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55615075184237024298125753 41711306388177768223594315)
            ·
              refine ⟨62566959582266652335391473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41711306388177768223594315 62566959582266652335391473)
              ·
                refine ⟨46925219686699989251543605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62566959582266652335391473 46925219686699989251543605)
                ·
                  refine ⟨4399239345628123992332213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46925219686699989251543605 4399239345628123992332213)
                  ·
                    refine ⟨412428688652636624281145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4399239345628123992332213 412428688652636624281145)
                    ·
                      rfl

theorem cell22_1204803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_1204803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204803 prefixEnd_1204803 := by exact prefixLift 1204803
  have htrace : WordTrace (prefixWord ++ tailWord_1204803) baseStart_1204803 baseEnd_1204803 := by
    simpa [prefixWord, tailWord_1204803, baseEnd_1204803] using wordTrace_append hprefix tailTrace_1204803
  have hstable : (prefixWord ++ tailWord_1204803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204803).length < 2 ^ (prefixWord ++ tailWord_1204803).sum := by decide
  have hdescent : baseEnd_1204803 < baseStart_1204803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204807 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1204807 : Nat := 118140960795 + 1204807 * 2 ^ 59
def prefixEnd_1204807 : Nat := 4983230072969 + 3 ^ 40 * 1204807 * 2
def baseEnd_1204807 : Nat := 412430057934381947181133

theorem tailTrace_1204807 : CollatzResearch.WordTrace tailWord_1204807 prefixEnd_1204807 412430057934381947181133 := by
  unfold tailWord_1204807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43942921346197478498948675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29295280897464985665965783 43942921346197478498948675)
  ·
    refine ⟨65914382019296217748423013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43942921346197478498948675 65914382019296217748423013)
    ·
      refine ⟨12358946628618040827829315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65914382019296217748423013 12358946628618040827829315)
      ·
        refine ⟨18538419942927061241743973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12358946628618040827829315 18538419942927061241743973)
        ·
          refine ⟨3475953739298823982826995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18538419942927061241743973 3475953739298823982826995)
          ·
            refine ⟨5213930608948235974240493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475953739298823982826995 5213930608948235974240493)
            ·
              refine ⟨1955223978355588490340185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5213930608948235974240493 1955223978355588490340185)
              ·
                refine ⟨1466417983766691367755139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955223978355588490340185 1466417983766691367755139)
                ·
                  refine ⟨2199626975650037051632709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466417983766691367755139 2199626975650037051632709)
                  ·
                    refine ⟨412430057934381947181133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199626975650037051632709 412430057934381947181133)
                    ·
                      rfl

theorem cell22_1204807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1204807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204807 prefixEnd_1204807 := by exact prefixLift 1204807
  have htrace : WordTrace (prefixWord ++ tailWord_1204807) baseStart_1204807 baseEnd_1204807 := by
    simpa [prefixWord, tailWord_1204807, baseEnd_1204807] using wordTrace_append hprefix tailTrace_1204807
  have hstable : (prefixWord ++ tailWord_1204807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204807).length < 2 ^ (prefixWord ++ tailWord_1204807).sum := by decide
  have hdescent : baseEnd_1204807 < baseStart_1204807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204820 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1204820 : Nat := 118140960795 + 1204820 * 2 ^ 59
def prefixEnd_1204820 : Nat := 4983230072969 + 3 ^ 40 * 1204820 * 2
def baseEnd_1204820 : Nat := 412434508100054246606093

theorem tailTrace_1204820 : CollatzResearch.WordTrace tailWord_1204820 prefixEnd_1204820 412434508100054246606093 := by
  unfold tailWord_1204820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21971697747575190859585957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29295596996766921146114609 21971697747575190859585957)
  ·
    refine ⟨4119693327670348286172367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21971697747575190859585957 4119693327670348286172367)
    ·
      refine ⟨6179539991505522429258551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119693327670348286172367 6179539991505522429258551)
      ·
        refine ⟨9269309987258283643887827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6179539991505522429258551 9269309987258283643887827)
        ·
          refine ⟨13903964980887425465831741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9269309987258283643887827 13903964980887425465831741)
          ·
            refine ⟨5213986867832784549686903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13903964980887425465831741 5213986867832784549686903)
            ·
              refine ⟨7820980301749176824530355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213986867832784549686903 7820980301749176824530355)
              ·
                refine ⟨11731470452623765236795533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7820980301749176824530355 11731470452623765236795533)
                ·
                  refine ⟨4399301419733911963798325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11731470452623765236795533 4399301419733911963798325)
                  ·
                    refine ⟨412434508100054246606093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4399301419733911963798325 412434508100054246606093)
                    ·
                      rfl

theorem cell22_1204820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1204820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204820 prefixEnd_1204820 := by exact prefixLift 1204820
  have htrace : WordTrace (prefixWord ++ tailWord_1204820) baseStart_1204820 baseEnd_1204820 := by
    simpa [prefixWord, tailWord_1204820, baseEnd_1204820] using wordTrace_append hprefix tailTrace_1204820
  have hstable : (prefixWord ++ tailWord_1204820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204820).length < 2 ^ (prefixWord ++ tailWord_1204820).sum := by decide
  have hdescent : baseEnd_1204820 < baseStart_1204820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204833 : List Nat := [1, 2, 3, 1, 1, 14]
def baseStart_1204833 : Nat := 118140960795 + 1204833 * 2 ^ 59
def prefixEnd_1204833 : Nat := 4983230072969 + 3 ^ 40 * 1204833 * 2
def baseEnd_1204833 : Nat := 5091838990934895630013

theorem tailTrace_1204833 : CollatzResearch.WordTrace tailWord_1204833 prefixEnd_1204833 5091838990934895630013 := by
  unfold tailWord_1204833
  simp only [CollatzResearch.WordTrace]
  refine ⟨43943869644103284939395153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29295913096068856626263435 43943869644103284939395153)
  ·
    refine ⟨32957902233077463704546365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43943869644103284939395153 32957902233077463704546365)
    ·
      refine ⟨12359213337404048889204887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32957902233077463704546365 12359213337404048889204887)
      ·
        refine ⟨18538820006106073333807331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12359213337404048889204887 18538820006106073333807331)
        ·
          refine ⟨27808230009159110000710997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18538820006106073333807331 27808230009159110000710997)
          ·
            refine ⟨5091838990934895630013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 27808230009159110000710997 5091838990934895630013)
            ·
              rfl

theorem cell22_1204833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 14].length) (baseStart_1204833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204833 prefixEnd_1204833 := by exact prefixLift 1204833
  have htrace : WordTrace (prefixWord ++ tailWord_1204833) baseStart_1204833 baseEnd_1204833 := by
    simpa [prefixWord, tailWord_1204833, baseEnd_1204833] using wordTrace_append hprefix tailTrace_1204833
  have hstable : (prefixWord ++ tailWord_1204833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204833).length < 2 ^ (prefixWord ++ tailWord_1204833).sum := by decide
  have hdescent : baseEnd_1204833 < baseStart_1204833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204835 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_1204835 : Nat := 118140960795 + 1204835 * 2 ^ 59
def prefixEnd_1204835 : Nat := 4983230072969 + 3 ^ 40 * 1204835 * 2
def baseEnd_1204835 : Nat := 412439642906599207481047

theorem tailTrace_1204835 : CollatzResearch.WordTrace tailWord_1204835 prefixEnd_1204835 412439642906599207481047 := by
  unfold tailWord_1204835
  simp only [CollatzResearch.WordTrace]
  refine ⟨43943942590096039280967959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29295961726730692853978639 43943942590096039280967959)
  ·
    refine ⟨65915913885144058921451939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43943942590096039280967959 65915913885144058921451939)
    ·
      refine ⟨98873870827716088382177909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65915913885144058921451939 98873870827716088382177909)
      ·
        refine ⟨9269425390098383285829179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98873870827716088382177909 9269425390098383285829179)
        ·
          refine ⟨13904138085147574928743769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9269425390098383285829179 13904138085147574928743769)
          ·
            refine ⟨10428103563860681196557827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13904138085147574928743769 10428103563860681196557827)
            ·
              refine ⟨15642155345791021794836741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428103563860681196557827 15642155345791021794836741)
              ·
                refine ⟨2932904127335816586531889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15642155345791021794836741 2932904127335816586531889)
                ·
                  refine ⟨2199678095501862439898917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932904127335816586531889 2199678095501862439898917)
                  ·
                    refine ⟨412439642906599207481047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199678095501862439898917 412439642906599207481047)
                    ·
                      rfl

theorem cell22_1204835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_1204835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204835 prefixEnd_1204835 := by exact prefixLift 1204835
  have htrace : WordTrace (prefixWord ++ tailWord_1204835) baseStart_1204835 baseEnd_1204835 := by
    simpa [prefixWord, tailWord_1204835, baseEnd_1204835] using wordTrace_append hprefix tailTrace_1204835
  have hstable : (prefixWord ++ tailWord_1204835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204835).length < 2 ^ (prefixWord ++ tailWord_1204835).sum := by decide
  have hdescent : baseEnd_1204835 < baseStart_1204835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204854 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1204854 : Nat := 118140960795 + 1204854 * 2 ^ 59
def prefixEnd_1204854 : Nat := 4983230072969 + 3 ^ 40 * 1204854 * 2
def baseEnd_1204854 : Nat := 412446146994889491255989

theorem tailTrace_1204854 : CollatzResearch.WordTrace tailWord_1204854 prefixEnd_1204854 412446146994889491255989 := by
  unfold tailWord_1204854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746539723564200345369351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29296423718018137017273077 2746539723564200345369351)
  ·
    refine ⟨4119809585346300518054027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746539723564200345369351 4119809585346300518054027)
    ·
      refine ⟨6179714378019450777081041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119809585346300518054027 6179714378019450777081041)
      ·
        refine ⟨4634785783514588082810781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6179714378019450777081041 4634785783514588082810781)
        ·
          refine ⟨1738044668817970531054043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4634785783514588082810781 1738044668817970531054043)
          ·
            refine ⟨2607067003226955796581065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738044668817970531054043 2607067003226955796581065)
            ·
              refine ⟨1955300252420216847435799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607067003226955796581065 1955300252420216847435799)
              ·
                refine ⟨2932950378630325271153699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955300252420216847435799 2932950378630325271153699)
                ·
                  refine ⟨4399425567945487906730549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932950378630325271153699 4399425567945487906730549)
                  ·
                    refine ⟨412446146994889491255989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4399425567945487906730549 412446146994889491255989)
                    ·
                      rfl

theorem cell22_1204854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1204854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204854 prefixEnd_1204854 := by exact prefixLift 1204854
  have htrace : WordTrace (prefixWord ++ tailWord_1204854) baseStart_1204854 baseEnd_1204854 := by
    simpa [prefixWord, tailWord_1204854, baseEnd_1204854] using wordTrace_append hprefix tailTrace_1204854
  have hstable : (prefixWord ++ tailWord_1204854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204854).length < 2 ^ (prefixWord ++ tailWord_1204854).sum := by decide
  have hdescent : baseEnd_1204854 < baseStart_1204854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204918 : List Nat := [5, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1204918 : Nat := 118140960795 + 1204918 * 2 ^ 59
def prefixEnd_1204918 : Nat := 4983230072969 + 3 ^ 40 * 1204918 * 2
def baseEnd_1204918 : Nat := 45829783944757184183977

theorem tailTrace_1204918 : CollatzResearch.WordTrace tailWord_1204918 prefixEnd_1204918 45829783944757184183977 := by
  unfold tailWord_1204918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746685615549709028514963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29297979899196896304159605 2746685615549709028514963)
  ·
    refine ⟨4120028423324563542772445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746685615549709028514963 4120028423324563542772445)
    ·
      refine ⟨1545010658746711328539667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4120028423324563542772445 1545010658746711328539667)
      ·
        refine ⟨2317515988120066992809501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545010658746711328539667 2317515988120066992809501)
        ·
          refine ⟨869068495545025122303563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2317515988120066992809501 869068495545025122303563)
          ·
            refine ⟨1303602743317537683455345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869068495545025122303563 1303602743317537683455345)
            ·
              refine ⟨977702057488153262591509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303602743317537683455345 977702057488153262591509)
              ·
                refine ⟨45829783944757184183977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 977702057488153262591509 45829783944757184183977)
                ·
                  rfl

theorem cell22_1204918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1204918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1204918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1204918 prefixEnd_1204918 := by exact prefixLift 1204918
  have htrace : WordTrace (prefixWord ++ tailWord_1204918) baseStart_1204918 baseEnd_1204918 := by
    simpa [prefixWord, tailWord_1204918, baseEnd_1204918] using wordTrace_append hprefix tailTrace_1204918
  have hstable : (prefixWord ++ tailWord_1204918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204918).length < 2 ^ (prefixWord ++ tailWord_1204918).sum := by decide
  have hdescent : baseEnd_1204918 < baseStart_1204918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205032 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1205032 : Nat := 118140960795 + 1205032 * 2 ^ 59
def prefixEnd_1205032 : Nat := 4983230072969 + 3 ^ 40 * 1205032 * 2
def baseEnd_1205032 : Nat := 412507080032556360305443

theorem tailTrace_1205032 : CollatzResearch.WordTrace tailWord_1205032 prefixEnd_1205032 412507080032556360305443 := by
  unfold tailWord_1205032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21975563885191170962944675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29300751846921561283926233 21975563885191170962944675)
  ·
    refine ⟨32963345827786756444417013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21975563885191170962944675 32963345827786756444417013)
    ·
      refine ⟨3090313671355008416664095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32963345827786756444417013 3090313671355008416664095)
      ·
        refine ⟨4635470507032512624996143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090313671355008416664095 4635470507032512624996143)
        ·
          refine ⟨6953205760548768937494215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635470507032512624996143 6953205760548768937494215)
          ·
            refine ⟨10429808640823153406241323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6953205760548768937494215 10429808640823153406241323)
            ·
              refine ⟨15644712961234730109361985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429808640823153406241323 15644712961234730109361985)
              ·
                refine ⟨11733534720926047582021489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15644712961234730109361985 11733534720926047582021489)
                ·
                  refine ⟨8800151040694535686516117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11733534720926047582021489 8800151040694535686516117)
                  ·
                    refine ⟨412507080032556360305443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8800151040694535686516117 412507080032556360305443)
                    ·
                      rfl

theorem cell22_1205032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1205032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205032 prefixEnd_1205032 := by exact prefixLift 1205032
  have htrace : WordTrace (prefixWord ++ tailWord_1205032) baseStart_1205032 baseEnd_1205032 := by
    simpa [prefixWord, tailWord_1205032, baseEnd_1205032] using wordTrace_append hprefix tailTrace_1205032
  have hstable : (prefixWord ++ tailWord_1205032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205032).length < 2 ^ (prefixWord ++ tailWord_1205032).sum := by decide
  have hdescent : baseEnd_1205032 < baseStart_1205032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205102 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1205102 : Nat := 118140960795 + 1205102 * 2 ^ 59
def prefixEnd_1205102 : Nat := 4983230072969 + 3 ^ 40 * 1205102 * 2
def baseEnd_1205102 : Nat := 412531042463099511055229

theorem tailTrace_1205102 : CollatzResearch.WordTrace tailWord_1205102 prefixEnd_1205102 412531042463099511055229 := by
  unfold tailWord_1205102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494210110016092985117195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29302453920085829253958373 5494210110016092985117195)
  ·
    refine ⟨8241315165024139477675793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494210110016092985117195 8241315165024139477675793)
    ·
      refine ⟨6180986373768104608256845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8241315165024139477675793 6180986373768104608256845)
      ·
        refine ⟨2317869890163039228096317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6180986373768104608256845 2317869890163039228096317)
        ·
          refine ⟨869201208811139710536119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2317869890163039228096317 869201208811139710536119)
          ·
            refine ⟨1303801813216709565804179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869201208811139710536119 1303801813216709565804179)
            ·
              refine ⟨1955702719825064348706269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303801813216709565804179 1955702719825064348706269)
              ·
                refine ⟨733388519934399130764851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955702719825064348706269 733388519934399130764851)
                ·
                  refine ⟨1100082779901598696147277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733388519934399130764851 1100082779901598696147277)
                  ·
                    refine ⟨412531042463099511055229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100082779901598696147277 412531042463099511055229)
                    ·
                      rfl

theorem cell22_1205102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1205102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205102 prefixEnd_1205102 := by exact prefixLift 1205102
  have htrace : WordTrace (prefixWord ++ tailWord_1205102) baseStart_1205102 baseEnd_1205102 := by
    simpa [prefixWord, tailWord_1205102, baseEnd_1205102] using wordTrace_append hprefix tailTrace_1205102
  have hstable : (prefixWord ++ tailWord_1205102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205102).length < 2 ^ (prefixWord ++ tailWord_1205102).sum := by decide
  have hdescent : baseEnd_1205102 < baseStart_1205102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205107 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_1205107 : Nat := 118140960795 + 1205107 * 2 ^ 59
def prefixEnd_1205107 : Nat := 4983230072969 + 3 ^ 40 * 1205107 * 2
def baseEnd_1205107 : Nat := 412532754065281164680213

theorem tailTrace_1205107 : CollatzResearch.WordTrace tailWord_1205107 prefixEnd_1205107 412532754065281164680213 := by
  unfold tailWord_1205107
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953863245110629734869575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29302575496740419823246383 43953863245110629734869575)
  ·
    refine ⟨65930794867665944602304363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43953863245110629734869575 65930794867665944602304363)
    ·
      refine ⟨98896192301498916903456545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65930794867665944602304363 98896192301498916903456545)
      ·
        refine ⟨74172144226124187677592409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98896192301498916903456545 74172144226124187677592409)
        ·
          refine ⟨55629108169593140758194307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74172144226124187677592409 55629108169593140758194307)
          ·
            refine ⟨83443662254389711137291461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55629108169593140758194307 83443662254389711137291461)
            ·
              refine ⟨15645686672698070838242149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83443662254389711137291461 15645686672698070838242149)
              ·
                refine ⟨2933566251130888282170403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15645686672698070838242149 2933566251130888282170403)
                ·
                  refine ⟨4400349376696332423255605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933566251130888282170403 4400349376696332423255605)
                  ·
                    refine ⟨412532754065281164680213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4400349376696332423255605 412532754065281164680213)
                    ·
                      rfl

theorem cell22_1205107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_1205107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205107 prefixEnd_1205107 := by exact prefixLift 1205107
  have htrace : WordTrace (prefixWord ++ tailWord_1205107) baseStart_1205107 baseEnd_1205107 := by
    simpa [prefixWord, tailWord_1205107, baseEnd_1205107] using wordTrace_append hprefix tailTrace_1205107
  have hstable : (prefixWord ++ tailWord_1205107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205107).length < 2 ^ (prefixWord ++ tailWord_1205107).sum := by decide
  have hdescent : baseEnd_1205107 < baseStart_1205107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205141 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1205141 : Nat := 118140960795 + 1205141 * 2 ^ 59
def prefixEnd_1205141 : Nat := 4983230072969 + 3 ^ 40 * 1205141 * 2
def baseEnd_1205141 : Nat := 412544392960116409330109

theorem tailTrace_1205141 : CollatzResearch.WordTrace tailWord_1205141 prefixEnd_1205141 412544392960116409330109 := by
  unfold tailWord_1205141
  simp only [CollatzResearch.WordTrace]
  refine ⟨43955103326987453541607277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29303402217991635694404851 43955103326987453541607277)
  ·
    refine ⟨16483163747620295078102729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43955103326987453541607277 16483163747620295078102729)
    ·
      refine ⟨12362372810715221308577047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16483163747620295078102729 12362372810715221308577047)
      ·
        refine ⟨18543559216072831962865571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12362372810715221308577047 18543559216072831962865571)
        ·
          refine ⟨27815338824109247944298357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18543559216072831962865571 27815338824109247944298357)
          ·
            refine ⟨2607688014760241994777971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27815338824109247944298357 2607688014760241994777971)
            ·
              refine ⟨3911532022140362992166957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607688014760241994777971 3911532022140362992166957)
              ·
                refine ⟨1466824508302636122062609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911532022140362992166957 1466824508302636122062609)
                ·
                  refine ⟨1100118381226977091546957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466824508302636122062609 1100118381226977091546957)
                  ·
                    refine ⟨412544392960116409330109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100118381226977091546957 412544392960116409330109)
                    ·
                      rfl

theorem cell22_1205141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1205141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205141 prefixEnd_1205141 := by exact prefixLift 1205141
  have htrace : WordTrace (prefixWord ++ tailWord_1205141) baseStart_1205141 baseEnd_1205141 := by
    simpa [prefixWord, tailWord_1205141, baseEnd_1205141] using wordTrace_append hprefix tailTrace_1205141
  have hstable : (prefixWord ++ tailWord_1205141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205141).length < 2 ^ (prefixWord ++ tailWord_1205141).sum := by decide
  have hdescent : baseEnd_1205141 < baseStart_1205141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205152 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1205152 : Nat := 118140960795 + 1205152 * 2 ^ 59
def prefixEnd_1205152 : Nat := 4983230072969 + 3 ^ 40 * 1205152 * 2
def baseEnd_1205152 : Nat := 412548158484916047305075

theorem tailTrace_1205152 : CollatzResearch.WordTrace tailWord_1205152 prefixEnd_1205152 412548158484916047305075 := by
  unfold tailWord_1205152
  simp only [CollatzResearch.WordTrace]
  refine ⟨21977752264973801210128855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29303669686631734946838473 21977752264973801210128855)
  ·
    refine ⟨32966628397460701815193283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21977752264973801210128855 32966628397460701815193283)
    ·
      refine ⟨49449942596191052722789925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32966628397460701815193283 49449942596191052722789925)
      ·
        refine ⟨9271864236785822385523111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49449942596191052722789925 9271864236785822385523111)
        ·
          refine ⟨13907796355178733578284667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9271864236785822385523111 13907796355178733578284667)
          ·
            refine ⟨20861694532768100367427001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13907796355178733578284667 20861694532768100367427001)
            ·
              refine ⟨15646270899576075275570251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20861694532768100367427001 15646270899576075275570251)
              ·
                refine ⟨23469406349364112913355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15646270899576075275570251 23469406349364112913355377)
                ·
                  refine ⟨17602054762023084685016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23469406349364112913355377 17602054762023084685016533)
                  ·
                    refine ⟨412548158484916047305075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17602054762023084685016533 412548158484916047305075)
                    ·
                      rfl

theorem cell22_1205152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1205152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205152 prefixEnd_1205152 := by exact prefixLift 1205152
  have htrace : WordTrace (prefixWord ++ tailWord_1205152) baseStart_1205152 baseEnd_1205152 := by
    simpa [prefixWord, tailWord_1205152, baseEnd_1205152] using wordTrace_append hprefix tailTrace_1205152
  have hstable : (prefixWord ++ tailWord_1205152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205152).length < 2 ^ (prefixWord ++ tailWord_1205152).sum := by decide
  have hdescent : baseEnd_1205152 < baseStart_1205152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205154 : List Nat := [3, 3, 1, 2, 2, 1, 2, 8]
def baseStart_1205154 : Nat := 118140960795 + 1205154 * 2 ^ 59
def prefixEnd_1205154 : Nat := 4983230072969 + 3 ^ 40 * 1205154 * 2
def baseEnd_1205154 : Nat := 45838760347309856528341

theorem tailTrace_1205154 : CollatzResearch.WordTrace tailWord_1205154 prefixEnd_1205154 45838760347309856528341 := by
  unfold tailWord_1205154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988894368985089190457629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29303718317293571174553677 10988894368985089190457629)
  ·
    refine ⟨4120835388369408446421611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10988894368985089190457629 4120835388369408446421611)
    ·
      refine ⟨6181253082554112669632417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120835388369408446421611 6181253082554112669632417)
      ·
        refine ⟨4635939811915584502224313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6181253082554112669632417 4635939811915584502224313)
        ·
          refine ⟨3476954858936688376668235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4635939811915584502224313 3476954858936688376668235)
          ·
            refine ⟨5215432288405032565002353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476954858936688376668235 5215432288405032565002353)
            ·
              refine ⟨3911574216303774423751765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215432288405032565002353 3911574216303774423751765)
              ·
                refine ⟨45838760347309856528341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3911574216303774423751765 45838760347309856528341)
                ·
                  rfl

theorem cell22_1205154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_1205154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205154 prefixEnd_1205154 := by exact prefixLift 1205154
  have htrace : WordTrace (prefixWord ++ tailWord_1205154) baseStart_1205154 baseEnd_1205154 := by
    simpa [prefixWord, tailWord_1205154, baseEnd_1205154] using wordTrace_append hprefix tailTrace_1205154
  have hstable : (prefixWord ++ tailWord_1205154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205154).length < 2 ^ (prefixWord ++ tailWord_1205154).sum := by decide
  have hdescent : baseEnd_1205154 < baseStart_1205154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205188 : List Nat := [2, 3, 3, 3, 1, 2, 1, 7]
def baseStart_1205188 : Nat := 118140960795 + 1205188 * 2 ^ 59
def prefixEnd_1205188 : Nat := 4983230072969 + 3 ^ 40 * 1205188 * 2
def baseEnd_1205188 : Nat := 45840053557847105933885

theorem tailTrace_1205188 : CollatzResearch.WordTrace tailWord_1205188 prefixEnd_1205188 45840053557847105933885 := by
  unfold tailWord_1205188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21978408778908590284284109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29304545038544787045712145 21978408778908590284284109)
  ·
    refine ⟨8241903292090721356606541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21978408778908590284284109 8241903292090721356606541)
    ·
      refine ⟨3090713734534020508727453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8241903292090721356606541 3090713734534020508727453)
      ·
        refine ⟨1159017650450257690772795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3090713734534020508727453 1159017650450257690772795)
        ·
          refine ⟨1738526475675386536159193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159017650450257690772795 1738526475675386536159193)
          ·
            refine ⟨1303894856756539902119395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738526475675386536159193 1303894856756539902119395)
            ·
              refine ⟨1955842285134809853179093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303894856756539902119395 1955842285134809853179093)
              ·
                refine ⟨45840053557847105933885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1955842285134809853179093 45840053557847105933885)
                ·
                  rfl

theorem cell22_1205188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_1205188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205188 prefixEnd_1205188 := by exact prefixLift 1205188
  have htrace : WordTrace (prefixWord ++ tailWord_1205188) baseStart_1205188 baseEnd_1205188 := by
    simpa [prefixWord, tailWord_1205188, baseEnd_1205188] using wordTrace_append hprefix tailTrace_1205188
  have hstable : (prefixWord ++ tailWord_1205188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205188).length < 2 ^ (prefixWord ++ tailWord_1205188).sum := by decide
  have hdescent : baseEnd_1205188 < baseStart_1205188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205199 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 5]
def baseStart_1205199 : Nat := 118140960795 + 1205199 * 2 ^ 59
def prefixEnd_1205199 : Nat := 4983230072969 + 3 ^ 40 * 1205199 * 2
def baseEnd_1205199 : Nat := 137521415848474530459977

theorem tailTrace_1205199 : CollatzResearch.WordTrace tailWord_1205199 prefixEnd_1205199 137521415848474530459977 := by
  unfold tailWord_1205199
  simp only [CollatzResearch.WordTrace]
  refine ⟨43957218760777329447218651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29304812507184886298145767 43957218760777329447218651)
  ·
    refine ⟨65935828141165994170827977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43957218760777329447218651 65935828141165994170827977)
    ·
      refine ⟨49451871105874495628120983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65935828141165994170827977 49451871105874495628120983)
      ·
        refine ⟨74177806658811743442181475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49451871105874495628120983 74177806658811743442181475)
        ·
          refine ⟨111266709988217615163272213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74177806658811743442181475 111266709988217615163272213)
          ·
            refine ⟨5215627030697700710778385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111266709988217615163272213 5215627030697700710778385)
            ·
              refine ⟨3911720273023275533083789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215627030697700710778385 3911720273023275533083789)
              ·
                refine ⟨1466895102383728324906421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911720273023275533083789 1466895102383728324906421)
                ·
                  refine ⟨137521415848474530459977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1466895102383728324906421 137521415848474530459977)
                  ·
                    rfl

theorem cell22_1205199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 5].length) (baseStart_1205199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205199 prefixEnd_1205199 := by exact prefixLift 1205199
  have htrace : WordTrace (prefixWord ++ tailWord_1205199) baseStart_1205199 baseEnd_1205199 := by
    simpa [prefixWord, tailWord_1205199, baseEnd_1205199] using wordTrace_append hprefix tailTrace_1205199
  have hstable : (prefixWord ++ tailWord_1205199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205199).length < 2 ^ (prefixWord ++ tailWord_1205199).sum := by decide
  have hdescent : baseEnd_1205199 < baseStart_1205199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205244 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1205244 : Nat := 118140960795 + 1205244 * 2 ^ 59
def prefixEnd_1205244 : Nat := 4983230072969 + 3 ^ 40 * 1205244 * 2
def baseEnd_1205244 : Nat := 137526550655019491334931

theorem tailTrace_1205244 : CollatzResearch.WordTrace tailWord_1205244 prefixEnd_1205244 137526550655019491334931 := by
  unfold tailWord_1205244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979430022807151066303393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29305906697076201421737857 21979430022807151066303393)
  ·
    refine ⟨16484572517105363299727545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21979430022807151066303393 16484572517105363299727545)
    ·
      refine ⟨12363429387829022474795659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16484572517105363299727545 12363429387829022474795659)
      ·
        refine ⟨18545144081743533712193489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12363429387829022474795659 18545144081743533712193489)
        ·
          refine ⟨13908858061307650284145117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18545144081743533712193489 13908858061307650284145117)
          ·
            refine ⟨5215821772990368856554419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13908858061307650284145117 5215821772990368856554419)
            ·
              refine ⟨7823732659485553284831629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215821772990368856554419 7823732659485553284831629)
              ·
                refine ⟨2933899747307082481811861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7823732659485553284831629 2933899747307082481811861)
                ·
                  refine ⟨137526550655019491334931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2933899747307082481811861 137526550655019491334931)
                  ·
                    rfl

theorem cell22_1205244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1205244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205244 prefixEnd_1205244 := by exact prefixLift 1205244
  have htrace : WordTrace (prefixWord ++ tailWord_1205244) baseStart_1205244 baseEnd_1205244 := by
    simpa [prefixWord, tailWord_1205244, baseEnd_1205244] using wordTrace_append hprefix tailTrace_1205244
  have hstable : (prefixWord ++ tailWord_1205244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205244).length < 2 ^ (prefixWord ++ tailWord_1205244).sum := by decide
  have hdescent : baseEnd_1205244 < baseStart_1205244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205274 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1205274 : Nat := 118140960795 + 1205274 * 2 ^ 59
def prefixEnd_1205274 : Nat := 4983230072969 + 3 ^ 40 * 1205274 * 2
def baseEnd_1205274 : Nat := 412589921578148395754701

theorem tailTrace_1205274 : CollatzResearch.WordTrace tailWord_1205274 prefixEnd_1205274 412589921578148395754701 := by
  unfold tailWord_1205274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989988558876404314049719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29306636157003744837465917 10989988558876404314049719)
  ·
    refine ⟨16484982838314606471074579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10989988558876404314049719 16484982838314606471074579)
    ·
      refine ⟨24727474257471909706611869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16484982838314606471074579 24727474257471909706611869)
      ·
        refine ⟨9272802846551966139979451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24727474257471909706611869 9272802846551966139979451)
        ·
          refine ⟨13909204269827949209969177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272802846551966139979451 13909204269827949209969177)
          ·
            refine ⟨10431903202370961907476883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13909204269827949209969177 10431903202370961907476883)
            ·
              refine ⟨15647854803556442861215325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10431903202370961907476883 15647854803556442861215325)
              ·
                refine ⟨5867945551333666072955747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15647854803556442861215325 5867945551333666072955747)
                ·
                  refine ⟨8801918327000499109433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867945551333666072955747 8801918327000499109433621)
                  ·
                    refine ⟨412589921578148395754701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8801918327000499109433621 412589921578148395754701)
                    ·
                      rfl

theorem cell22_1205274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1205274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205274 prefixEnd_1205274 := by exact prefixLift 1205274
  have htrace : WordTrace (prefixWord ++ tailWord_1205274) baseStart_1205274 baseEnd_1205274 := by
    simpa [prefixWord, tailWord_1205274, baseEnd_1205274] using wordTrace_append hprefix tailTrace_1205274
  have hstable : (prefixWord ++ tailWord_1205274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205274).length < 2 ^ (prefixWord ++ tailWord_1205274).sum := by decide
  have hdescent : baseEnd_1205274 < baseStart_1205274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205310 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1205310 : Nat := 118140960795 + 1205310 * 2 ^ 59
def prefixEnd_1205310 : Nat := 4983230072969 + 3 ^ 40 * 1205310 * 2
def baseEnd_1205310 : Nat := 412602245113856301854591

theorem tailTrace_1205310 : CollatzResearch.WordTrace tailWord_1205310 prefixEnd_1205310 412602245113856301854591 := by
  unfold tailWord_1205310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495158407921899425563673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29307511508916796936339589 5495158407921899425563673)
  ·
    refine ⟨4121368805941424569172755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5495158407921899425563673 4121368805941424569172755)
    ·
      refine ⟨6182053208912136853759133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121368805941424569172755 6182053208912136853759133)
      ·
        refine ⟨2318269953342051320159675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6182053208912136853759133 2318269953342051320159675)
        ·
          refine ⟨3477404930013076980239513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318269953342051320159675 3477404930013076980239513)
          ·
            refine ⟨2608053697509807735179635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477404930013076980239513 2608053697509807735179635)
            ·
              refine ⟨3912080546264711602769453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608053697509807735179635 3912080546264711602769453)
              ·
                refine ⟨1467030204849266851038545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3912080546264711602769453 1467030204849266851038545)
                ·
                  refine ⟨1100272653636950138278909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467030204849266851038545 1100272653636950138278909)
                  ·
                    refine ⟨412602245113856301854591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100272653636950138278909 412602245113856301854591)
                    ·
                      rfl

theorem cell22_1205310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1205310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205310 prefixEnd_1205310 := by exact prefixLift 1205310
  have htrace : WordTrace (prefixWord ++ tailWord_1205310) baseStart_1205310 baseEnd_1205310 := by
    simpa [prefixWord, tailWord_1205310, baseEnd_1205310] using wordTrace_append hprefix tailTrace_1205310
  have hstable : (prefixWord ++ tailWord_1205310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205310).length < 2 ^ (prefixWord ++ tailWord_1205310).sum := by decide
  have hdescent : baseEnd_1205310 < baseStart_1205310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205351 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 5]
def baseStart_1205351 : Nat := 118140960795 + 1205351 * 2 ^ 59
def prefixEnd_1205351 : Nat := 4983230072969 + 3 ^ 40 * 1205351 * 2
def baseEnd_1205351 : Nat := 137538760083915287193155

theorem tailTrace_1205351 : CollatzResearch.WordTrace tailWord_1205351 prefixEnd_1205351 137538760083915287193155 := by
  unfold tailWord_1205351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43962762656226659406751907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29308508437484439604501271 43962762656226659406751907)
  ·
    refine ⟨65944143984339989110127861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43962762656226659406751907 65944143984339989110127861)
    ·
      refine ⟨6182263498531873979074487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65944143984339989110127861 6182263498531873979074487)
      ·
        refine ⟨9273395247797810968611731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182263498531873979074487 9273395247797810968611731)
        ·
          refine ⟨13910092871696716452917597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273395247797810968611731 13910092871696716452917597)
          ·
            refine ⟨5216284826886268669844099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13910092871696716452917597 5216284826886268669844099)
            ·
              refine ⟨7824427240329403004766149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216284826886268669844099 7824427240329403004766149)
              ·
                refine ⟨1467080107561763063393653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7824427240329403004766149 1467080107561763063393653)
                ·
                  refine ⟨137538760083915287193155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1467080107561763063393653 137538760083915287193155)
                  ·
                    rfl

theorem cell22_1205351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 5].length) (baseStart_1205351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205351 prefixEnd_1205351 := by exact prefixLift 1205351
  have htrace : WordTrace (prefixWord ++ tailWord_1205351) baseStart_1205351 baseEnd_1205351 := by
    simpa [prefixWord, tailWord_1205351, baseEnd_1205351] using wordTrace_append hprefix tailTrace_1205351
  have hstable : (prefixWord ++ tailWord_1205351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205351).length < 2 ^ (prefixWord ++ tailWord_1205351).sum := by decide
  have hdescent : baseEnd_1205351 < baseStart_1205351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205413 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 4]
def baseStart_1205413 : Nat := 118140960795 + 1205413 * 2 ^ 59
def prefixEnd_1205413 : Nat := 4983230072969 + 3 ^ 40 * 1205413 * 2
def baseEnd_1205413 : Nat := 137545834706266122176425

theorem tailTrace_1205413 : CollatzResearch.WordTrace tailWord_1205413 prefixEnd_1205413 137545834706266122176425 := by
  unfold tailWord_1205413
  simp only [CollatzResearch.WordTrace]
  refine ⟨43965023982002043995508893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29310015988001362663672595 43965023982002043995508893)
  ·
    refine ⟨16486883993250766498315835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43965023982002043995508893 16486883993250766498315835)
    ·
      refine ⟨24730325989876149747473753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16486883993250766498315835 24730325989876149747473753)
      ·
        refine ⟨18547744492407112310605315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24730325989876149747473753 18547744492407112310605315)
        ·
          refine ⟨27821616738610668465907973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18547744492407112310605315 27821616738610668465907973)
          ·
            refine ⟨5216553138489500337357745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27821616738610668465907973 5216553138489500337357745)
            ·
              refine ⟨3912414853867125253018309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216553138489500337357745 3912414853867125253018309)
              ·
                refine ⟨733577785100085984940933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3912414853867125253018309 733577785100085984940933)
                ·
                  refine ⟨137545834706266122176425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733577785100085984940933 137545834706266122176425)
                  ·
                    rfl

theorem cell22_1205413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_1205413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205413 prefixEnd_1205413 := by exact prefixLift 1205413
  have htrace : WordTrace (prefixWord ++ tailWord_1205413) baseStart_1205413 baseEnd_1205413 := by
    simpa [prefixWord, tailWord_1205413, baseEnd_1205413] using wordTrace_append hprefix tailTrace_1205413
  have hstable : (prefixWord ++ tailWord_1205413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205413).length < 2 ^ (prefixWord ++ tailWord_1205413).sum := by decide
  have hdescent : baseEnd_1205413 < baseStart_1205413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205426 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1205426 : Nat := 118140960795 + 1205426 * 2 ^ 59
def prefixEnd_1205426 : Nat := 4983230072969 + 3 ^ 40 * 1205426 * 2
def baseEnd_1205426 : Nat := 412641954284470665954235

theorem tailTrace_1205426 : CollatzResearch.WordTrace tailWord_1205426 prefixEnd_1205426 412641954284470665954235 := by
  unfold tailWord_1205426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991374532738736803933033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29310332087303298143821421 10991374532738736803933033)
  ·
    refine ⟨8243530899554052602949775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10991374532738736803933033 8243530899554052602949775)
    ·
      refine ⟨12365296349331078904424663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8243530899554052602949775 12365296349331078904424663)
      ·
        refine ⟨18547944523996618356636995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12365296349331078904424663 18547944523996618356636995)
        ·
          refine ⟨27821916785994927534955493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18547944523996618356636995 27821916785994927534955493)
          ·
            refine ⟨5216609397374048912804155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27821916785994927534955493 5216609397374048912804155)
            ·
              refine ⟨7824914096061073369206233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216609397374048912804155 7824914096061073369206233)
              ·
                refine ⟨5868685572045805026904675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7824914096061073369206233 5868685572045805026904675)
                ·
                  refine ⟨8803028358068707540357013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5868685572045805026904675 8803028358068707540357013)
                  ·
                    refine ⟨412641954284470665954235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8803028358068707540357013 412641954284470665954235)
                    ·
                      rfl

theorem cell22_1205426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1205426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205426 prefixEnd_1205426 := by exact prefixLift 1205426
  have htrace : WordTrace (prefixWord ++ tailWord_1205426) baseStart_1205426 baseEnd_1205426 := by
    simpa [prefixWord, tailWord_1205426, baseEnd_1205426] using wordTrace_append hprefix tailTrace_1205426
  have hstable : (prefixWord ++ tailWord_1205426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205426).length < 2 ^ (prefixWord ++ tailWord_1205426).sum := by decide
  have hdescent : baseEnd_1205426 < baseStart_1205426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205479 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1205479 : Nat := 118140960795 + 1205479 * 2 ^ 59
def prefixEnd_1205479 : Nat := 4983230072969 + 3 ^ 40 * 1205479 * 2
def baseEnd_1205479 : Nat := 412660097267596194379073

theorem tailTrace_1205479 : CollatzResearch.WordTrace tailWord_1205479 prefixEnd_1205479 412660097267596194379073 := by
  unfold tailWord_1205479
  simp only [CollatzResearch.WordTrace]
  refine ⟨43967431199762937267411491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29311620799841958178274327 43967431199762937267411491)
  ·
    refine ⟨65951146799644405901117237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43967431199762937267411491 65951146799644405901117237)
    ·
      refine ⟨6182920012466663053229741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65951146799644405901117237 6182920012466663053229741)
      ·
        refine ⟨2318595004674998644961153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6182920012466663053229741 2318595004674998644961153)
        ·
          refine ⟨1738946253506248983720865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2318595004674998644961153 1738946253506248983720865)
          ·
            refine ⟨1304209690129686737790649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738946253506248983720865 1304209690129686737790649)
            ·
              refine ⟨978157267597265053342987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304209690129686737790649 978157267597265053342987)
              ·
                refine ⟨1467235901395897580014481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978157267597265053342987 1467235901395897580014481)
                ·
                  refine ⟨1100426926046923185010861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467235901395897580014481 1100426926046923185010861)
                  ·
                    refine ⟨412660097267596194379073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100426926046923185010861 412660097267596194379073)
                    ·
                      rfl

theorem cell22_1205479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1205479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205479 prefixEnd_1205479 := by exact prefixLift 1205479
  have htrace : WordTrace (prefixWord ++ tailWord_1205479) baseStart_1205479 baseEnd_1205479 := by
    simpa [prefixWord, tailWord_1205479, baseEnd_1205479] using wordTrace_append hprefix tailTrace_1205479
  have hstable : (prefixWord ++ tailWord_1205479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205479).length < 2 ^ (prefixWord ++ tailWord_1205479).sum := by decide
  have hdescent : baseEnd_1205479 < baseStart_1205479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205501 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1205501 : Nat := 118140960795 + 1205501 * 2 ^ 59
def prefixEnd_1205501 : Nat := 4983230072969 + 3 ^ 40 * 1205501 * 2
def baseEnd_1205501 : Nat := 412667628317195470329005

theorem tailTrace_1205501 : CollatzResearch.WordTrace tailWord_1205501 prefixEnd_1205501 412667628317195470329005 := by
  unfold tailWord_1205501
  simp only [CollatzResearch.WordTrace]
  refine ⟨43968233605683235024712357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29312155737122156683141571 43968233605683235024712357)
  ·
    refine ⟨8244043801065606567133567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43968233605683235024712357 8244043801065606567133567)
    ·
      refine ⟨12366065701598409850700351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8244043801065606567133567 12366065701598409850700351)
      ·
        refine ⟨18549098552397614776050527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366065701598409850700351 18549098552397614776050527)
        ·
          refine ⟨27823647828596422164075791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18549098552397614776050527 27823647828596422164075791)
          ·
            refine ⟨41735471742894633246113687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27823647828596422164075791 41735471742894633246113687)
            ·
              refine ⟨62603207614341949869170531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41735471742894633246113687 62603207614341949869170531)
              ·
                refine ⟨93904811421512924803755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62603207614341949869170531 93904811421512924803755797)
                ·
                  refine ⟨4401788035383418350176053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93904811421512924803755797 4401788035383418350176053)
                  ·
                    refine ⟨412667628317195470329005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4401788035383418350176053 412667628317195470329005)
                    ·
                      rfl

theorem cell22_1205501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1205501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205501 prefixEnd_1205501 := by exact prefixLift 1205501
  have htrace : WordTrace (prefixWord ++ tailWord_1205501) baseStart_1205501 baseEnd_1205501 := by
    simpa [prefixWord, tailWord_1205501, baseEnd_1205501] using wordTrace_append hprefix tailTrace_1205501
  have hstable : (prefixWord ++ tailWord_1205501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205501).length < 2 ^ (prefixWord ++ tailWord_1205501).sum := by decide
  have hdescent : baseEnd_1205501 < baseStart_1205501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205531 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 6]
def baseStart_1205531 : Nat := 118140960795 + 1205531 * 2 ^ 59
def prefixEnd_1205531 : Nat := 4983230072969 + 3 ^ 40 * 1205531 * 2
def baseEnd_1205531 : Nat := 137559299310095130692971

theorem tailTrace_1205531 : CollatzResearch.WordTrace tailWord_1205531 prefixEnd_1205531 137559299310095130692971 := by
  unfold tailWord_1205531
  simp only [CollatzResearch.WordTrace]
  refine ⟨43969327795574550148304447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29312885197049700098869631 43969327795574550148304447)
  ·
    refine ⟨65953991693361825222456671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43969327795574550148304447 65953991693361825222456671)
    ·
      refine ⟨98930987540042737833685007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65953991693361825222456671 98930987540042737833685007)
      ·
        refine ⟨148396481310064106750527511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98930987540042737833685007 148396481310064106750527511)
        ·
          refine ⟨222594721965096160125791267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148396481310064106750527511 222594721965096160125791267)
          ·
            refine ⟨333892082947644240188686901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222594721965096160125791267 333892082947644240188686901)
            ·
              refine ⟨31302382776341647517689397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 333892082947644240188686901 31302382776341647517689397)
              ·
                refine ⟨2934598385282029454783381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31302382776341647517689397 2934598385282029454783381)
                ·
                  refine ⟨137559299310095130692971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2934598385282029454783381 137559299310095130692971)
                  ·
                    rfl

theorem cell22_1205531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_1205531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205531 prefixEnd_1205531 := by exact prefixLift 1205531
  have htrace : WordTrace (prefixWord ++ tailWord_1205531) baseStart_1205531 baseEnd_1205531 := by
    simpa [prefixWord, tailWord_1205531, baseEnd_1205531] using wordTrace_append hprefix tailTrace_1205531
  have hstable : (prefixWord ++ tailWord_1205531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205531).length < 2 ^ (prefixWord ++ tailWord_1205531).sum := by decide
  have hdescent : baseEnd_1205531 < baseStart_1205531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205567 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 1, 4]
def baseStart_1205567 : Nat := 118140960795 + 1205567 * 2 ^ 59
def prefixEnd_1205567 : Nat := 4983230072969 + 3 ^ 40 * 1205567 * 2
def baseEnd_1205567 : Nat := 412690221465993298178803

theorem tailTrace_1205567 : CollatzResearch.WordTrace tailWord_1205567 prefixEnd_1205567 412690221465993298178803 := by
  unfold tailWord_1205567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43970640823444128296614955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29313760548962752197743303 43970640823444128296614955)
  ·
    refine ⟨65955961235166192444922433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43970640823444128296614955 65955961235166192444922433)
    ·
      refine ⟨49466970926374644333691825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65955961235166192444922433 49466970926374644333691825)
      ·
        refine ⟨37100228194780983250268869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49466970926374644333691825 37100228194780983250268869)
        ·
          refine ⟨6956292786521434359425413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37100228194780983250268869 6956292786521434359425413)
          ·
            refine ⟨1304304897472768942392265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6956292786521434359425413 1304304897472768942392265)
            ·
              refine ⟨978228673104576706794199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304304897472768942392265 978228673104576706794199)
              ·
                refine ⟨1467343009656865060191299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978228673104576706794199 1467343009656865060191299)
                ·
                  refine ⟨2201014514485297590286949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467343009656865060191299 2201014514485297590286949)
                  ·
                    refine ⟨412690221465993298178803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201014514485297590286949 412690221465993298178803)
                    ·
                      rfl

theorem cell22_1205567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_1205567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205567 prefixEnd_1205567 := by exact prefixLift 1205567
  have htrace : WordTrace (prefixWord ++ tailWord_1205567) baseStart_1205567 baseEnd_1205567 := by
    simpa [prefixWord, tailWord_1205567, baseEnd_1205567] using wordTrace_append hprefix tailTrace_1205567
  have hstable : (prefixWord ++ tailWord_1205567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205567).length < 2 ^ (prefixWord ++ tailWord_1205567).sum := by decide
  have hdescent : baseEnd_1205567 < baseStart_1205567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205578 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1205578 : Nat := 118140960795 + 1205578 * 2 ^ 59
def prefixEnd_1205578 : Nat := 4983230072969 + 3 ^ 40 * 1205578 * 2
def baseEnd_1205578 : Nat := 412693986990792936153769

theorem tailTrace_1205578 : CollatzResearch.WordTrace tailWord_1205578 prefixEnd_1205578 412693986990792936153769 := by
  unfold tailWord_1205578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992760506601069293816347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29314028017602851450176925 10992760506601069293816347)
  ·
    refine ⟨16489140759901603940724521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992760506601069293816347 16489140759901603940724521)
    ·
      refine ⟨12366855569926202955543391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16489140759901603940724521 12366855569926202955543391)
      ·
        refine ⟨18550283354889304433315087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366855569926202955543391 18550283354889304433315087)
        ·
          refine ⟨27825425032333956649972631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18550283354889304433315087 27825425032333956649972631)
          ·
            refine ⟨41738137548500934974958947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27825425032333956649972631 41738137548500934974958947)
            ·
              refine ⟨62607206322751402462438421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41738137548500934974958947 62607206322751402462438421)
              ·
                refine ⟨2934712796378971990426801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62607206322751402462438421 2934712796378971990426801)
                ·
                  refine ⟨2201034597284228992820101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934712796378971990426801 2201034597284228992820101)
                  ·
                    refine ⟨412693986990792936153769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201034597284228992820101 412693986990792936153769)
                    ·
                      rfl

theorem cell22_1205578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1205578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205578 prefixEnd_1205578 := by exact prefixLift 1205578
  have htrace : WordTrace (prefixWord ++ tailWord_1205578) baseStart_1205578 baseEnd_1205578 := by
    simpa [prefixWord, tailWord_1205578, baseEnd_1205578] using wordTrace_append hprefix tailTrace_1205578
  have hstable : (prefixWord ++ tailWord_1205578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205578).length < 2 ^ (prefixWord ++ tailWord_1205578).sum := by decide
  have hdescent : baseEnd_1205578 < baseStart_1205578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205580 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_1205580 : Nat := 118140960795 + 1205580 * 2 ^ 59
def prefixEnd_1205580 : Nat := 4983230072969 + 3 ^ 40 * 1205580 * 2
def baseEnd_1205580 : Nat := 412694671631665597603763

theorem tailTrace_1205580 : CollatzResearch.WordTrace tailWord_1205580 prefixEnd_1205580 412694671631665597603763 := by
  unfold tailWord_1205580
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985557486198515758419097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29314076648264687677892129 21985557486198515758419097)
  ·
    refine ⟨16489168114648886818814323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21985557486198515758419097 16489168114648886818814323)
    ·
      refine ⟨24733752171973330228221485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16489168114648886818814323 24733752171973330228221485)
      ·
        refine ⟨9275157064489998835583057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24733752171973330228221485 9275157064489998835583057)
        ·
          refine ⟨6956367798367499126687293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9275157064489998835583057 6956367798367499126687293)
          ·
            refine ⟨2608637924387812172507735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6956367798367499126687293 2608637924387812172507735)
            ·
              refine ⟨3912956886581718258761603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608637924387812172507735 3912956886581718258761603)
              ·
                refine ⟨5869435329872577388142405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912956886581718258761603 5869435329872577388142405)
                ·
                  refine ⟨1100519124351108260276701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5869435329872577388142405 1100519124351108260276701)
                  ·
                    refine ⟨412694671631665597603763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100519124351108260276701 412694671631665597603763)
                    ·
                      rfl

theorem cell22_1205580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_1205580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205580 prefixEnd_1205580 := by exact prefixLift 1205580
  have htrace : WordTrace (prefixWord ++ tailWord_1205580) baseStart_1205580 baseEnd_1205580 := by
    simpa [prefixWord, tailWord_1205580, baseEnd_1205580] using wordTrace_append hprefix tailTrace_1205580
  have hstable : (prefixWord ++ tailWord_1205580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205580).length < 2 ^ (prefixWord ++ tailWord_1205580).sum := by decide
  have hdescent : baseEnd_1205580 < baseStart_1205580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205610 : List Nat := [3, 1, 3, 3, 2, 1, 1, 8]
def baseStart_1205610 : Nat := 118140960795 + 1205610 * 2 ^ 59
def prefixEnd_1205610 : Nat := 4983230072969 + 3 ^ 40 * 1205610 * 2
def baseEnd_1205610 : Nat := 45856104582750613261519

theorem tailTrace_1205610 : CollatzResearch.WordTrace tailWord_1205610 prefixEnd_1205610 45856104582750613261519 := by
  unfold tailWord_1205610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993052290572086660107571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29314806108192231093620189 10993052290572086660107571)
  ·
    refine ⟨16489578435858129990161357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10993052290572086660107571 16489578435858129990161357)
    ·
      refine ⟨6183591913446798746310509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16489578435858129990161357 6183591913446798746310509)
      ·
        refine ⟨2318846967542549529866441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6183591913446798746310509 2318846967542549529866441)
        ·
          refine ⟨1739135225656912147399831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2318846967542549529866441 1739135225656912147399831)
          ·
            refine ⟨2608702838485368221099747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739135225656912147399831 2608702838485368221099747)
            ·
              refine ⟨3913054257728052331649621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608702838485368221099747 3913054257728052331649621)
              ·
                refine ⟨45856104582750613261519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3913054257728052331649621 45856104582750613261519)
                ·
                  rfl

theorem cell22_1205610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_1205610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205610 prefixEnd_1205610 := by exact prefixLift 1205610
  have htrace : WordTrace (prefixWord ++ tailWord_1205610) baseStart_1205610 baseEnd_1205610 := by
    simpa [prefixWord, tailWord_1205610, baseEnd_1205610] using wordTrace_append hprefix tailTrace_1205610
  have hstable : (prefixWord ++ tailWord_1205610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205610).length < 2 ^ (prefixWord ++ tailWord_1205610).sum := by decide
  have hdescent : baseEnd_1205610 < baseStart_1205610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205653 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1205653 : Nat := 118140960795 + 1205653 * 2 ^ 59
def prefixEnd_1205653 : Nat := 4983230072969 + 3 ^ 40 * 1205653 * 2
def baseEnd_1205653 : Nat := 412719661023517740528539

theorem tailTrace_1205653 : CollatzResearch.WordTrace tailWord_1205653 prefixEnd_1205653 412719661023517740528539 := by
  unfold tailWord_1205653
  simp only [CollatzResearch.WordTrace]
  refine ⟨43973777501132564984245613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29315851667421709989497075 43973777501132564984245613)
  ·
    refine ⟨16490166562924711869092105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43973777501132564984245613 16490166562924711869092105)
    ·
      refine ⟨12367624922193533901819079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16490166562924711869092105 12367624922193533901819079)
      ·
        refine ⟨18551437383290300852728619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12367624922193533901819079 18551437383290300852728619)
        ·
          refine ⟨27827156074935451279092929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18551437383290300852728619 27827156074935451279092929)
          ·
            refine ⟨20870367056201588459319697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27827156074935451279092929 20870367056201588459319697)
            ·
              refine ⟨15652775292151191344489773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20870367056201588459319697 15652775292151191344489773)
              ·
                refine ⟨5869790734556696754183665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15652775292151191344489773 5869790734556696754183665)
                ·
                  refine ⟨4402343050917522565637749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869790734556696754183665 4402343050917522565637749)
                  ·
                    refine ⟨412719661023517740528539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4402343050917522565637749 412719661023517740528539)
                    ·
                      rfl

theorem cell22_1205653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1205653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205653 prefixEnd_1205653 := by exact prefixLift 1205653
  have htrace : WordTrace (prefixWord ++ tailWord_1205653) baseStart_1205653 baseEnd_1205653 := by
    simpa [prefixWord, tailWord_1205653, baseEnd_1205653] using wordTrace_append hprefix tailTrace_1205653
  have hstable : (prefixWord ++ tailWord_1205653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205653).length < 2 ^ (prefixWord ++ tailWord_1205653).sum := by decide
  have hdescent : baseEnd_1205653 < baseStart_1205653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205749 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1205749 : Nat := 118140960795 + 1205749 * 2 ^ 59
def prefixEnd_1205749 : Nat := 4983230072969 + 3 ^ 40 * 1205749 * 2
def baseEnd_1205749 : Nat := 412752523785405490128245

theorem tailTrace_1205749 : CollatzResearch.WordTrace tailWord_1205749 prefixEnd_1205749 412752523785405490128245 := by
  unfold tailWord_1205749
  simp only [CollatzResearch.WordTrace]
  refine ⟨43977278908784773379740301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29318185939189848919826867 43977278908784773379740301)
  ·
    refine ⟨16491479590794290017402613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43977278908784773379740301 16491479590794290017402613)
    ·
      refine ⟨1546076211636964689131495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16491479590794290017402613 1546076211636964689131495)
      ·
        refine ⟨2319114317455447033697243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546076211636964689131495 2319114317455447033697243)
        ·
          refine ⟨3478671476183170550545865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319114317455447033697243 3478671476183170550545865)
          ·
            refine ⟨2609003607137377912909399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478671476183170550545865 2609003607137377912909399)
            ·
              refine ⟨3913505410706066869364099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609003607137377912909399 3913505410706066869364099)
              ·
                refine ⟨5870258116059100304046149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913505410706066869364099 5870258116059100304046149)
                ·
                  refine ⟨1100673396761081307008653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5870258116059100304046149 1100673396761081307008653)
                  ·
                    refine ⟨412752523785405490128245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100673396761081307008653 412752523785405490128245)
                    ·
                      rfl

theorem cell22_1205749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1205749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205749 prefixEnd_1205749 := by exact prefixLift 1205749
  have htrace : WordTrace (prefixWord ++ tailWord_1205749) baseStart_1205749 baseEnd_1205749 := by
    simpa [prefixWord, tailWord_1205749, baseEnd_1205749] using wordTrace_append hprefix tailTrace_1205749
  have hstable : (prefixWord ++ tailWord_1205749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205749).length < 2 ^ (prefixWord ++ tailWord_1205749).sum := by decide
  have hdescent : baseEnd_1205749 < baseStart_1205749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205811 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 1, 3]
def baseStart_1205811 : Nat := 118140960795 + 1205811 * 2 ^ 59
def prefixEnd_1205811 : Nat := 4983230072969 + 3 ^ 40 * 1205811 * 2
def baseEnd_1205811 : Nat := 412773747652457995078055

theorem tailTrace_1205811 : CollatzResearch.WordTrace tailWord_1205811 prefixEnd_1205811 412773747652457995078055 := by
  unfold tailWord_1205811
  simp only [CollatzResearch.WordTrace]
  refine ⟨43979540234560157968497287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29319693489706771978998191 43979540234560157968497287)
  ·
    refine ⟨65969310351840236952745931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43979540234560157968497287 65969310351840236952745931)
    ·
      refine ⟨98953965527760355429118897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65969310351840236952745931 98953965527760355429118897)
      ·
        refine ⟨74215474145820266571839173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98953965527760355429118897 74215474145820266571839173)
        ·
          refine ⟨13915401402341299982219845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74215474145820266571839173 13915401402341299982219845)
          ·
            refine ⟨2609137762938993746666221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13915401402341299982219845 2609137762938993746666221)
            ·
              refine ⟨978426661102122654999833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2609137762938993746666221 978426661102122654999833)
              ·
                refine ⟨733819995826591991249875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978426661102122654999833 733819995826591991249875)
                ·
                  refine ⟨1100729993739887986874813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733819995826591991249875 1100729993739887986874813)
                  ·
                    refine ⟨412773747652457995078055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100729993739887986874813 412773747652457995078055)
                    ·
                      rfl

theorem cell22_1205811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 3].length) (baseStart_1205811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205811 prefixEnd_1205811 := by exact prefixLift 1205811
  have htrace : WordTrace (prefixWord ++ tailWord_1205811) baseStart_1205811 baseEnd_1205811 := by
    simpa [prefixWord, tailWord_1205811, baseEnd_1205811] using wordTrace_append hprefix tailTrace_1205811
  have hstable : (prefixWord ++ tailWord_1205811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205811).length < 2 ^ (prefixWord ++ tailWord_1205811).sum := by decide
  have hdescent : baseEnd_1205811 < baseStart_1205811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205918 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1205918 : Nat := 118140960795 + 1205918 * 2 ^ 59
def prefixEnd_1205918 : Nat := 4983230072969 + 3 ^ 40 * 1205918 * 2
def baseEnd_1205918 : Nat := 412810375939145382652727

theorem tailTrace_1205918 : CollatzResearch.WordTrace tailWord_1205918 prefixEnd_1205918 412810375939145382652727 := by
  unfold tailWord_1205918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497930355646564405330301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29322295230115010161761605 5497930355646564405330301)
  ·
    refine ⟨2061723883367461651998863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5497930355646564405330301 2061723883367461651998863)
    ·
      refine ⟨3092585825051192477998295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061723883367461651998863 3092585825051192477998295)
      ·
        refine ⟨4638878737576788716997443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3092585825051192477998295 4638878737576788716997443)
        ·
          refine ⟨6958318106365183075496165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638878737576788716997443 6958318106365183075496165)
          ·
            refine ⟨1304684644943471826655531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6958318106365183075496165 1304684644943471826655531)
            ·
              refine ⟨1957026967415207739983297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304684644943471826655531 1957026967415207739983297)
              ·
                refine ⟨1467770225561405804987473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957026967415207739983297 1467770225561405804987473)
                ·
                  refine ⟨1100827669171054353740605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467770225561405804987473 1100827669171054353740605)
                  ·
                    refine ⟨412810375939145382652727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100827669171054353740605 412810375939145382652727)
                    ·
                      rfl

theorem cell22_1205918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1205918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205918 prefixEnd_1205918 := by exact prefixLift 1205918
  have htrace : WordTrace (prefixWord ++ tailWord_1205918) baseStart_1205918 baseEnd_1205918 := by
    simpa [prefixWord, tailWord_1205918, baseEnd_1205918] using wordTrace_append hprefix tailTrace_1205918
  have hstable : (prefixWord ++ tailWord_1205918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205918).length < 2 ^ (prefixWord ++ tailWord_1205918).sum := by decide
  have hdescent : baseEnd_1205918 < baseStart_1205918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205955 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_1205955 : Nat := 118140960795 + 1205955 * 2 ^ 59
def prefixEnd_1205955 : Nat := 4983230072969 + 3 ^ 40 * 1205955 * 2
def baseEnd_1205955 : Nat := 412823041795289619477613

theorem tailTrace_1205955 : CollatzResearch.WordTrace tailWord_1205955 prefixEnd_1205955 412823041795289619477613 := by
  unfold tailWord_1205955
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984792346038470561739319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29323194897358980374492879 43984792346038470561739319)
  ·
    refine ⟨65977188519057705842608979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43984792346038470561739319 65977188519057705842608979)
    ·
      refine ⟨98965782778586558763913469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65977188519057705842608979 98965782778586558763913469)
      ·
        refine ⟨37112168541969959536467551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98965782778586558763913469 37112168541969959536467551)
        ·
          refine ⟨55668252812954939304701327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37112168541969959536467551 55668252812954939304701327)
          ·
            refine ⟨83502379219432408957051991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55668252812954939304701327 83502379219432408957051991)
            ·
              refine ⟨125253568829148613435577987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83502379219432408957051991 125253568829148613435577987)
              ·
                refine ⟨187880353243722920153366981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125253568829148613435577987 187880353243722920153366981)
                ·
                  refine ⟨35227566233198047528756309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187880353243722920153366981 35227566233198047528756309)
                  ·
                    refine ⟨412823041795289619477613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35227566233198047528756309 412823041795289619477613)
                    ·
                      rfl

theorem cell22_1205955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_1205955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205955 prefixEnd_1205955 := by exact prefixLift 1205955
  have htrace : WordTrace (prefixWord ++ tailWord_1205955) baseStart_1205955 baseEnd_1205955 := by
    simpa [prefixWord, tailWord_1205955, baseEnd_1205955] using wordTrace_append hprefix tailTrace_1205955
  have hstable : (prefixWord ++ tailWord_1205955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205955).length < 2 ^ (prefixWord ++ tailWord_1205955).sum := by decide
  have hdescent : baseEnd_1205955 < baseStart_1205955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205980 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1205980 : Nat := 118140960795 + 1205980 * 2 ^ 59
def prefixEnd_1205980 : Nat := 4983230072969 + 3 ^ 40 * 1205980 * 2
def baseEnd_1205980 : Nat := 412831599806197887602537

theorem tailTrace_1205980 : CollatzResearch.WordTrace tailWord_1205980 prefixEnd_1205980 412831599806197887602537 := by
  unfold tailWord_1205980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21992852085473949915699697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29323802780631933220932929 21992852085473949915699697)
  ·
    refine ⟨16494639064105462436774773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21992852085473949915699697 16494639064105462436774773)
    ·
      refine ⟨1546372412259887103447635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16494639064105462436774773 1546372412259887103447635)
      ·
        refine ⟨2319558618389830655171453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546372412259887103447635 2319558618389830655171453)
        ·
          refine ⟨869834481896186495689295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2319558618389830655171453 869834481896186495689295)
          ·
            refine ⟨1304751722844279743533943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869834481896186495689295 1304751722844279743533943)
            ·
              refine ⟨1957127584266419615300915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304751722844279743533943 1957127584266419615300915)
              ·
                refine ⟨2935691376399629422951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957127584266419615300915 2935691376399629422951373)
                ·
                  refine ⟨1100884266149861033606765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2935691376399629422951373 1100884266149861033606765)
                  ·
                    refine ⟨412831599806197887602537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100884266149861033606765 412831599806197887602537)
                    ·
                      rfl

theorem cell22_1205980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1205980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1205980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1205980 prefixEnd_1205980 := by exact prefixLift 1205980
  have htrace : WordTrace (prefixWord ++ tailWord_1205980) baseStart_1205980 baseEnd_1205980 := by
    simpa [prefixWord, tailWord_1205980, baseEnd_1205980] using wordTrace_append hprefix tailTrace_1205980
  have hstable : (prefixWord ++ tailWord_1205980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205980).length < 2 ^ (prefixWord ++ tailWord_1205980).sum := by decide
  have hdescent : baseEnd_1205980 < baseStart_1205980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206006 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1206006 : Nat := 118140960795 + 1206006 * 2 ^ 59
def prefixEnd_1206006 : Nat := 4983230072969 + 3 ^ 40 * 1206006 * 2
def baseEnd_1206006 : Nat := 412840500137542486452457

theorem tailTrace_1206006 : CollatzResearch.WordTrace tailWord_1206006 prefixEnd_1206006 412840500137542486452457 := by
  unfold tailWord_1206006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749165779303356641990367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29324434979235804181230581 2749165779303356641990367)
  ·
    refine ⟨4123748668955034962985551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2749165779303356641990367 4123748668955034962985551)
    ·
      refine ⟨6185623003432552444478327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123748668955034962985551 6185623003432552444478327)
      ·
        refine ⟨9278434505148828666717491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185623003432552444478327 9278434505148828666717491)
        ·
          refine ⟨13917651757723243000076237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9278434505148828666717491 13917651757723243000076237)
          ·
            refine ⟨5219119409146216125028589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13917651757723243000076237 5219119409146216125028589)
            ·
              refine ⟨1957169778429831046885721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5219119409146216125028589 1957169778429831046885721)
              ·
                refine ⟨1467877333822373285164291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957169778429831046885721 1467877333822373285164291)
                ·
                  refine ⟨2201816000733559927746437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467877333822373285164291 2201816000733559927746437)
                  ·
                    refine ⟨412840500137542486452457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201816000733559927746437 412840500137542486452457)
                    ·
                      rfl

theorem cell22_1206006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1206006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206006 prefixEnd_1206006 := by exact prefixLift 1206006
  have htrace : WordTrace (prefixWord ++ tailWord_1206006) baseStart_1206006 baseEnd_1206006 := by
    simpa [prefixWord, tailWord_1206006, baseEnd_1206006] using wordTrace_append hprefix tailTrace_1206006
  have hstable : (prefixWord ++ tailWord_1206006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206006).length < 2 ^ (prefixWord ++ tailWord_1206006).sum := by decide
  have hdescent : baseEnd_1206006 < baseStart_1206006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206017 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1206017 : Nat := 118140960795 + 1206017 * 2 ^ 59
def prefixEnd_1206017 : Nat := 4983230072969 + 3 ^ 40 * 1206017 * 2
def baseEnd_1206017 : Nat := 412844265662342124427423

theorem tailTrace_1206017 : CollatzResearch.WordTrace tailWord_1206017 prefixEnd_1206017 412844265662342124427423 := by
  unfold tailWord_1206017
  simp only [CollatzResearch.WordTrace]
  refine ⟨43987053671813855150496305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29324702447875903433664203 43987053671813855150496305)
  ·
    refine ⟨32990290253860391362872229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43987053671813855150496305 32990290253860391362872229)
    ·
      refine ⟨6185679422598823380538543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32990290253860391362872229 6185679422598823380538543)
      ·
        refine ⟨9278519133898235070807815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185679422598823380538543 9278519133898235070807815)
        ·
          refine ⟨13917778700847352606211723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9278519133898235070807815 13917778700847352606211723)
          ·
            refine ⟨20876668051271028909317585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13917778700847352606211723 20876668051271028909317585)
            ·
              refine ⟨15657501038453271681988189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20876668051271028909317585 15657501038453271681988189)
              ·
                refine ⟨5871562889419976880745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15657501038453271681988189 5871562889419976880745571)
                ·
                  refine ⟨8807344334129965321118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871562889419976880745571 8807344334129965321118357)
                  ·
                    refine ⟨412844265662342124427423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8807344334129965321118357 412844265662342124427423)
                    ·
                      rfl

theorem cell22_1206017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1206017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206017 prefixEnd_1206017 := by exact prefixLift 1206017
  have htrace : WordTrace (prefixWord ++ tailWord_1206017) baseStart_1206017 baseEnd_1206017 := by
    simpa [prefixWord, tailWord_1206017, baseEnd_1206017] using wordTrace_append hprefix tailTrace_1206017
  have hstable : (prefixWord ++ tailWord_1206017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206017).length < 2 ^ (prefixWord ++ tailWord_1206017).sum := by decide
  have hdescent : baseEnd_1206017 < baseStart_1206017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206023 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1206023 : Nat := 118140960795 + 1206023 * 2 ^ 59
def prefixEnd_1206023 : Nat := 4983230072969 + 3 ^ 40 * 1206023 * 2
def baseEnd_1206023 : Nat := 412846319584960108777405

theorem tailTrace_1206023 : CollatzResearch.WordTrace tailWord_1206023 prefixEnd_1206023 412846319584960108777405 := by
  unfold tailWord_1206023
  simp only [CollatzResearch.WordTrace]
  refine ⟨43987272509792118175214723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29324848339861412116809815 43987272509792118175214723)
  ·
    refine ⟨65980908764688177262822085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43987272509792118175214723 65980908764688177262822085)
    ·
      refine ⟨12371420393379033236779141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65980908764688177262822085 12371420393379033236779141)
      ·
        refine ⟨2319641323758568731896089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12371420393379033236779141 2319641323758568731896089)
        ·
          refine ⟨1739730992818926548922067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319641323758568731896089 1739730992818926548922067)
          ·
            refine ⟨2609596489228389823383101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739730992818926548922067 2609596489228389823383101)
            ·
              refine ⟨978598683460646183768663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2609596489228389823383101 978598683460646183768663)
              ·
                refine ⟨1467898025190969275652995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978598683460646183768663 1467898025190969275652995)
                ·
                  refine ⟨2201847037786453913479493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467898025190969275652995 2201847037786453913479493)
                  ·
                    refine ⟨412846319584960108777405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201847037786453913479493 412846319584960108777405)
                    ·
                      rfl

theorem cell22_1206023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1206023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206023 prefixEnd_1206023 := by exact prefixLift 1206023
  have htrace : WordTrace (prefixWord ++ tailWord_1206023) baseStart_1206023 baseEnd_1206023 := by
    simpa [prefixWord, tailWord_1206023, baseEnd_1206023] using wordTrace_append hprefix tailTrace_1206023
  have hstable : (prefixWord ++ tailWord_1206023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206023).length < 2 ^ (prefixWord ++ tailWord_1206023).sum := by decide
  have hdescent : baseEnd_1206023 < baseStart_1206023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206049 : List Nat := [1, 2, 3, 2, 1, 5, 1, 7]
def baseStart_1206049 : Nat := 118140960795 + 1206049 * 2 ^ 59
def prefixEnd_1206049 : Nat := 4983230072969 + 3 ^ 40 * 1206049 * 2
def baseEnd_1206049 : Nat := 45872802212922745291925

theorem tailTrace_1206049 : CollatzResearch.WordTrace tailWord_1206049 prefixEnd_1206049 45872802212922745291925 := by
  unfold tailWord_1206049
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988220807697924615661201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29325480538465283077107467 43988220807697924615661201)
  ·
    refine ⟨32991165605773443461745901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43988220807697924615661201 32991165605773443461745901)
    ·
      refine ⟨12371687102165041298154713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32991165605773443461745901 12371687102165041298154713)
      ·
        refine ⟨9278765326623780973616035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12371687102165041298154713 9278765326623780973616035)
        ·
          refine ⟨13918147989935671460424053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9278765326623780973616035 13918147989935671460424053)
          ·
            refine ⟨1304826374056469199414755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13918147989935671460424053 1304826374056469199414755)
            ·
              refine ⟨1957239561084703799122133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304826374056469199414755 1957239561084703799122133)
              ·
                refine ⟨45872802212922745291925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1957239561084703799122133 45872802212922745291925)
                ·
                  rfl

theorem cell22_1206049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 7].length) (baseStart_1206049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206049 prefixEnd_1206049 := by exact prefixLift 1206049
  have htrace : WordTrace (prefixWord ++ tailWord_1206049) baseStart_1206049 baseEnd_1206049 := by
    simpa [prefixWord, tailWord_1206049, baseEnd_1206049] using wordTrace_append hprefix tailTrace_1206049
  have hstable : (prefixWord ++ tailWord_1206049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206049).length < 2 ^ (prefixWord ++ tailWord_1206049).sum := by decide
  have hdescent : baseEnd_1206049 < baseStart_1206049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206068 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1206068 : Nat := 118140960795 + 1206068 * 2 ^ 59
def prefixEnd_1206068 : Nat := 4983230072969 + 3 ^ 40 * 1206068 * 2
def baseEnd_1206068 : Nat := 412861724004594991402267

theorem tailTrace_1206068 : CollatzResearch.WordTrace tailWord_1206068 prefixEnd_1206068 412861724004594991402267 := by
  unfold tailWord_1206068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21994456897314545430301429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29325942529752727240401905 21994456897314545430301429)
  ·
    refine ⟨2061980334123238634090759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21994456897314545430301429 2061980334123238634090759)
    ·
      refine ⟨3092970501184857951136139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061980334123238634090759 3092970501184857951136139)
      ·
        refine ⟨4639455751777286926704209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3092970501184857951136139 4639455751777286926704209)
        ·
          refine ⟨3479591813832965195028157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4639455751777286926704209 3479591813832965195028157)
          ·
            refine ⟨1304846930187361948135559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3479591813832965195028157 1304846930187361948135559)
            ·
              refine ⟨1957270395281042922203339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304846930187361948135559 1957270395281042922203339)
              ·
                refine ⟨2935905592921564383305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957270395281042922203339 2935905592921564383305009)
                ·
                  refine ⟨2201929194691173287478757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935905592921564383305009 2201929194691173287478757)
                  ·
                    refine ⟨412861724004594991402267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201929194691173287478757 412861724004594991402267)
                    ·
                      rfl

theorem cell22_1206068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1206068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206068 prefixEnd_1206068 := by exact prefixLift 1206068
  have htrace : WordTrace (prefixWord ++ tailWord_1206068) baseStart_1206068 baseEnd_1206068 := by
    simpa [prefixWord, tailWord_1206068, baseEnd_1206068] using wordTrace_append hprefix tailTrace_1206068
  have hstable : (prefixWord ++ tailWord_1206068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206068).length < 2 ^ (prefixWord ++ tailWord_1206068).sum := by decide
  have hdescent : baseEnd_1206068 < baseStart_1206068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206098 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_1206098 : Nat := 118140960795 + 1206098 * 2 ^ 59
def prefixEnd_1206098 : Nat := 4983230072969 + 3 ^ 40 * 1206098 * 2
def baseEnd_1206098 : Nat := 412871993617684913152175

theorem tailTrace_1206098 : CollatzResearch.WordTrace tailWord_1206098 prefixEnd_1206098 412871993617684913152175 := by
  unfold tailWord_1206098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10997501996130101496048737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29326671989680270656129965 10997501996130101496048737)
  ·
    refine ⟨8248126497097576122036553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10997501996130101496048737 8248126497097576122036553)
    ·
      refine ⟨6186094872823182091527415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8248126497097576122036553 6186094872823182091527415)
      ·
        refine ⟨9279142309234773137291123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6186094872823182091527415 9279142309234773137291123)
        ·
          refine ⟨13918713463852159705936685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9279142309234773137291123 13918713463852159705936685)
          ·
            refine ⟨5219517548944559889726257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13918713463852159705936685 5219517548944559889726257)
            ·
              refine ⟨3914638161708419917294693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5219517548944559889726257 3914638161708419917294693)
              ·
                refine ⟨733994655320328734492755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3914638161708419917294693 733994655320328734492755)
                ·
                  refine ⟨1100991982980493101739133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733994655320328734492755 1100991982980493101739133)
                  ·
                    refine ⟨412871993617684913152175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100991982980493101739133 412871993617684913152175)
                    ·
                      rfl

theorem cell22_1206098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_1206098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206098 prefixEnd_1206098 := by exact prefixLift 1206098
  have htrace : WordTrace (prefixWord ++ tailWord_1206098) baseStart_1206098 baseEnd_1206098 := by
    simpa [prefixWord, tailWord_1206098, baseEnd_1206098] using wordTrace_append hprefix tailTrace_1206098
  have hstable : (prefixWord ++ tailWord_1206098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206098).length < 2 ^ (prefixWord ++ tailWord_1206098).sum := by decide
  have hdescent : baseEnd_1206098 < baseStart_1206098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206111 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 5]
def baseStart_1206111 : Nat := 118140960795 + 1206111 * 2 ^ 59
def prefixEnd_1206111 : Nat := 4983230072969 + 3 ^ 40 * 1206111 * 2
def baseEnd_1206111 : Nat := 137625481261119070859045

theorem tailTrace_1206111 : CollatzResearch.WordTrace tailWord_1206111 prefixEnd_1206111 137625481261119070859045 := by
  unfold tailWord_1206111
  simp only [CollatzResearch.WordTrace]
  refine ⟨43990482133473309204418187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29326988088982206136278791 43990482133473309204418187)
  ·
    refine ⟨65985723200209963806627281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43990482133473309204418187 65985723200209963806627281)
    ·
      refine ⟨49489292400157472854970461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65985723200209963806627281 49489292400157472854970461)
      ·
        refine ⟨18558484650059052320613923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49489292400157472854970461 18558484650059052320613923)
        ·
          refine ⟨27837726975088578480920885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18558484650059052320613923 27837726975088578480920885)
          ·
            refine ⟨2609786903914554232586333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27837726975088578480920885 2609786903914554232586333)
            ·
              refine ⟨978670088967957837219875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2609786903914554232586333 978670088967957837219875)
              ·
                refine ⟨1468005133451936755829813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978670088967957837219875 1468005133451936755829813)
                ·
                  refine ⟨137625481261119070859045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468005133451936755829813 137625481261119070859045)
                  ·
                    rfl

theorem cell22_1206111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 5].length) (baseStart_1206111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206111 prefixEnd_1206111 := by exact prefixLift 1206111
  have htrace : WordTrace (prefixWord ++ tailWord_1206111) baseStart_1206111 baseEnd_1206111 := by
    simpa [prefixWord, tailWord_1206111, baseEnd_1206111] using wordTrace_append hprefix tailTrace_1206111
  have hstable : (prefixWord ++ tailWord_1206111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206111).length < 2 ^ (prefixWord ++ tailWord_1206111).sum := by decide
  have hdescent : baseEnd_1206111 < baseStart_1206111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206175 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 1, 4]
def baseStart_1206175 : Nat := 118140960795 + 1206175 * 2 ^ 59
def prefixEnd_1206175 : Nat := 4983230072969 + 3 ^ 40 * 1206175 * 2
def baseEnd_1206175 : Nat := 412898352291282378976939

theorem tailTrace_1206175 : CollatzResearch.WordTrace tailWord_1206175 prefixEnd_1206175 412898352291282378976939 := by
  unfold tailWord_1206175
  simp only [CollatzResearch.WordTrace]
  refine ⟨43992816405241448134747979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29328544270160965423165319 43992816405241448134747979)
  ·
    refine ⟨65989224607862172202121969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43992816405241448134747979 65989224607862172202121969)
    ·
      refine ⟨49491918455896629151591477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65989224607862172202121969 49491918455896629151591477)
      ·
        refine ⟨4639867355240308982961701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49491918455896629151591477 4639867355240308982961701)
        ·
          refine ⟨869975129107557934305319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4639867355240308982961701 869975129107557934305319)
          ·
            refine ⟨1304962693661336901457979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869975129107557934305319 1304962693661336901457979)
            ·
              refine ⟨1957444040492005352186969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304962693661336901457979 1957444040492005352186969)
              ·
                refine ⟨1468083030369004014140227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957444040492005352186969 1468083030369004014140227)
                ·
                  refine ⟨2202124545553506021210341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468083030369004014140227 2202124545553506021210341)
                  ·
                    refine ⟨412898352291282378976939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202124545553506021210341 412898352291282378976939)
                    ·
                      rfl

theorem cell22_1206175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_1206175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206175 prefixEnd_1206175 := by exact prefixLift 1206175
  have htrace : WordTrace (prefixWord ++ tailWord_1206175) baseStart_1206175 baseEnd_1206175 := by
    simpa [prefixWord, tailWord_1206175, baseEnd_1206175] using wordTrace_append hprefix tailTrace_1206175
  have hstable : (prefixWord ++ tailWord_1206175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206175).length < 2 ^ (prefixWord ++ tailWord_1206175).sum := by decide
  have hdescent : baseEnd_1206175 < baseStart_1206175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206233 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_1206233 : Nat := 118140960795 + 1206233 * 2 ^ 59
def prefixEnd_1206233 : Nat := 4983230072969 + 3 ^ 40 * 1206233 * 2
def baseEnd_1206233 : Nat := 412918206876589561026761

theorem tailTrace_1206233 : CollatzResearch.WordTrace tailWord_1206233 prefixEnd_1206233 412918206876589561026761 := by
  unfold tailWord_1206233
  simp only [CollatzResearch.WordTrace]
  refine ⟨43994931839031324040359353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29329954559354216026906235 43994931839031324040359353)
  ·
    refine ⟨32996198879273493030269515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43994931839031324040359353 32996198879273493030269515)
    ·
      refine ⟨49494298318910239545404273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32996198879273493030269515 49494298318910239545404273)
      ·
        refine ⟨37120723739182679659053205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49494298318910239545404273 37120723739182679659053205)
        ·
          refine ⟨1740033925274188109018119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37120723739182679659053205 1740033925274188109018119)
          ·
            refine ⟨2610050887911282163527179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740033925274188109018119 2610050887911282163527179)
            ·
              refine ⟨3915076331866923245290769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610050887911282163527179 3915076331866923245290769)
              ·
                refine ⟨2936307248900192433968077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915076331866923245290769 2936307248900192433968077)
                ·
                  refine ⟨1101115218337572162738029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2936307248900192433968077 1101115218337572162738029)
                  ·
                    refine ⟨412918206876589561026761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101115218337572162738029 412918206876589561026761)
                    ·
                      rfl

theorem cell22_1206233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_1206233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206233 prefixEnd_1206233 := by exact prefixLift 1206233
  have htrace : WordTrace (prefixWord ++ tailWord_1206233) baseStart_1206233 baseEnd_1206233 := by
    simpa [prefixWord, tailWord_1206233, baseEnd_1206233] using wordTrace_append hprefix tailTrace_1206233
  have hstable : (prefixWord ++ tailWord_1206233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206233).length < 2 ^ (prefixWord ++ tailWord_1206233).sum := by decide
  have hdescent : baseEnd_1206233 < baseStart_1206233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206244 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1206244 : Nat := 118140960795 + 1206244 * 2 ^ 59
def prefixEnd_1206244 : Nat := 4983230072969 + 3 ^ 40 * 1206244 * 2
def baseEnd_1206244 : Nat := 412921972401389199001727

theorem tailTrace_1206244 : CollatzResearch.WordTrace tailWord_1206244 prefixEnd_1206244 412921972401389199001727 := by
  unfold tailWord_1206244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997666520995736459504893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29330222027994315279339857 21997666520995736459504893)
  ·
    refine ⟨8249124945373401172314335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21997666520995736459504893 8249124945373401172314335)
    ·
      refine ⟨12373687418060101758471503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8249124945373401172314335 12373687418060101758471503)
      ·
        refine ⟨18560531127090152637707255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12373687418060101758471503 18560531127090152637707255)
        ·
          refine ⟨27840796690635228956560883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18560531127090152637707255 27840796690635228956560883)
          ·
            refine ⟨41761195035952843434841325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27840796690635228956560883 41761195035952843434841325)
            ·
              refine ⟨15660448138482316288065497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41761195035952843434841325 15660448138482316288065497)
              ·
                refine ⟨11745336103861737216049123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15660448138482316288065497 11745336103861737216049123)
                ·
                  refine ⟨17618004155792605824073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11745336103861737216049123 17618004155792605824073685)
                  ·
                    refine ⟨412921972401389199001727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17618004155792605824073685 412921972401389199001727)
                    ·
                      rfl

theorem cell22_1206244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1206244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206244 prefixEnd_1206244 := by exact prefixLift 1206244
  have htrace : WordTrace (prefixWord ++ tailWord_1206244) baseStart_1206244 baseEnd_1206244 := by
    simpa [prefixWord, tailWord_1206244, baseEnd_1206244] using wordTrace_append hprefix tailTrace_1206244
  have hstable : (prefixWord ++ tailWord_1206244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206244).length < 2 ^ (prefixWord ++ tailWord_1206244).sum := by decide
  have hdescent : baseEnd_1206244 < baseStart_1206244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206250 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1206250 : Nat := 118140960795 + 1206250 * 2 ^ 59
def prefixEnd_1206250 : Nat := 4983230072969 + 3 ^ 40 * 1206250 * 2
def baseEnd_1206250 : Nat := 412924026324007183351709

theorem tailTrace_1206250 : CollatzResearch.WordTrace tailWord_1206250 prefixEnd_1206250 412924026324007183351709 := by
  unfold tailWord_1206250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10998887969992433985932051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29330367919979823962485469 10998887969992433985932051)
  ·
    refine ⟨16498331954988650978898077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10998887969992433985932051 16498331954988650978898077)
    ·
      refine ⟨6186874483120744117086779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16498331954988650978898077 6186874483120744117086779)
      ·
        refine ⟨9280311724681116175630169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6186874483120744117086779 9280311724681116175630169)
        ·
          refine ⟨6960233793510837131722627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9280311724681116175630169 6960233793510837131722627)
          ·
            refine ⟨10440350690266255697583941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6960233793510837131722627 10440350690266255697583941)
            ·
              refine ⟨1957565754424922943296989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10440350690266255697583941 1957565754424922943296989)
              ·
                refine ⟨734087157909346103736371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1957565754424922943296989 734087157909346103736371)
                ·
                  refine ⟨1101130736864019155604557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734087157909346103736371 1101130736864019155604557)
                  ·
                    refine ⟨412924026324007183351709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101130736864019155604557 412924026324007183351709)
                    ·
                      rfl

theorem cell22_1206250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1206250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206250 prefixEnd_1206250 := by exact prefixLift 1206250
  have htrace : WordTrace (prefixWord ++ tailWord_1206250) baseStart_1206250 baseEnd_1206250 := by
    simpa [prefixWord, tailWord_1206250, baseEnd_1206250] using wordTrace_append hprefix tailTrace_1206250
  have hstable : (prefixWord ++ tailWord_1206250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206250).length < 2 ^ (prefixWord ++ tailWord_1206250).sum := by decide
  have hdescent : baseEnd_1206250 < baseStart_1206250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206306 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1206306 : Nat := 118140960795 + 1206306 * 2 ^ 59
def prefixEnd_1206306 : Nat := 4983230072969 + 3 ^ 40 * 1206306 * 2
def baseEnd_1206306 : Nat := 412943196268441703951537

theorem tailTrace_1206306 : CollatzResearch.WordTrace tailWord_1206306 prefixEnd_1206306 412943196268441703951537 := by
  unfold tailWord_1206306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999398591941714376941693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29331729578511238338511181 10999398591941714376941693)
  ·
    refine ⟨4124774471978142891353135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10999398591941714376941693 4124774471978142891353135)
    ·
      refine ⟨6187161707967214337029703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4124774471978142891353135 6187161707967214337029703)
      ·
        refine ⟨9280742561950821505544555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6187161707967214337029703 9280742561950821505544555)
        ·
          refine ⟨13921113842926232258316833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280742561950821505544555 13921113842926232258316833)
          ·
            refine ⟨10440835382194674193737625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13921113842926232258316833 10440835382194674193737625)
            ·
              refine ⟨7830626536646005645303219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440835382194674193737625 7830626536646005645303219)
              ·
                refine ⟨11745939804969008467954829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830626536646005645303219 11745939804969008467954829)
                ·
                  refine ⟨4404727426863378175483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11745939804969008467954829 4404727426863378175483061)
                  ·
                    refine ⟨412943196268441703951537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4404727426863378175483061 412943196268441703951537)
                    ·
                      rfl

theorem cell22_1206306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1206306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206306 prefixEnd_1206306 := by exact prefixLift 1206306
  have htrace : WordTrace (prefixWord ++ tailWord_1206306) baseStart_1206306 baseEnd_1206306 := by
    simpa [prefixWord, tailWord_1206306, baseEnd_1206306] using wordTrace_append hprefix tailTrace_1206306
  have hstable : (prefixWord ++ tailWord_1206306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206306).length < 2 ^ (prefixWord ++ tailWord_1206306).sum := by decide
  have hdescent : baseEnd_1206306 < baseStart_1206306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206321 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1206321 : Nat := 118140960795 + 1206321 * 2 ^ 59
def prefixEnd_1206321 : Nat := 4983230072969 + 3 ^ 40 * 1206321 * 2
def baseEnd_1206321 : Nat := 412948331074986664826491

theorem tailTrace_1206321 : CollatzResearch.WordTrace tailWord_1206321 prefixEnd_1206321 412948331074986664826491 := by
  unfold tailWord_1206321
  simp only [CollatzResearch.WordTrace]
  refine ⟨43998141462712515069562817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29332094308475010046375211 43998141462712515069562817)
  ·
    refine ⟨32998606097034386302172113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43998141462712515069562817 32998606097034386302172113)
    ·
      refine ⟨24748954572775789726629085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32998606097034386302172113 24748954572775789726629085)
      ·
        refine ⟨9280857964790921147485907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24748954572775789726629085 9280857964790921147485907)
        ·
          refine ⟨13921286947186381721228861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280857964790921147485907 13921286947186381721228861)
          ·
            refine ⟨5220482605194893145460823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13921286947186381721228861 5220482605194893145460823)
            ·
              refine ⟨7830723907792339718191235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220482605194893145460823 7830723907792339718191235)
              ·
                refine ⟨11746085861688509577286853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830723907792339718191235 11746085861688509577286853)
                ·
                  refine ⟨2202391099066595545741285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11746085861688509577286853 2202391099066595545741285)
                  ·
                    refine ⟨412948331074986664826491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202391099066595545741285 412948331074986664826491)
                    ·
                      rfl

theorem cell22_1206321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1206321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206321 prefixEnd_1206321 := by exact prefixLift 1206321
  have htrace : WordTrace (prefixWord ++ tailWord_1206321) baseStart_1206321 baseEnd_1206321 := by
    simpa [prefixWord, tailWord_1206321, baseEnd_1206321] using wordTrace_append hprefix tailTrace_1206321
  have hstable : (prefixWord ++ tailWord_1206321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206321).length < 2 ^ (prefixWord ++ tailWord_1206321).sum := by decide
  have hdescent : baseEnd_1206321 < baseStart_1206321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206336 : List Nat := [2, 1, 1, 2, 2, 5, 2, 7]
def baseStart_1206336 : Nat := 118140960795 + 1206336 * 2 ^ 59
def prefixEnd_1206336 : Nat := 4983230072969 + 3 ^ 40 * 1206336 * 2
def baseEnd_1206336 : Nat := 45883718431281291744605

theorem tailTrace_1206336 : CollatzResearch.WordTrace tailWord_1206336 prefixEnd_1206336 45883718431281291744605 := by
  unfold tailWord_1206336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21999344278829086315679431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29332459038438781754239241 21999344278829086315679431)
  ·
    refine ⟨32999016418243629473519147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21999344278829086315679431 32999016418243629473519147)
    ·
      refine ⟨49498524627365444210278721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32999016418243629473519147 49498524627365444210278721)
      ·
        refine ⟨37123893470524083157709041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49498524627365444210278721 37123893470524083157709041)
        ·
          refine ⟨27842920102893062368281781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37123893470524083157709041 27842920102893062368281781)
          ·
            refine ⟨2610273759646224597026417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27842920102893062368281781 2610273759646224597026417)
            ·
              refine ⟨1957705319734668447769813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610273759646224597026417 1957705319734668447769813)
              ·
                refine ⟨45883718431281291744605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1957705319734668447769813 45883718431281291744605)
                ·
                  rfl

theorem cell22_1206336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_1206336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206336 prefixEnd_1206336 := by exact prefixLift 1206336
  have htrace : WordTrace (prefixWord ++ tailWord_1206336) baseStart_1206336 baseEnd_1206336 := by
    simpa [prefixWord, tailWord_1206336, baseEnd_1206336] using wordTrace_append hprefix tailTrace_1206336
  have hstable : (prefixWord ++ tailWord_1206336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206336).length < 2 ^ (prefixWord ++ tailWord_1206336).sum := by decide
  have hdescent : baseEnd_1206336 < baseStart_1206336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206385 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_1206385 : Nat := 118140960795 + 1206385 * 2 ^ 59
def prefixEnd_1206385 : Nat := 4983230072969 + 3 ^ 40 * 1206385 * 2
def baseEnd_1206385 : Nat := 412970239582911831226295

theorem tailTrace_1206385 : CollatzResearch.WordTrace tailWord_1206385 prefixEnd_1206385 412970239582911831226295 := by
  unfold tailWord_1206385
  simp only [CollatzResearch.WordTrace]
  refine ⟨44000475734480653999892609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29333650489653769333261739 44000475734480653999892609)
  ·
    refine ⟨33000356800860490499919457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44000475734480653999892609 33000356800860490499919457)
    ·
      refine ⟨24750267600645367874939593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33000356800860490499919457 24750267600645367874939593)
      ·
        refine ⟨18562700700484025906204695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24750267600645367874939593 18562700700484025906204695)
        ·
          refine ⟨27844051050726038859307043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562700700484025906204695 27844051050726038859307043)
          ·
            refine ⟨41766076576089058288960565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27844051050726038859307043 41766076576089058288960565)
            ·
              refine ⟨3915569679008349214590053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41766076576089058288960565 3915569679008349214590053)
              ·
                refine ⟨734169314814065477735635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3915569679008349214590053 734169314814065477735635)
                ·
                  refine ⟨1101253972221098216603453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734169314814065477735635 1101253972221098216603453)
                  ·
                    refine ⟨412970239582911831226295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101253972221098216603453 412970239582911831226295)
                    ·
                      rfl

theorem cell22_1206385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_1206385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206385 prefixEnd_1206385 := by exact prefixLift 1206385
  have htrace : WordTrace (prefixWord ++ tailWord_1206385) baseStart_1206385 baseEnd_1206385 := by
    simpa [prefixWord, tailWord_1206385, baseEnd_1206385] using wordTrace_append hprefix tailTrace_1206385
  have hstable : (prefixWord ++ tailWord_1206385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206385).length < 2 ^ (prefixWord ++ tailWord_1206385).sum := by decide
  have hdescent : baseEnd_1206385 < baseStart_1206385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206396 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1206396 : Nat := 118140960795 + 1206396 * 2 ^ 59
def prefixEnd_1206396 : Nat := 4983230072969 + 3 ^ 40 * 1206396 * 2
def baseEnd_1206396 : Nat := 412974005107711469201261

theorem tailTrace_1206396 : CollatzResearch.WordTrace tailWord_1206396 prefixEnd_1206396 412974005107711469201261 := by
  unfold tailWord_1206396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000438468720401439271521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29333917958293868585695361 22000438468720401439271521)
  ·
    refine ⟨16500328851540301079453641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22000438468720401439271521 16500328851540301079453641)
    ·
      refine ⟨12375246638655225809590231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16500328851540301079453641 12375246638655225809590231)
      ·
        refine ⟨18562869957982838714385347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375246638655225809590231 18562869957982838714385347)
        ·
          refine ⟨27844304936974258071578021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562869957982838714385347 27844304936974258071578021)
          ·
            refine ⟨5220807175682673388420879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27844304936974258071578021 5220807175682673388420879)
            ·
              refine ⟨7831210763524010082631319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220807175682673388420879 7831210763524010082631319)
              ·
                refine ⟨11746816145286015123946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7831210763524010082631319 11746816145286015123946979)
                ·
                  refine ⟨17620224217929022685920469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11746816145286015123946979 17620224217929022685920469)
                  ·
                    refine ⟨412974005107711469201261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17620224217929022685920469 412974005107711469201261)
                    ·
                      rfl

theorem cell22_1206396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1206396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206396 prefixEnd_1206396 := by exact prefixLift 1206396
  have htrace : WordTrace (prefixWord ++ tailWord_1206396) baseStart_1206396 baseEnd_1206396 := by
    simpa [prefixWord, tailWord_1206396, baseEnd_1206396] using wordTrace_append hprefix tailTrace_1206396
  have hstable : (prefixWord ++ tailWord_1206396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206396).length < 2 ^ (prefixWord ++ tailWord_1206396).sum := by decide
  have hdescent : baseEnd_1206396 < baseStart_1206396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206456 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1206456 : Nat := 118140960795 + 1206456 * 2 ^ 59
def prefixEnd_1206456 : Nat := 4983230072969 + 3 ^ 40 * 1206456 * 2
def baseEnd_1206456 : Nat := 412994544333891312701077

theorem tailTrace_1206456 : CollatzResearch.WordTrace tailWord_1206456 prefixEnd_1206456 412994544333891312701077 := by
  unfold tailWord_1206456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22001532658611716562863611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29335376878148955417151481 22001532658611716562863611)
  ·
    refine ⟨33002298987917574844295417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22001532658611716562863611 33002298987917574844295417)
    ·
      refine ⟨24751724240938181133221563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33002298987917574844295417 24751724240938181133221563)
      ·
        refine ⟨37127586361407271699832345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24751724240938181133221563 37127586361407271699832345)
        ·
          refine ⟨27845689771055453774874259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37127586361407271699832345 27845689771055453774874259)
          ·
            refine ⟨41768534656583180662311389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27845689771055453774874259 41768534656583180662311389)
            ·
              refine ⟨15663200496218692748366771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41768534656583180662311389 15663200496218692748366771)
              ·
                refine ⟨23494800744328039122550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15663200496218692748366771 23494800744328039122550157)
                ·
                  refine ⟨8810550279123014670956309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23494800744328039122550157 8810550279123014670956309)
                  ·
                    refine ⟨412994544333891312701077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8810550279123014670956309 412994544333891312701077)
                    ·
                      rfl

theorem cell22_1206456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1206456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206456 prefixEnd_1206456 := by exact prefixLift 1206456
  have htrace : WordTrace (prefixWord ++ tailWord_1206456) baseStart_1206456 baseEnd_1206456 := by
    simpa [prefixWord, tailWord_1206456, baseEnd_1206456] using wordTrace_append hprefix tailTrace_1206456
  have hstable : (prefixWord ++ tailWord_1206456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206456).length < 2 ^ (prefixWord ++ tailWord_1206456).sum := by decide
  have hdescent : baseEnd_1206456 < baseStart_1206456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206458 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_1206458 : Nat := 118140960795 + 1206458 * 2 ^ 59
def prefixEnd_1206458 : Nat := 4983230072969 + 3 ^ 40 * 1206458 * 2
def baseEnd_1206458 : Nat := 412995228974763974151071

theorem tailTrace_1206458 : CollatzResearch.WordTrace tailWord_1206458 prefixEnd_1206458 412995228974763974151071 := by
  unfold tailWord_1206458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000784565804046866825007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29335425508810791644866685 11000784565804046866825007)
  ·
    refine ⟨16501176848706070300237511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11000784565804046866825007 16501176848706070300237511)
    ·
      refine ⟨24751765273059105450356267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16501176848706070300237511 24751765273059105450356267)
      ·
        refine ⟨37127647909588658175534401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24751765273059105450356267 37127647909588658175534401)
        ·
          refine ⟨27845735932191493631650801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37127647909588658175534401 27845735932191493631650801)
          ·
            refine ⟨20884301949143620223738101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27845735932191493631650801 20884301949143620223738101)
            ·
              refine ⟨1957903307732214395975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20884301949143620223738101 1957903307732214395975447)
              ·
                refine ⟨2936854961598321593963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957903307732214395975447 2936854961598321593963171)
                ·
                  refine ⟨4405282442397482390944757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936854961598321593963171 4405282442397482390944757)
                  ·
                    refine ⟨412995228974763974151071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4405282442397482390944757 412995228974763974151071)
                    ·
                      rfl

theorem cell22_1206458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_1206458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206458 prefixEnd_1206458 := by exact prefixLift 1206458
  have htrace : WordTrace (prefixWord ++ tailWord_1206458) baseStart_1206458 baseEnd_1206458 := by
    simpa [prefixWord, tailWord_1206458, baseEnd_1206458] using wordTrace_append hprefix tailTrace_1206458
  have hstable : (prefixWord ++ tailWord_1206458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206458).length < 2 ^ (prefixWord ++ tailWord_1206458).sum := by decide
  have hdescent : baseEnd_1206458 < baseStart_1206458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206462 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1206462 : Nat := 118140960795 + 1206462 * 2 ^ 59
def prefixEnd_1206462 : Nat := 4983230072969 + 3 ^ 40 * 1206462 * 2
def baseEnd_1206462 : Nat := 412996598256509297051059

theorem tailTrace_1206462 : CollatzResearch.WordTrace tailWord_1206462 prefixEnd_1206462 412996598256509297051059 := by
  unfold tailWord_1206462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500410519400212018805705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29335522770134464100297093 5500410519400212018805705)
  ·
    refine ⟨4125307889550159014104279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500410519400212018805705 4125307889550159014104279)
    ·
      refine ⟨6187961834325238521156419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125307889550159014104279 6187961834325238521156419)
      ·
        refine ⟨9281942751487857781734629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6187961834325238521156419 9281942751487857781734629)
        ·
          refine ⟨1740364265903973334075243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9281942751487857781734629 1740364265903973334075243)
          ·
            refine ⟨2610546398855960001112865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740364265903973334075243 2610546398855960001112865)
            ·
              refine ⟨1957909799141970000834649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610546398855960001112865 1957909799141970000834649)
              ·
                refine ⟨1468432349356477500625987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957909799141970000834649 1468432349356477500625987)
                ·
                  refine ⟨2202648524034716250938981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468432349356477500625987 2202648524034716250938981)
                  ·
                    refine ⟨412996598256509297051059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202648524034716250938981 412996598256509297051059)
                    ·
                      rfl

theorem cell22_1206462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1206462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206462 prefixEnd_1206462 := by exact prefixLift 1206462
  have htrace : WordTrace (prefixWord ++ tailWord_1206462) baseStart_1206462 baseEnd_1206462 := by
    simpa [prefixWord, tailWord_1206462, baseEnd_1206462] using wordTrace_append hprefix tailTrace_1206462
  have hstable : (prefixWord ++ tailWord_1206462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206462).length < 2 ^ (prefixWord ++ tailWord_1206462).sum := by decide
  have hdescent : baseEnd_1206462 < baseStart_1206462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206488 : List Nat := [2, 1, 2, 2, 4, 3, 8]
def baseStart_1206488 : Nat := 118140960795 + 1206488 * 2 ^ 59
def prefixEnd_1206488 : Nat := 4983230072969 + 3 ^ 40 * 1206488 * 2
def baseEnd_1206488 : Nat := 15296499947698292440777

theorem tailTrace_1206488 : CollatzResearch.WordTrace tailWord_1206488 prefixEnd_1206488 15296499947698292440777 := by
  unfold tailWord_1206488
  simp only [CollatzResearch.WordTrace]
  refine ⟨22002116226553751295446059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29336154968738335060594745 22002116226553751295446059)
  ·
    refine ⟨33003174339830626943169089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22002116226553751295446059 33003174339830626943169089)
    ·
      refine ⟨24752380754872970207376817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33003174339830626943169089 24752380754872970207376817)
      ·
        refine ⟨18564285566154727655532613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24752380754872970207376817 18564285566154727655532613)
        ·
          refine ⟨3480803543654011435412365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18564285566154727655532613 3480803543654011435412365)
          ·
            refine ⟨1305301328870254288279637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3480803543654011435412365 1305301328870254288279637)
            ·
              refine ⟨15296499947698292440777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1305301328870254288279637 15296499947698292440777)
              ·
                rfl

theorem cell22_1206488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 8].length) (baseStart_1206488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206488 prefixEnd_1206488 := by exact prefixLift 1206488
  have htrace : WordTrace (prefixWord ++ tailWord_1206488) baseStart_1206488 baseEnd_1206488 := by
    simpa [prefixWord, tailWord_1206488, baseEnd_1206488] using wordTrace_append hprefix tailTrace_1206488
  have hstable : (prefixWord ++ tailWord_1206488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206488).length < 2 ^ (prefixWord ++ tailWord_1206488).sum := by decide
  have hdescent : baseEnd_1206488 < baseStart_1206488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206554 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_1206554 : Nat := 118140960795 + 1206554 * 2 ^ 59
def prefixEnd_1206554 : Nat := 4983230072969 + 3 ^ 40 * 1206554 * 2
def baseEnd_1206554 : Nat := 413028091736651723750777

theorem tailTrace_1206554 : CollatzResearch.WordTrace tailWord_1206554 prefixEnd_1206554 413028091736651723750777 := by
  unfold tailWord_1206554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11001659917717098965698679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29337759780578930575196477 11001659917717098965698679)
  ·
    refine ⟨16502489876575648448548019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11001659917717098965698679 16502489876575648448548019)
    ·
      refine ⟨24753734814863472672822029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16502489876575648448548019 24753734814863472672822029)
      ·
        refine ⟨9282650555573802252308261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24753734814863472672822029 9282650555573802252308261)
        ·
          refine ⟨1740496979170087922307799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9282650555573802252308261 1740496979170087922307799)
          ·
            refine ⟨2610745468755131883461699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740496979170087922307799 2610745468755131883461699)
            ·
              refine ⟨3916118203132697825192549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610745468755131883461699 3916118203132697825192549)
              ·
                refine ⟨734272163087380842223603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3916118203132697825192549 734272163087380842223603)
                ·
                  refine ⟨1101408244631071263335405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734272163087380842223603 1101408244631071263335405)
                  ·
                    refine ⟨413028091736651723750777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101408244631071263335405 413028091736651723750777)
                    ·
                      rfl

theorem cell22_1206554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_1206554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206554 prefixEnd_1206554 := by exact prefixLift 1206554
  have htrace : WordTrace (prefixWord ++ tailWord_1206554) baseStart_1206554 baseEnd_1206554 := by
    simpa [prefixWord, tailWord_1206554, baseEnd_1206554] using wordTrace_append hprefix tailTrace_1206554
  have hstable : (prefixWord ++ tailWord_1206554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206554).length < 2 ^ (prefixWord ++ tailWord_1206554).sum := by decide
  have hdescent : baseEnd_1206554 < baseStart_1206554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206563 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_1206563 : Nat := 118140960795 + 1206563 * 2 ^ 59
def prefixEnd_1206563 : Nat := 4983230072969 + 3 ^ 40 * 1206563 * 2
def baseEnd_1206563 : Nat := 413031172620578700275749

theorem tailTrace_1206563 : CollatzResearch.WordTrace tailWord_1206563 prefixEnd_1206563 413031172620578700275749 := by
  unfold tailWord_1206563
  simp only [CollatzResearch.WordTrace]
  refine ⟨44006967927835790399872343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29337978618557193599914895 44006967927835790399872343)
  ·
    refine ⟨66010451891753685599808515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44006967927835790399872343 66010451891753685599808515)
    ·
      refine ⟨99015677837630528399712773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66010451891753685599808515 99015677837630528399712773)
      ·
        refine ⟨18565439594555724074946145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99015677837630528399712773 18565439594555724074946145)
        ·
          refine ⟨13924079695916793056209609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18565439594555724074946145 13924079695916793056209609)
          ·
            refine ⟨10443059771937594792157207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13924079695916793056209609 10443059771937594792157207)
            ·
              refine ⟨15664589657906392188235811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443059771937594792157207 15664589657906392188235811)
              ·
                refine ⟨23496884486859588282353717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15664589657906392188235811 23496884486859588282353717)
                ·
                  refine ⟨2202832920643086401470661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23496884486859588282353717 2202832920643086401470661)
                  ·
                    refine ⟨413031172620578700275749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202832920643086401470661 413031172620578700275749)
                    ·
                      rfl

theorem cell22_1206563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_1206563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206563 prefixEnd_1206563 := by exact prefixLift 1206563
  have htrace : WordTrace (prefixWord ++ tailWord_1206563) baseStart_1206563 baseEnd_1206563 := by
    simpa [prefixWord, tailWord_1206563, baseEnd_1206563] using wordTrace_append hprefix tailTrace_1206563
  have hstable : (prefixWord ++ tailWord_1206563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206563).length < 2 ^ (prefixWord ++ tailWord_1206563).sum := by decide
  have hdescent : baseEnd_1206563 < baseStart_1206563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206565 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_1206565 : Nat := 118140960795 + 1206565 * 2 ^ 59
def prefixEnd_1206565 : Nat := 4983230072969 + 3 ^ 40 * 1206565 * 2
def baseEnd_1206565 : Nat := 413031857261451361725743

theorem tailTrace_1206565 : CollatzResearch.WordTrace tailWord_1206565 prefixEnd_1206565 413031857261451361725743 := by
  unfold tailWord_1206565
  simp only [CollatzResearch.WordTrace]
  refine ⟨44007040873828544741445149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29338027249219029827630099 44007040873828544741445149)
  ·
    refine ⟨16502640327685704278041931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44007040873828544741445149 16502640327685704278041931)
    ·
      refine ⟨24753960491528556417062897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16502640327685704278041931 24753960491528556417062897)
      ·
        refine ⟨18565470368646417312797173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24753960491528556417062897 18565470368646417312797173)
        ·
          refine ⟨1740512847060601623074735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18565470368646417312797173 1740512847060601623074735)
          ·
            refine ⟨2610769270590902434612103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740512847060601623074735 2610769270590902434612103)
            ·
              refine ⟨3916153905886353651918155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610769270590902434612103 3916153905886353651918155)
              ·
                refine ⟨5874230858829530477877233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916153905886353651918155 5874230858829530477877233)
                ·
                  refine ⟨4405673144122147858407925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5874230858829530477877233 4405673144122147858407925)
                  ·
                    refine ⟨413031857261451361725743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4405673144122147858407925 413031857261451361725743)
                    ·
                      rfl

theorem cell22_1206565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_1206565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206565 prefixEnd_1206565 := by exact prefixLift 1206565
  have htrace : WordTrace (prefixWord ++ tailWord_1206565) baseStart_1206565 baseEnd_1206565 := by
    simpa [prefixWord, tailWord_1206565, baseEnd_1206565] using wordTrace_append hprefix tailTrace_1206565
  have hstable : (prefixWord ++ tailWord_1206565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206565).length < 2 ^ (prefixWord ++ tailWord_1206565).sum := by decide
  have hdescent : baseEnd_1206565 < baseStart_1206565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206595 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 4]
def baseStart_1206595 : Nat := 118140960795 + 1206595 * 2 ^ 59
def prefixEnd_1206595 : Nat := 4983230072969 + 3 ^ 40 * 1206595 * 2
def baseEnd_1206595 : Nat := 137680708958180427825217

theorem tailTrace_1206595 : CollatzResearch.WordTrace tailWord_1206595 prefixEnd_1206595 137680708958180427825217 := by
  unfold tailWord_1206595
  simp only [CollatzResearch.WordTrace]
  refine ⟨44008135063719859865037239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29338756709146573243358159 44008135063719859865037239)
  ·
    refine ⟨66012202595579789797555859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44008135063719859865037239 66012202595579789797555859)
    ·
      refine ⟨99018303893369684696333789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66012202595579789797555859 99018303893369684696333789)
      ·
        refine ⟨37131863960013631761125171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99018303893369684696333789 37131863960013631761125171)
        ·
          refine ⟨55697795940020447641687757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37131863960013631761125171 55697795940020447641687757)
          ·
            refine ⟨20886673477507667865632909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55697795940020447641687757 20886673477507667865632909)
            ·
              refine ⟨7832502554065375449612341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20886673477507667865632909 7832502554065375449612341)
              ·
                refine ⟨734297114443628948401157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7832502554065375449612341 734297114443628948401157)
                ·
                  refine ⟨137680708958180427825217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734297114443628948401157 137680708958180427825217)
                  ·
                    rfl

theorem cell22_1206595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 4].length) (baseStart_1206595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206595 prefixEnd_1206595 := by exact prefixLift 1206595
  have htrace : WordTrace (prefixWord ++ tailWord_1206595) baseStart_1206595 baseEnd_1206595 := by
    simpa [prefixWord, tailWord_1206595, baseEnd_1206595] using wordTrace_append hprefix tailTrace_1206595
  have hstable : (prefixWord ++ tailWord_1206595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206595).length < 2 ^ (prefixWord ++ tailWord_1206595).sum := by decide
  have hdescent : baseEnd_1206595 < baseStart_1206595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206612 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1206612 : Nat := 118140960795 + 1206612 * 2 ^ 59
def prefixEnd_1206612 : Nat := 4983230072969 + 3 ^ 40 * 1206612 * 2
def baseEnd_1206612 : Nat := 137682648773986301933533

theorem tailTrace_1206612 : CollatzResearch.WordTrace tailWord_1206612 prefixEnd_1206612 137682648773986301933533 := by
  unfold tailWord_1206612
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004377552329135884203045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29339170069772181178937393 22004377552329135884203045)
  ·
    refine ⟨4125820791061712978288071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22004377552329135884203045 4125820791061712978288071)
    ·
      refine ⟨6188731186592569467432107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125820791061712978288071 6188731186592569467432107)
      ·
        refine ⟨9283096779888854201148161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188731186592569467432107 9283096779888854201148161)
        ·
          refine ⟨6962322584916640650861121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9283096779888854201148161 6962322584916640650861121)
          ·
            refine ⟨5221741938687480488145841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962322584916640650861121 5221741938687480488145841)
            ·
              refine ⟨3916306454015610366109381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5221741938687480488145841 3916306454015610366109381)
              ·
                refine ⟨734307460127926943645509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3916306454015610366109381 734307460127926943645509)
                ·
                  refine ⟨137682648773986301933533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734307460127926943645509 137682648773986301933533)
                  ·
                    rfl

theorem cell22_1206612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1206612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206612 prefixEnd_1206612 := by exact prefixLift 1206612
  have htrace : WordTrace (prefixWord ++ tailWord_1206612) baseStart_1206612 baseEnd_1206612 := by
    simpa [prefixWord, tailWord_1206612, baseEnd_1206612] using wordTrace_append hprefix tailTrace_1206612
  have hstable : (prefixWord ++ tailWord_1206612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206612).length < 2 ^ (prefixWord ++ tailWord_1206612).sum := by decide
  have hdescent : baseEnd_1206612 < baseStart_1206612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206640 : List Nat := [2, 1, 1, 1, 4, 3, 4, 6]
def baseStart_1206640 : Nat := 118140960795 + 1206640 * 2 ^ 59
def prefixEnd_1206640 : Nat := 4983230072969 + 3 ^ 40 * 1206640 * 2
def baseEnd_1206640 : Nat := 45895281254908462900057

theorem tailTrace_1206640 : CollatzResearch.WordTrace tailWord_1206640 prefixEnd_1206640 45895281254908462900057 := by
  unfold tailWord_1206640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004888174278416275212687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29339850899037888366950249 22004888174278416275212687)
  ·
    refine ⟨33007332261417624412819031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22004888174278416275212687 33007332261417624412819031)
    ·
      refine ⟨49510998392126436619228547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33007332261417624412819031 49510998392126436619228547)
      ·
        refine ⟨74266497588189654928842821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49510998392126436619228547 74266497588189654928842821)
        ·
          refine ⟨13924968297785560299158029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74266497588189654928842821 13924968297785560299158029)
          ·
            refine ⟨5221863111669585112184261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13924968297785560299158029 5221863111669585112184261)
            ·
              refine ⟨979099333438047208534549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5221863111669585112184261 979099333438047208534549)
              ·
                refine ⟨45895281254908462900057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 979099333438047208534549 45895281254908462900057)
                ·
                  rfl

theorem cell22_1206640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_1206640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206640 prefixEnd_1206640 := by exact prefixLift 1206640
  have htrace : WordTrace (prefixWord ++ tailWord_1206640) baseStart_1206640 baseEnd_1206640 := by
    simpa [prefixWord, tailWord_1206640, baseEnd_1206640] using wordTrace_append hprefix tailTrace_1206640
  have hstable : (prefixWord ++ tailWord_1206640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206640).length < 2 ^ (prefixWord ++ tailWord_1206640).sum := by decide
  have hdescent : baseEnd_1206640 < baseStart_1206640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206730 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_1206730 : Nat := 118140960795 + 1206730 * 2 ^ 59
def prefixEnd_1206730 : Nat := 4983230072969 + 3 ^ 40 * 1206730 * 2
def baseEnd_1206730 : Nat := 137696113377815310450079

theorem tailTrace_1206730 : CollatzResearch.WordTrace tailWord_1206730 prefixEnd_1206730 137696113377815310450079 := by
  unfold tailWord_1206730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11003264729557694480300411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29342039278820518614134429 11003264729557694480300411)
  ·
    refine ⟨16504897094336541720450617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11003264729557694480300411 16504897094336541720450617)
    ·
      refine ⟨12378672820752406290337963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16504897094336541720450617 12378672820752406290337963)
      ·
        refine ⟨18568009231128609435506945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12378672820752406290337963 18568009231128609435506945)
        ·
          refine ⟨13926006923346457076630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18568009231128609435506945 13926006923346457076630209)
          ·
            refine ⟨10444505192509842807472657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13926006923346457076630209 10444505192509842807472657)
            ·
              refine ⟨7833378894382382105604493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10444505192509842807472657 7833378894382382105604493)
              ·
                refine ⟨2937517085393393289601685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7833378894382382105604493 2937517085393393289601685)
                ·
                  refine ⟨137696113377815310450079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2937517085393393289601685 137696113377815310450079)
                  ·
                    rfl

theorem cell22_1206730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_1206730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206730 prefixEnd_1206730 := by exact prefixLift 1206730
  have htrace : WordTrace (prefixWord ++ tailWord_1206730) baseStart_1206730 baseEnd_1206730 := by
    simpa [prefixWord, tailWord_1206730, baseEnd_1206730] using wordTrace_append hprefix tailTrace_1206730
  have hstable : (prefixWord ++ tailWord_1206730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206730).length < 2 ^ (prefixWord ++ tailWord_1206730).sum := by decide
  have hdescent : baseEnd_1206730 < baseStart_1206730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206762 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1206762 : Nat := 118140960795 + 1206762 * 2 ^ 59
def prefixEnd_1206762 : Nat := 4983230072969 + 3 ^ 40 * 1206762 * 2
def baseEnd_1206762 : Nat := 413099294387408514550139

theorem tailTrace_1206762 : CollatzResearch.WordTrace tailWord_1206762 prefixEnd_1206762 413099294387408514550139 := by
  unfold tailWord_1206762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11003556513528711846591635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29342817369409898257577693 11003556513528711846591635)
  ·
    refine ⟨16505334770293067769887453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11003556513528711846591635 16505334770293067769887453)
    ·
      refine ⟨6189500538859900413707795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16505334770293067769887453 6189500538859900413707795)
      ·
        refine ⟨9284250808289850620561693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189500538859900413707795 9284250808289850620561693)
        ·
          refine ⟨3481594053108693982710635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9284250808289850620561693 3481594053108693982710635)
          ·
            refine ⟨5222391079663040974065953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481594053108693982710635 5222391079663040974065953)
            ·
              refine ⟨3916793309747280730549465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5222391079663040974065953 3916793309747280730549465)
              ·
                refine ⟨2937594982310460547912099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916793309747280730549465 2937594982310460547912099)
                ·
                  refine ⟨4406392473465690821868149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937594982310460547912099 4406392473465690821868149)
                  ·
                    refine ⟨413099294387408514550139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4406392473465690821868149 413099294387408514550139)
                    ·
                      rfl

theorem cell22_1206762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1206762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1206762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1206762 prefixEnd_1206762 := by exact prefixLift 1206762
  have htrace : WordTrace (prefixWord ++ tailWord_1206762) baseStart_1206762 baseEnd_1206762 := by
    simpa [prefixWord, tailWord_1206762, baseEnd_1206762] using wordTrace_append hprefix tailTrace_1206762
  have hstable : (prefixWord ++ tailWord_1206762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206762).length < 2 ^ (prefixWord ++ tailWord_1206762).sum := by decide
  have hdescent : baseEnd_1206762 < baseStart_1206762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
