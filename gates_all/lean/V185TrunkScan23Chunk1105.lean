import V185TrunkScan23Chunk1104

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6543007 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 1, 5]
def baseStart_6543007 : Nat := 118140960795 + 6543007 * 2 ^ 59
def prefixEnd_6543007 : Nat := 4983230072969 + 3 ^ 40 * 6543007 * 2
def baseEnd_6543007 : Nat := 1119902505577529062907255

theorem tailTrace_6543007 : CollatzResearch.WordTrace tailWord_6543007 prefixEnd_6543007 1119902505577529062907255 := by
  unfold tailWord_6543007
  simp only [CollatzResearch.WordTrace]
  refine ⟨238643070606810570475443275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159095380404540380316962183 238643070606810570475443275)
  ·
    refine ⟨357964605910215855713164913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238643070606810570475443275 357964605910215855713164913)
    ·
      refine ⟨268473454432661891784873685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357964605910215855713164913 268473454432661891784873685)
      ·
        refine ⟨6292346588265513088707977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 268473454432661891784873685 6292346588265513088707977)
        ·
          refine ⟨4719259941199134816530983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6292346588265513088707977 4719259941199134816530983)
          ·
            refine ⟨7078889911798702224796475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719259941199134816530983 7078889911798702224796475)
            ·
              refine ⟨10618334867698053337194713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078889911798702224796475 10618334867698053337194713)
              ·
                refine ⟨7963751150773540002896035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10618334867698053337194713 7963751150773540002896035)
                ·
                  refine ⟨11945626726160310004344053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7963751150773540002896035 11945626726160310004344053)
                  ·
                    refine ⟨1119902505577529062907255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11945626726160310004344053 1119902505577529062907255)
                    ·
                      rfl

theorem cell23_6543007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_6543007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543007 prefixEnd_6543007 := by exact prefixLift 6543007
  have htrace : WordTrace (prefixWord ++ tailWord_6543007) baseStart_6543007 baseEnd_6543007 := by
    simpa [prefixWord, tailWord_6543007, baseEnd_6543007] using wordTrace_append hprefix tailTrace_6543007
  have hstable : (prefixWord ++ tailWord_6543007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543007).length < 2 ^ (prefixWord ++ tailWord_6543007).sum := by decide
  have hdescent : baseEnd_6543007 < baseStart_6543007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543010 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6543010 : Nat := 118140960795 + 6543010 * 2 ^ 59
def prefixEnd_6543010 : Nat := 4983230072969 + 3 ^ 40 * 6543010 * 2
def baseEnd_6543010 : Nat := 3359709057174550676984251

theorem tailTrace_6543010 : CollatzResearch.WordTrace tailWord_6543010 prefixEnd_6543010 3359709057174550676984251 := by
  unfold tailWord_6543010
  simp only [CollatzResearch.WordTrace]
  refine ⟨59660795006449925496950621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159095453350533134658534989 59660795006449925496950621)
  ·
    refine ⟨22372798127418722061356483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59660795006449925496950621 22372798127418722061356483)
    ·
      refine ⟨33559197191128083092034725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22372798127418722061356483 33559197191128083092034725)
      ·
        refine ⟨6292349473336515579756511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33559197191128083092034725 6292349473336515579756511)
        ·
          refine ⟨9438524210004773369634767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292349473336515579756511 9438524210004773369634767)
          ·
            refine ⟨14157786315007160054452151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438524210004773369634767 14157786315007160054452151)
            ·
              refine ⟨21236679472510740081678227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157786315007160054452151 21236679472510740081678227)
              ·
                refine ⟨31855019208766110122517341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21236679472510740081678227 31855019208766110122517341)
                ·
                  refine ⟨11945632203287291295944003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31855019208766110122517341 11945632203287291295944003)
                  ·
                    refine ⟨17918448304930936943916005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11945632203287291295944003 17918448304930936943916005)
                    ·
                      refine ⟨3359709057174550676984251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17918448304930936943916005 3359709057174550676984251)
                      ·
                        rfl

theorem cell23_6543010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6543010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543010 prefixEnd_6543010 := by exact prefixLift 6543010
  have htrace : WordTrace (prefixWord ++ tailWord_6543010) baseStart_6543010 baseEnd_6543010 := by
    simpa [prefixWord, tailWord_6543010, baseEnd_6543010] using wordTrace_append hprefix tailTrace_6543010
  have hstable : (prefixWord ++ tailWord_6543010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543010).length < 2 ^ (prefixWord ++ tailWord_6543010).sum := by decide
  have hdescent : baseEnd_6543010 < baseStart_6543010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543013 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_6543013 : Nat := 118140960795 + 6543013 * 2 ^ 59
def prefixEnd_6543013 : Nat := 4983230072969 + 3 ^ 40 * 6543013 * 2
def baseEnd_6543013 : Nat := 3359710597616514165246737

theorem tailTrace_6543013 : CollatzResearch.WordTrace tailWord_6543013 prefixEnd_6543013 3359710597616514165246737 := by
  unfold tailWord_6543013
  simp only [CollatzResearch.WordTrace]
  refine ⟨238643289444788833500161693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159095526296525889000107795 238643289444788833500161693)
  ·
    refine ⟨89491233541795812562560635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238643289444788833500161693 89491233541795812562560635)
    ·
      refine ⟨134236850312693718843840953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89491233541795812562560635 134236850312693718843840953)
      ·
        refine ⟨100677637734520289132880715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134236850312693718843840953 100677637734520289132880715)
        ·
          refine ⟨151016456601780433699321073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100677637734520289132880715 151016456601780433699321073)
          ·
            refine ⟨113262342451335325274490805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151016456601780433699321073 113262342451335325274490805)
            ·
              refine ⟨10618344604812686744483513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113262342451335325274490805 10618344604812686744483513)
              ·
                refine ⟨7963758453609515058362635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10618344604812686744483513 7963758453609515058362635)
                ·
                  refine ⟨11945637680414272587543953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7963758453609515058362635 11945637680414272587543953)
                  ·
                    refine ⟨8959228260310704440657965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11945637680414272587543953 8959228260310704440657965)
                    ·
                      refine ⟨3359710597616514165246737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959228260310704440657965 3359710597616514165246737)
                      ·
                        rfl

theorem cell23_6543013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_6543013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543013 prefixEnd_6543013 := by exact prefixLift 6543013
  have htrace : WordTrace (prefixWord ++ tailWord_6543013) baseStart_6543013 baseEnd_6543013 := by
    simpa [prefixWord, tailWord_6543013, baseEnd_6543013] using wordTrace_append hprefix tailTrace_6543013
  have hstable : (prefixWord ++ tailWord_6543013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543013).length < 2 ^ (prefixWord ++ tailWord_6543013).sum := by decide
  have hdescent : baseEnd_6543013 < baseStart_6543013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543026 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_6543026 : Nat := 118140960795 + 6543026 * 2 ^ 59
def prefixEnd_6543026 : Nat := 4983230072969 + 3 ^ 40 * 6543026 * 2
def baseEnd_6543026 : Nat := 3359717272865022614384177

theorem tailTrace_6543026 : CollatzResearch.WordTrace tailWord_6543026 prefixEnd_6543026 3359717272865022614384177 := by
  unfold tailWord_6543026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59660940898435434180096233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159095842395827824480256621 59660940898435434180096233)
  ·
    refine ⟨44745705673826575635072175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59660940898435434180096233 44745705673826575635072175)
    ·
      refine ⟨67118558510739863452608263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44745705673826575635072175 67118558510739863452608263)
      ·
        refine ⟨100677837766109795178912395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67118558510739863452608263 100677837766109795178912395)
        ·
          refine ⟨151016756649164692768368593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100677837766109795178912395 151016756649164692768368593)
          ·
            refine ⟨113262567486873519576276445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151016756649164692768368593 113262567486873519576276445)
            ·
              refine ⟨42473462807577569841103667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113262567486873519576276445 42473462807577569841103667)
              ·
                refine ⟨63710194211366354761655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42473462807577569841103667 63710194211366354761655501)
                ·
                  refine ⟨23891322829262383035620813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63710194211366354761655501 23891322829262383035620813)
                  ·
                    refine ⟨8959246060973393638357805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23891322829262383035620813 8959246060973393638357805)
                    ·
                      refine ⟨3359717272865022614384177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959246060973393638357805 3359717272865022614384177)
                      ·
                        rfl

theorem cell23_6543026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_6543026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543026 prefixEnd_6543026 := by exact prefixLift 6543026
  have htrace : WordTrace (prefixWord ++ tailWord_6543026) baseStart_6543026 baseEnd_6543026 := by
    simpa [prefixWord, tailWord_6543026, baseEnd_6543026] using wordTrace_append hprefix tailTrace_6543026
  have hstable : (prefixWord ++ tailWord_6543026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543026).length < 2 ^ (prefixWord ++ tailWord_6543026).sum := by decide
  have hdescent : baseEnd_6543026 < baseStart_6543026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543030 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6543030 : Nat := 118140960795 + 6543030 * 2 ^ 59
def prefixEnd_6543030 : Nat := 4983230072969 + 3 ^ 40 * 6543030 * 2
def baseEnd_6543030 : Nat := 3359719326787640598734159

theorem tailTrace_6543030 : CollatzResearch.WordTrace tailWord_6543030 prefixEnd_6543030 3359719326787640598734159 := by
  unfold tailWord_6543030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915244342857952837720659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159095939657151496935687029 14915244342857952837720659)
  ·
    refine ⟨22372866514286929256580989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14915244342857952837720659 22372866514286929256580989)
    ·
      refine ⟨8389824942857598471217871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22372866514286929256580989 8389824942857598471217871)
      ·
        refine ⟨12584737414286397706826807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389824942857598471217871 12584737414286397706826807)
        ·
          refine ⟨18877106121429596560240211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584737414286397706826807 18877106121429596560240211)
          ·
            refine ⟨28315659182144394840360317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18877106121429596560240211 28315659182144394840360317)
            ·
              refine ⟨10618372193304148065135119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28315659182144394840360317 10618372193304148065135119)
              ·
                refine ⟨15927558289956222097702679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618372193304148065135119 15927558289956222097702679)
                ·
                  refine ⟨23891337434934333146554019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15927558289956222097702679 23891337434934333146554019)
                  ·
                    refine ⟨35837006152401499719831029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23891337434934333146554019 35837006152401499719831029)
                    ·
                      refine ⟨3359719326787640598734159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35837006152401499719831029 3359719326787640598734159)
                      ·
                        rfl

theorem cell23_6543030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6543030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543030 prefixEnd_6543030 := by exact prefixLift 6543030
  have htrace : WordTrace (prefixWord ++ tailWord_6543030) baseStart_6543030 baseEnd_6543030 := by
    simpa [prefixWord, tailWord_6543030, baseEnd_6543030] using wordTrace_append hprefix tailTrace_6543030
  have hstable : (prefixWord ++ tailWord_6543030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543030).length < 2 ^ (prefixWord ++ tailWord_6543030).sum := by decide
  have hdescent : baseEnd_6543030 < baseStart_6543030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543060 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6543060 : Nat := 118140960795 + 6543060 * 2 ^ 59
def prefixEnd_6543060 : Nat := 4983230072969 + 3 ^ 40 * 6543060 * 2
def baseEnd_6543060 : Nat := 3359734731207275481359021

theorem tailTrace_6543060 : CollatzResearch.WordTrace tailWord_6543060 prefixEnd_6543060 3359734731207275481359021 := by
  unfold tailWord_6543060
  simp only [CollatzResearch.WordTrace]
  refine ⟨119322501837809280263561317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159096669117079040351415089 119322501837809280263561317)
  ·
    refine ⟨22372969094589240049417747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119322501837809280263561317 22372969094589240049417747)
    ·
      refine ⟨33559453641883860074126621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22372969094589240049417747 33559453641883860074126621)
      ·
        refine ⟨12584795115706447527797483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33559453641883860074126621 12584795115706447527797483)
        ·
          refine ⟨18877192673559671291696225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584795115706447527797483 18877192673559671291696225)
          ·
            refine ⟨14157894505169753468772169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18877192673559671291696225 14157894505169753468772169)
            ·
              refine ⟨10618420878877315101579127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14157894505169753468772169 10618420878877315101579127)
              ·
                refine ⟨15927631318315972652368691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618420878877315101579127 15927631318315972652368691)
                ·
                  refine ⟨23891446977473958978553037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15927631318315972652368691 23891446977473958978553037)
                  ·
                    refine ⟨8959292616552734616957389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23891446977473958978553037 8959292616552734616957389)
                    ·
                      refine ⟨3359734731207275481359021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959292616552734616957389 3359734731207275481359021)
                      ·
                        rfl

theorem cell23_6543060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6543060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543060 prefixEnd_6543060 := by exact prefixLift 6543060
  have htrace : WordTrace (prefixWord ++ tailWord_6543060) baseStart_6543060 baseEnd_6543060 := by
    simpa [prefixWord, tailWord_6543060, baseEnd_6543060] using wordTrace_append hprefix tailTrace_6543060
  have hstable : (prefixWord ++ tailWord_6543060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543060).length < 2 ^ (prefixWord ++ tailWord_6543060).sum := by decide
  have hdescent : baseEnd_6543060 < baseStart_6543060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543083 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 4, 2]
def baseStart_6543083 : Nat := 118140960795 + 6543083 * 2 ^ 59
def prefixEnd_6543083 : Nat := 4983230072969 + 3 ^ 40 * 6543083 * 2
def baseEnd_6543083 : Nat := 3359746541262328891371415

theorem tailTrace_6543083 : CollatzResearch.WordTrace tailWord_6543083 prefixEnd_6543083 3359746541262328891371415 := by
  unfold tailWord_6543083
  simp only [CollatzResearch.WordTrace]
  refine ⟨238645842554535235455209903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159097228369690156970139935 238645842554535235455209903)
  ·
    refine ⟨357968763831802853182814855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238645842554535235455209903 357968763831802853182814855)
    ·
      refine ⟨536953145747704279774222283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357968763831802853182814855 536953145747704279774222283)
      ·
        refine ⟨805429718621556419661333425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536953145747704279774222283 805429718621556419661333425)
        ·
          refine ⟨604072288966167314746000069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805429718621556419661333425 604072288966167314746000069)
          ·
            refine ⟨113263554181156371514875013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 604072288966167314746000069 113263554181156371514875013)
            ·
              refine ⟨21236916408966819659039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113263554181156371514875013 21236916408966819659039065)
              ·
                refine ⟨15927687306725114744279299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21236916408966819659039065 15927687306725114744279299)
                ·
                  refine ⟨23891530960087672116418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15927687306725114744279299 23891530960087672116418949)
                  ·
                    refine ⟨4479662055016438521828553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23891530960087672116418949 4479662055016438521828553)
                    ·
                      refine ⟨3359746541262328891371415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479662055016438521828553 3359746541262328891371415)
                      ·
                        rfl

theorem cell23_6543083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 4, 2].length) (baseStart_6543083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543083 prefixEnd_6543083 := by exact prefixLift 6543083
  have htrace : WordTrace (prefixWord ++ tailWord_6543083) baseStart_6543083 baseEnd_6543083 := by
    simpa [prefixWord, tailWord_6543083, baseEnd_6543083] using wordTrace_append hprefix tailTrace_6543083
  have hstable : (prefixWord ++ tailWord_6543083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543083).length < 2 ^ (prefixWord ++ tailWord_6543083).sum := by decide
  have hdescent : baseEnd_6543083 < baseStart_6543083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543086 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6543086 : Nat := 118140960795 + 6543086 * 2 ^ 59
def prefixEnd_6543086 : Nat := 4983230072969 + 3 ^ 40 * 6543086 * 2
def baseEnd_6543086 : Nat := 3359748081704292379633901

theorem tailTrace_6543086 : CollatzResearch.WordTrace tailWord_6543086 prefixEnd_6543086 3359748081704292379633901 := by
  unfold tailWord_6543086
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830743996690545870946139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159097301315682911311712741 29830743996690545870946139)
  ·
    refine ⟨44746115995035818806419209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29830743996690545870946139 44746115995035818806419209)
    ·
      refine ⟨33559586996276864104814407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44746115995035818806419209 33559586996276864104814407)
      ·
        refine ⟨50339380494415296157221611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33559586996276864104814407 50339380494415296157221611)
        ·
          refine ⟨75509070741622944235832417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50339380494415296157221611 75509070741622944235832417)
          ·
            refine ⟨56631803056217208176874313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75509070741622944235832417 56631803056217208176874313)
            ·
              refine ⟨42473852292162906132655735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56631803056217208176874313 42473852292162906132655735)
              ·
                refine ⟨63710778438244359198983603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42473852292162906132655735 63710778438244359198983603)
                ·
                  refine ⟨95566167657366538798475405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63710778438244359198983603 95566167657366538798475405)
                  ·
                    refine ⟨35837312871512452049428277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95566167657366538798475405 35837312871512452049428277)
                    ·
                      refine ⟨3359748081704292379633901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35837312871512452049428277 3359748081704292379633901)
                      ·
                        rfl

theorem cell23_6543086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6543086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543086 prefixEnd_6543086 := by exact prefixLift 6543086
  have htrace : WordTrace (prefixWord ++ tailWord_6543086) baseStart_6543086 baseEnd_6543086 := by
    simpa [prefixWord, tailWord_6543086, baseEnd_6543086] using wordTrace_append hprefix tailTrace_6543086
  have hstable : (prefixWord ++ tailWord_6543086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543086).length < 2 ^ (prefixWord ++ tailWord_6543086).sum := by decide
  have hdescent : baseEnd_6543086 < baseStart_6543086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_6543099 : Nat := 118140960795 + 6543099 * 2 ^ 59
def prefixEnd_6543099 : Nat := 4983230072969 + 3 ^ 40 * 6543099 * 2
def baseEnd_6543099 : Nat := 3359754756952800828771341

theorem tailTrace_6543099 : CollatzResearch.WordTrace tailWord_6543099 prefixEnd_6543099 3359754756952800828771341 := by
  unfold tailWord_6543099
  simp only [CollatzResearch.WordTrace]
  refine ⟨238646426122477270187792351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159097617414984846791861567 238646426122477270187792351)
  ·
    refine ⟨357969639183715905281688527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238646426122477270187792351 357969639183715905281688527)
    ·
      refine ⟨536954458775573857922532791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357969639183715905281688527 536954458775573857922532791)
      ·
        refine ⟨805431688163360786883799187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536954458775573857922532791 805431688163360786883799187)
        ·
          refine ⟨1208147532245041180325698781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805431688163360786883799187 1208147532245041180325698781)
          ·
            refine ⟨453055324591890442622137043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1208147532245041180325698781 453055324591890442622137043)
            ·
              refine ⟨679582986887835663933205565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453055324591890442622137043 679582986887835663933205565)
              ·
                refine ⟨254843620082938373974952087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679582986887835663933205565 254843620082938373974952087)
                ·
                  refine ⟨382265430124407560962428131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254843620082938373974952087 382265430124407560962428131)
                  ·
                    refine ⟨573398145186611341443642197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 382265430124407560962428131 573398145186611341443642197)
                    ·
                      refine ⟨3359754756952800828771341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 573398145186611341443642197 3359754756952800828771341)
                      ·
                        rfl

theorem cell23_6543099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_6543099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543099 prefixEnd_6543099 := by exact prefixLift 6543099
  have htrace : WordTrace (prefixWord ++ tailWord_6543099) baseStart_6543099 baseEnd_6543099 := by
    simpa [prefixWord, tailWord_6543099, baseEnd_6543099] using wordTrace_append hprefix tailTrace_6543099
  have hstable : (prefixWord ++ tailWord_6543099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543099).length < 2 ^ (prefixWord ++ tailWord_6543099).sum := by decide
  have hdescent : baseEnd_6543099 < baseStart_6543099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543100 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_6543100 : Nat := 118140960795 + 6543100 * 2 ^ 59
def prefixEnd_6543100 : Nat := 4983230072969 + 3 ^ 40 * 6543100 * 2
def baseEnd_6543100 : Nat := 3359755270433455324858837

theorem tailTrace_6543100 : CollatzResearch.WordTrace tailWord_6543100 prefixEnd_6543100 3359755270433455324858837 := by
  unfold tailWord_6543100
  simp only [CollatzResearch.WordTrace]
  refine ⟨119323231297736823679289377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159097641730315764905719169 119323231297736823679289377)
  ·
    refine ⟨89492423473302617759467033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119323231297736823679289377 89492423473302617759467033)
    ·
      refine ⟨67119317604976963319600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89492423473302617759467033 67119317604976963319600275)
      ·
        refine ⟨100678976407465444979400413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67119317604976963319600275 100678976407465444979400413)
        ·
          refine ⟨37754616152799541867275155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100678976407465444979400413 37754616152799541867275155)
          ·
            refine ⟨56631924229199312800912733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37754616152799541867275155 56631924229199312800912733)
            ·
              refine ⟨21236971585949742300342275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56631924229199312800912733 21236971585949742300342275)
              ·
                refine ⟨31855457378924613450513413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21236971585949742300342275 31855457378924613450513413)
                ·
                  refine ⟨5972898258548365021971265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31855457378924613450513413 5972898258548365021971265)
                  ·
                    refine ⟨4479673693911273766478449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972898258548365021971265 4479673693911273766478449)
                    ·
                      refine ⟨3359755270433455324858837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479673693911273766478449 3359755270433455324858837)
                      ·
                        rfl

theorem cell23_6543100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_6543100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543100 prefixEnd_6543100 := by exact prefixLift 6543100
  have htrace : WordTrace (prefixWord ++ tailWord_6543100) baseStart_6543100 baseEnd_6543100 := by
    simpa [prefixWord, tailWord_6543100, baseEnd_6543100] using wordTrace_append hprefix tailTrace_6543100
  have hstable : (prefixWord ++ tailWord_6543100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543100).length < 2 ^ (prefixWord ++ tailWord_6543100).sum := by decide
  have hdescent : baseEnd_6543100 < baseStart_6543100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543136 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_6543136 : Nat := 118140960795 + 6543136 * 2 ^ 59
def prefixEnd_6543136 : Nat := 4983230072969 + 3 ^ 40 * 6543136 * 2
def baseEnd_6543136 : Nat := 1119924585245672394669557

theorem tailTrace_6543136 : CollatzResearch.WordTrace tailWord_6543136 prefixEnd_6543136 1119924585245672394669557 := by
  unfold tailWord_6543136
  simp only [CollatzResearch.WordTrace]
  refine ⟨119323887811671612753444631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159098517082228817004592841 119323887811671612753444631)
  ·
    refine ⟨178985831717507419130166947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119323887811671612753444631 178985831717507419130166947)
    ·
      refine ⟨268478747576261128695250421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178985831717507419130166947 268478747576261128695250421)
      ·
        refine ⟨25169882585274480815179727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268478747576261128695250421 25169882585274480815179727)
        ·
          refine ⟨37754823877911721222769591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25169882585274480815179727 37754823877911721222769591)
          ·
            refine ⟨56632235816867581834154387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37754823877911721222769591 56632235816867581834154387)
            ·
              refine ⟨84948353725301372751231581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56632235816867581834154387 84948353725301372751231581)
              ·
                refine ⟨31855632646988014781711843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84948353725301372751231581 31855632646988014781711843)
                ·
                  refine ⟨47783448970482022172567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31855632646988014781711843 47783448970482022172567765)
                  ·
                    refine ⟨1119924585245672394669557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47783448970482022172567765 1119924585245672394669557)
                    ·
                      rfl

theorem cell23_6543136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_6543136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543136 prefixEnd_6543136 := by exact prefixLift 6543136
  have htrace : WordTrace (prefixWord ++ tailWord_6543136) baseStart_6543136 baseEnd_6543136 := by
    simpa [prefixWord, tailWord_6543136, baseEnd_6543136] using wordTrace_append hprefix tailTrace_6543136
  have hstable : (prefixWord ++ tailWord_6543136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543136).length < 2 ^ (prefixWord ++ tailWord_6543136).sum := by decide
  have hdescent : baseEnd_6543136 < baseStart_6543136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543140 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 5]
def baseStart_6543140 : Nat := 118140960795 + 6543140 * 2 ^ 59
def prefixEnd_6543140 : Nat := 4983230072969 + 3 ^ 40 * 6543140 * 2
def baseEnd_6543140 : Nat := 373308423295515018706517

theorem tailTrace_6543140 : CollatzResearch.WordTrace tailWord_6543140 prefixEnd_6543140 373308423295515018706517 := by
  unfold tailWord_6543140
  simp only [CollatzResearch.WordTrace]
  refine ⟨119323960757664367095017437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159098614343552489460023249 119323960757664367095017437)
  ·
    refine ⟨44746485284124137660631539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119323960757664367095017437 44746485284124137660631539)
    ·
      refine ⟨67119727926186206490947309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44746485284124137660631539 67119727926186206490947309)
      ·
        refine ⟨25169897972319827434105241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67119727926186206490947309 25169897972319827434105241)
        ·
          refine ⟨18877423479239870575578931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25169897972319827434105241 18877423479239870575578931)
          ·
            refine ⟨28316135218859805863368397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18877423479239870575578931 28316135218859805863368397)
            ·
              refine ⟨10618550707072427198763149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28316135218859805863368397 10618550707072427198763149)
              ·
                refine ⟨3981956515152160199536181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10618550707072427198763149 3981956515152160199536181)
                ·
                  refine ⟨373308423295515018706517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981956515152160199536181 373308423295515018706517)
                  ·
                    rfl

theorem cell23_6543140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_6543140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543140 prefixEnd_6543140 := by exact prefixLift 6543140
  have htrace : WordTrace (prefixWord ++ tailWord_6543140) baseStart_6543140 baseEnd_6543140 := by
    simpa [prefixWord, tailWord_6543140, baseEnd_6543140] using wordTrace_append hprefix tailTrace_6543140
  have hstable : (prefixWord ++ tailWord_6543140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543140).length < 2 ^ (prefixWord ++ tailWord_6543140).sum := by decide
  have hdescent : baseEnd_6543140 < baseStart_6543140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543153 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_6543153 : Nat := 118140960795 + 6543153 * 2 ^ 59
def prefixEnd_6543153 : Nat := 4983230072969 + 3 ^ 40 * 6543153 * 2
def baseEnd_6543153 : Nat := 1119927494969381205832031

theorem tailTrace_6543153 : CollatzResearch.WordTrace tailWord_6543153 prefixEnd_6543153 1119927494969381205832031 := by
  unfold tailWord_6543153
  simp only [CollatzResearch.WordTrace]
  refine ⟨238648395664281637410258113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159098930442854424940172075 238648395664281637410258113)
  ·
    refine ⟨178986296748211228057693585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238648395664281637410258113 178986296748211228057693585)
    ·
      refine ⟨134239722561158421043270189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178986296748211228057693585 134239722561158421043270189)
      ·
        refine ⟨50339895960434407891226321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134239722561158421043270189 50339895960434407891226321)
        ·
          refine ⟨37754921970325805918419741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50339895960434407891226321 37754921970325805918419741)
          ·
            refine ⟨14158095738872177219407403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37754921970325805918419741 14158095738872177219407403)
            ·
              refine ⟨21237143608308265829111105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158095738872177219407403 21237143608308265829111105)
              ·
                refine ⟨15927857706231199371833329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21237143608308265829111105 15927857706231199371833329)
                ·
                  refine ⟨11945893279673399528874997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15927857706231199371833329 11945893279673399528874997)
                  ·
                    refine ⟨1119927494969381205832031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11945893279673399528874997 1119927494969381205832031)
                    ·
                      rfl

theorem cell23_6543153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_6543153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543153 prefixEnd_6543153 := by exact prefixLift 6543153
  have htrace : WordTrace (prefixWord ++ tailWord_6543153) baseStart_6543153 baseEnd_6543153 := by
    simpa [prefixWord, tailWord_6543153, baseEnd_6543153] using wordTrace_append hprefix tailTrace_6543153
  have hstable : (prefixWord ++ tailWord_6543153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543153).length < 2 ^ (prefixWord ++ tailWord_6543153).sum := by decide
  have hdescent : baseEnd_6543153 < baseStart_6543153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543157 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 5]
def baseStart_6543157 : Nat := 118140960795 + 6543157 * 2 ^ 59
def prefixEnd_6543157 : Nat := 4983230072969 + 3 ^ 40 * 6543157 * 2
def baseEnd_6543157 : Nat := 373309393203417955760675

theorem tailTrace_6543157 : CollatzResearch.WordTrace tailWord_6543157 prefixEnd_6543157 373309393203417955760675 := by
  unfold tailWord_6543157
  simp only [CollatzResearch.WordTrace]
  refine ⟨238648541556267146093403725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159099027704178097395602483 238648541556267146093403725)
  ·
    refine ⟨89493203083600179785026397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238648541556267146093403725 89493203083600179785026397)
    ·
      refine ⟨33559951156350067419384899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89493203083600179785026397 33559951156350067419384899)
      ·
        refine ⟨50339926734525101129077349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33559951156350067419384899 50339926734525101129077349)
        ·
          refine ⟨9438736262723456461702003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50339926734525101129077349 9438736262723456461702003)
          ·
            refine ⟨14158104394085184692553005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438736262723456461702003 14158104394085184692553005)
            ·
              refine ⟨5309289147781944259707377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14158104394085184692553005 5309289147781944259707377)
              ·
                refine ⟨3981966860836458194780533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309289147781944259707377 3981966860836458194780533)
                ·
                  refine ⟨373309393203417955760675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981966860836458194780533 373309393203417955760675)
                  ·
                    rfl

theorem cell23_6543157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_6543157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543157 prefixEnd_6543157 := by exact prefixLift 6543157
  have htrace : WordTrace (prefixWord ++ tailWord_6543157) baseStart_6543157 baseEnd_6543157 := by
    simpa [prefixWord, tailWord_6543157, baseEnd_6543157] using wordTrace_append hprefix tailTrace_6543157
  have hstable : (prefixWord ++ tailWord_6543157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543157).length < 2 ^ (prefixWord ++ tailWord_6543157).sum := by decide
  have hdescent : baseEnd_6543157 < baseStart_6543157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543173 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_6543173 : Nat := 118140960795 + 6543173 * 2 ^ 59
def prefixEnd_6543173 : Nat := 4983230072969 + 3 ^ 40 * 6543173 * 2
def baseEnd_6543173 : Nat := 3359792754521233539246001

theorem tailTrace_6543173 : CollatzResearch.WordTrace tailWord_6543173 prefixEnd_6543173 3359792754521233539246001 := by
  unfold tailWord_6543173
  simp only [CollatzResearch.WordTrace]
  refine ⟨238649125124209180825986173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159099416749472787217324115 238649125124209180825986173)
  ·
    refine ⟨89493421921578442809744815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238649125124209180825986173 89493421921578442809744815)
    ·
      refine ⟨134240132882367664214617223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89493421921578442809744815 134240132882367664214617223)
      ·
        refine ⟨201360199323551496321925835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134240132882367664214617223 201360199323551496321925835)
        ·
          refine ⟨302040298985327244482888753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201360199323551496321925835 302040298985327244482888753)
          ·
            refine ⟨226530224238995433362166565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302040298985327244482888753 226530224238995433362166565)
            ·
              refine ⟨42474417044811643755406231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226530224238995433362166565 42474417044811643755406231)
              ·
                refine ⟨63711625567217465633109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42474417044811643755406231 63711625567217465633109347)
                ·
                  refine ⟨95567438350826198449664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63711625567217465633109347 95567438350826198449664021)
                  ·
                    refine ⟨4479723672694978052328001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95567438350826198449664021 4479723672694978052328001)
                    ·
                      refine ⟨3359792754521233539246001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4479723672694978052328001 3359792754521233539246001)
                      ·
                        rfl

theorem cell23_6543173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_6543173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543173 prefixEnd_6543173 := by exact prefixLift 6543173
  have htrace : WordTrace (prefixWord ++ tailWord_6543173) baseStart_6543173 baseEnd_6543173 := by
    simpa [prefixWord, tailWord_6543173, baseEnd_6543173] using wordTrace_append hprefix tailTrace_6543173
  have hstable : (prefixWord ++ tailWord_6543173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543173).length < 2 ^ (prefixWord ++ tailWord_6543173).sum := by decide
  have hdescent : baseEnd_6543173 < baseStart_6543173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543213 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 6]
def baseStart_6543213 : Nat := 118140960795 + 6543213 * 2 ^ 59
def prefixEnd_6543213 : Nat := 4983230072969 + 3 ^ 40 * 6543213 * 2
def baseEnd_6543213 : Nat := 373312588194157042527313

theorem tailTrace_6543213 : CollatzResearch.WordTrace tailWord_6543213 prefixEnd_6543213 373312588194157042527313 := by
  unfold tailWord_6543213
  simp only [CollatzResearch.WordTrace]
  refine ⟨238650584044064267657442293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159100389362709511771628195 238650584044064267657442293)
  ·
    refine ⟨22373492254131025092885215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238650584044064267657442293 22373492254131025092885215)
    ·
      refine ⟨33560238381196537639327823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22373492254131025092885215 33560238381196537639327823)
      ·
        refine ⟨50340357571794806458991735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33560238381196537639327823 50340357571794806458991735)
        ·
          refine ⟨75510536357692209688487603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50340357571794806458991735 75510536357692209688487603)
          ·
            refine ⟨113265804536538314532731405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75510536357692209688487603 113265804536538314532731405)
            ·
              refine ⟨42474676701201867949774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113265804536538314532731405 42474676701201867949774277)
              ·
                refine ⟨7964001881475350240582677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42474676701201867949774277 7964001881475350240582677)
                ·
                  refine ⟨373312588194157042527313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7964001881475350240582677 373312588194157042527313)
                  ·
                    rfl

theorem cell23_6543213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_6543213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543213 prefixEnd_6543213 := by exact prefixLift 6543213
  have htrace : WordTrace (prefixWord ++ tailWord_6543213) baseStart_6543213 baseEnd_6543213 := by
    simpa [prefixWord, tailWord_6543213, baseEnd_6543213] using wordTrace_append hprefix tailTrace_6543213
  have hstable : (prefixWord ++ tailWord_6543213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543213).length < 2 ^ (prefixWord ++ tailWord_6543213).sum := by decide
  have hdescent : baseEnd_6543213 < baseStart_6543213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543216 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_6543216 : Nat := 118140960795 + 6543216 * 2 ^ 59
def prefixEnd_6543216 : Nat := 4983230072969 + 3 ^ 40 * 6543216 * 2
def baseEnd_6543216 : Nat := 3359814834189376871008303

theorem tailTrace_6543216 : CollatzResearch.WordTrace tailWord_6543216 prefixEnd_6543216 3359814834189376871008303 := by
  unfold tailWord_6543216
  simp only [CollatzResearch.WordTrace]
  refine ⟨119325346731526699584900751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159100462308702266113201001 119325346731526699584900751)
  ·
    refine ⟨178988020097290049377351127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119325346731526699584900751 178988020097290049377351127)
    ·
      refine ⟨268482030145935074066026691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178988020097290049377351127 268482030145935074066026691)
      ·
        refine ⟨402723045218902611099040037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268482030145935074066026691 402723045218902611099040037)
        ·
          refine ⟨75510570978544239581070007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402723045218902611099040037 75510570978544239581070007)
          ·
            refine ⟨113265856467816359371605011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75510570978544239581070007 113265856467816359371605011)
            ·
              refine ⟨169898784701724539057407517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113265856467816359371605011 169898784701724539057407517)
              ·
                refine ⟨63712044263146702146527819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169898784701724539057407517 63712044263146702146527819)
                ·
                  refine ⟨95568066394720053219791729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63712044263146702146527819 95568066394720053219791729)
                  ·
                    refine ⟨71676049796040039914843797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95568066394720053219791729 71676049796040039914843797)
                    ·
                      refine ⟨3359814834189376871008303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71676049796040039914843797 3359814834189376871008303)
                      ·
                        rfl

theorem cell23_6543216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_6543216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543216 prefixEnd_6543216 := by exact prefixLift 6543216
  have htrace : WordTrace (prefixWord ++ tailWord_6543216) baseStart_6543216 baseEnd_6543216 := by
    simpa [prefixWord, tailWord_6543216, baseEnd_6543216] using wordTrace_append hprefix tailTrace_6543216
  have hstable : (prefixWord ++ tailWord_6543216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543216).length < 2 ^ (prefixWord ++ tailWord_6543216).sum := by decide
  have hdescent : baseEnd_6543216 < baseStart_6543216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543243 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 1, 5]
def baseStart_6543243 : Nat := 118140960795 + 6543243 * 2 ^ 59
def prefixEnd_6543243 : Nat := 4983230072969 + 3 ^ 40 * 6543243 * 2
def baseEnd_6543243 : Nat := 1119942899389016088456893

theorem tailTrace_6543243 : CollatzResearch.WordTrace tailWord_6543243 prefixEnd_6543243 1119942899389016088456893 := by
  unfold tailWord_6543243
  simp only [CollatzResearch.WordTrace]
  refine ⟨238651678233955582781034383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159101118822637055187356255 238651678233955582781034383)
  ·
    refine ⟨357977517350933374171551575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238651678233955582781034383 357977517350933374171551575)
    ·
      refine ⟨536966276026400061257327363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357977517350933374171551575 536966276026400061257327363)
      ·
        refine ⟨805449414039600091885991045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536966276026400061257327363 805449414039600091885991045)
        ·
          refine ⟨151021765132425017228623321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 805449414039600091885991045 151021765132425017228623321)
          ·
            refine ⟨113266323849318762921467491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151021765132425017228623321 113266323849318762921467491)
            ·
              refine ⟨169899485773978144382201237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113266323849318762921467491 169899485773978144382201237)
              ·
                refine ⟨7964038395655225517915683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169899485773978144382201237 7964038395655225517915683)
                ·
                  refine ⟨11946057593482838276873525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964038395655225517915683 11946057593482838276873525)
                  ·
                    refine ⟨1119942899389016088456893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11946057593482838276873525 1119942899389016088456893)
                    ·
                      rfl

theorem cell23_6543243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 5].length) (baseStart_6543243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543243 prefixEnd_6543243 := by exact prefixLift 6543243
  have htrace : WordTrace (prefixWord ++ tailWord_6543243) baseStart_6543243 baseEnd_6543243 := by
    simpa [prefixWord, tailWord_6543243, baseEnd_6543243] using wordTrace_append hprefix tailTrace_6543243
  have hstable : (prefixWord ++ tailWord_6543243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543243).length < 2 ^ (prefixWord ++ tailWord_6543243).sum := by decide
  have hdescent : baseEnd_6543243 < baseStart_6543243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543257 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 1, 1, 3]
def baseStart_6543257 : Nat := 118140960795 + 6543257 * 2 ^ 59
def prefixEnd_6543257 : Nat := 4983230072969 + 3 ^ 40 * 6543257 * 2
def baseEnd_6543257 : Nat := 3359835886896211210595615

theorem tailTrace_6543257 : CollatzResearch.WordTrace tailWord_6543257 prefixEnd_6543257 3359835886896211210595615 := by
  unfold tailWord_6543257
  simp only [CollatzResearch.WordTrace]
  refine ⟨238652188855904863172044025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159101459237269908781362683 238652188855904863172044025)
  ·
    refine ⟨178989141641928647379033019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238652188855904863172044025 178989141641928647379033019)
    ·
      refine ⟨268483712462892971068549529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178989141641928647379033019 268483712462892971068549529)
      ·
        refine ⟨201362784347169728301412147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268483712462892971068549529 201362784347169728301412147)
        ·
          refine ⟨302044176520754592452118221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201362784347169728301412147 302044176520754592452118221)
          ·
            refine ⟨113266566195282972169544333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302044176520754592452118221 113266566195282972169544333)
            ·
              refine ⟨42474962323231114563579125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113266566195282972169544333 42474962323231114563579125)
              ·
                refine ⟨3982027717802916990335543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42474962323231114563579125 3982027717802916990335543)
                ·
                  refine ⟨5973041576704375485503315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982027717802916990335543 5973041576704375485503315)
                  ·
                    refine ⟨8959562365056563228254973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973041576704375485503315 8959562365056563228254973)
                    ·
                      refine ⟨3359835886896211210595615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959562365056563228254973 3359835886896211210595615)
                      ·
                        rfl

theorem cell23_6543257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_6543257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543257 prefixEnd_6543257 := by exact prefixLift 6543257
  have htrace : WordTrace (prefixWord ++ tailWord_6543257) baseStart_6543257 baseEnd_6543257 := by
    simpa [prefixWord, tailWord_6543257, baseEnd_6543257] using wordTrace_append hprefix tailTrace_6543257
  have hstable : (prefixWord ++ tailWord_6543257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543257).length < 2 ^ (prefixWord ++ tailWord_6543257).sum := by decide
  have hdescent : baseEnd_6543257 < baseStart_6543257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543283 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_6543283 : Nat := 118140960795 + 6543283 * 2 ^ 59
def prefixEnd_6543283 : Nat := 4983230072969 + 3 ^ 40 * 6543283 * 2
def baseEnd_6543283 : Nat := 3359849237393228108870495

theorem tailTrace_6543283 : CollatzResearch.WordTrace tailWord_6543283 prefixEnd_6543283 3359849237393228108870495 := by
  unfold tailWord_6543283
  simp only [CollatzResearch.WordTrace]
  refine ⟨238653137153810669612490503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159102091435873779741660335 238653137153810669612490503)
  ·
    refine ⟨357979705730716004418735755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238653137153810669612490503 357979705730716004418735755)
    ·
      refine ⟨536969558596074006628103633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357979705730716004418735755 536969558596074006628103633)
      ·
        refine ⟨402727168947055504971077725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536969558596074006628103633 402727168947055504971077725)
        ·
          refine ⟨151022688355145814364154147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402727168947055504971077725 151022688355145814364154147)
          ·
            refine ⟨226534032532718721546231221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151022688355145814364154147 226534032532718721546231221)
            ·
              refine ⟨21237565549942380144959177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226534032532718721546231221 21237565549942380144959177)
              ·
                refine ⟨15928174162456785108719383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21237565549942380144959177 15928174162456785108719383)
                ·
                  refine ⟨23892261243685177663079075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15928174162456785108719383 23892261243685177663079075)
                  ·
                    refine ⟨35838391865527766494618613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23892261243685177663079075 35838391865527766494618613)
                    ·
                      refine ⟨3359849237393228108870495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35838391865527766494618613 3359849237393228108870495)
                      ·
                        rfl

theorem cell23_6543283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_6543283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543283 prefixEnd_6543283 := by exact prefixLift 6543283
  have htrace : WordTrace (prefixWord ++ tailWord_6543283) baseStart_6543283 baseEnd_6543283 := by
    simpa [prefixWord, tailWord_6543283, baseEnd_6543283] using wordTrace_append hprefix tailTrace_6543283
  have hstable : (prefixWord ++ tailWord_6543283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543283).length < 2 ^ (prefixWord ++ tailWord_6543283).sum := by decide
  have hdescent : baseEnd_6543283 < baseStart_6543283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543317 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6543317 : Nat := 118140960795 + 6543317 * 2 ^ 59
def prefixEnd_6543317 : Nat := 4983230072969 + 3 ^ 40 * 6543317 * 2
def baseEnd_6543317 : Nat := 3359866695735480975845339

theorem tailTrace_6543317 : CollatzResearch.WordTrace tailWord_6543317 prefixEnd_6543317 3359866695735480975845339 := by
  unfold tailWord_6543317
  simp only [CollatzResearch.WordTrace]
  refine ⟨238654377235687493419228205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159102918157124995612818803 238654377235687493419228205)
  ·
    refine ⟨89495391463382810032210577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238654377235687493419228205 89495391463382810032210577)
    ·
      refine ⟨67121543597537107524157933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89495391463382810032210577 67121543597537107524157933)
      ·
        refine ⟨25170578849076415321559225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67121543597537107524157933 25170578849076415321559225)
        ·
          refine ⟨18877934136807311491169419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25170578849076415321559225 18877934136807311491169419)
          ·
            refine ⟨28316901205210967236754129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18877934136807311491169419 28316901205210967236754129)
            ·
              refine ⟨21237675903908225427565597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28316901205210967236754129 21237675903908225427565597)
              ·
                refine ⟨7964128463965584535337099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21237675903908225427565597 7964128463965584535337099)
                ·
                  refine ⟨11946192695948376803005649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964128463965584535337099 11946192695948376803005649)
                  ·
                    refine ⟨8959644521961282602254237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11946192695948376803005649 8959644521961282602254237)
                    ·
                      refine ⟨3359866695735480975845339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959644521961282602254237 3359866695735480975845339)
                      ·
                        rfl

theorem cell23_6543317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6543317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543317 prefixEnd_6543317 := by exact prefixLift 6543317
  have htrace : WordTrace (prefixWord ++ tailWord_6543317) baseStart_6543317 baseEnd_6543317 := by
    simpa [prefixWord, tailWord_6543317, baseEnd_6543317] using wordTrace_append hprefix tailTrace_6543317
  have hstable : (prefixWord ++ tailWord_6543317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543317).length < 2 ^ (prefixWord ++ tailWord_6543317).sum := by decide
  have hdescent : baseEnd_6543317 < baseStart_6543317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543364 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6543364 : Nat := 118140960795 + 6543364 * 2 ^ 59
def prefixEnd_6543364 : Nat := 4983230072969 + 3 ^ 40 * 6543364 * 2
def baseEnd_6543364 : Nat := 3359890829326242291957623

theorem tailTrace_6543364 : CollatzResearch.WordTrace tailWord_6543364 prefixEnd_6543364 3359890829326242291957623 := by
  unfold tailWord_6543364
  simp only [CollatzResearch.WordTrace]
  refine ⟨119328045733258610223094573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159104060977678146964126097 119328045733258610223094573)
  ·
    refine ⟨44748017149971978833660465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119328045733258610223094573 44748017149971978833660465)
    ·
      refine ⟨33561012862478984125245349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44748017149971978833660465 33561012862478984125245349)
      ·
        refine ⟨6292689911714809523483503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33561012862478984125245349 6292689911714809523483503)
        ·
          refine ⟨9439034867572214285225255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292689911714809523483503 9439034867572214285225255)
          ·
            refine ⟨14158552301358321427837883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9439034867572214285225255 14158552301358321427837883)
            ·
              refine ⟨21237828452037482141756825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158552301358321427837883 21237828452037482141756825)
              ·
                refine ⟨15928371339028111606317619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21237828452037482141756825 15928371339028111606317619)
                ·
                  refine ⟨23892557008542167409476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15928371339028111606317619 23892557008542167409476429)
                  ·
                    refine ⟨8959708878203312778553661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23892557008542167409476429 8959708878203312778553661)
                    ·
                      refine ⟨3359890829326242291957623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959708878203312778553661 3359890829326242291957623)
                      ·
                        rfl

theorem cell23_6543364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6543364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543364 prefixEnd_6543364 := by exact prefixLift 6543364
  have htrace : WordTrace (prefixWord ++ tailWord_6543364) baseStart_6543364 baseEnd_6543364 := by
    simpa [prefixWord, tailWord_6543364, baseEnd_6543364] using wordTrace_append hprefix tailTrace_6543364
  have hstable : (prefixWord ++ tailWord_6543364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543364).length < 2 ^ (prefixWord ++ tailWord_6543364).sum := by decide
  have hdescent : baseEnd_6543364 < baseStart_6543364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543410 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_6543410 : Nat := 118140960795 + 6543410 * 2 ^ 59
def prefixEnd_6543410 : Nat := 4983230072969 + 3 ^ 40 * 6543410 * 2
def baseEnd_6543410 : Nat := 373323827715149901331379

theorem tailTrace_6543410 : CollatzResearch.WordTrace tailWord_6543410 prefixEnd_6543410 373323827715149901331379 := by
  unfold tailWord_6543410
  simp only [CollatzResearch.WordTrace]
  refine ⟨59664442306087642575590921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159105179482900380201575789 59664442306087642575590921)
  ·
    refine ⟨44748331729565731931693191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59664442306087642575590921 44748331729565731931693191)
    ·
      refine ⟨67122497594348597897539787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44748331729565731931693191 67122497594348597897539787)
      ·
        refine ⟨100683746391522896846309681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67122497594348597897539787 100683746391522896846309681)
        ·
          refine ⟨75512809793642172634732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100683746391522896846309681 75512809793642172634732261)
          ·
            refine ⟨14158651836307907369012299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75512809793642172634732261 14158651836307907369012299)
            ·
              refine ⟨21237977754461861053518449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158651836307907369012299 21237977754461861053518449)
              ·
                refine ⟨15928483315846395790138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21237977754461861053518449 15928483315846395790138837)
                ·
                  refine ⟨373323827715149901331379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15928483315846395790138837 373323827715149901331379)
                  ·
                    rfl

theorem cell23_6543410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_6543410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543410 prefixEnd_6543410 := by exact prefixLift 6543410
  have htrace : WordTrace (prefixWord ++ tailWord_6543410) baseStart_6543410 baseEnd_6543410 := by
    simpa [prefixWord, tailWord_6543410, baseEnd_6543410] using wordTrace_append hprefix tailTrace_6543410
  have hstable : (prefixWord ++ tailWord_6543410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543410).length < 2 ^ (prefixWord ++ tailWord_6543410).sum := by decide
  have hdescent : baseEnd_6543410 < baseStart_6543410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543420 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_6543420 : Nat := 118140960795 + 6543420 * 2 ^ 59
def prefixEnd_6543420 : Nat := 4983230072969 + 3 ^ 40 * 6543420 * 2
def baseEnd_6543420 : Nat := 3359919584242894072857365

theorem tailTrace_6543420 : CollatzResearch.WordTrace tailWord_6543420 prefixEnd_6543420 3359919584242894072857365 := by
  unfold tailWord_6543420
  simp only [CollatzResearch.WordTrace]
  refine ⟨119329066977157171005113857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159105422636209561340151809 119329066977157171005113857)
  ·
    refine ⟨89496800232867878253835393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119329066977157171005113857 89496800232867878253835393)
    ·
      refine ⟨67122600174650908690376545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89496800232867878253835393 67122600174650908690376545)
      ·
        refine ⟨50341950130988181517782409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67122600174650908690376545 50341950130988181517782409)
        ·
          refine ⟨37756462598241136138336807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50341950130988181517782409 37756462598241136138336807)
          ·
            refine ⟨56634693897361704207505211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37756462598241136138336807 56634693897361704207505211)
            ·
              refine ⟨84952040846042556311257817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56634693897361704207505211 84952040846042556311257817)
              ·
                refine ⟨63714030634531917233443363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84952040846042556311257817 63714030634531917233443363)
                ·
                  refine ⟨95571045951797875850165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63714030634531917233443363 95571045951797875850165045)
                  ·
                    refine ⟨8959785557981050860952973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95571045951797875850165045 8959785557981050860952973)
                    ·
                      refine ⟨3359919584242894072857365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959785557981050860952973 3359919584242894072857365)
                      ·
                        rfl

theorem cell23_6543420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_6543420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543420 prefixEnd_6543420 := by exact prefixLift 6543420
  have htrace : WordTrace (prefixWord ++ tailWord_6543420) baseStart_6543420 baseEnd_6543420 := by
    simpa [prefixWord, tailWord_6543420, baseEnd_6543420] using wordTrace_append hprefix tailTrace_6543420
  have hstable : (prefixWord ++ tailWord_6543420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543420).length < 2 ^ (prefixWord ++ tailWord_6543420).sum := by decide
  have hdescent : baseEnd_6543420 < baseStart_6543420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543437 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6543437 : Nat := 118140960795 + 6543437 * 2 ^ 59
def prefixEnd_6543437 : Nat := 4983230072969 + 3 ^ 40 * 6543437 * 2
def baseEnd_6543437 : Nat := 3359928313414020506344787

theorem tailTrace_6543437 : CollatzResearch.WordTrace tailWord_6543437 prefixEnd_6543437 3359928313414020506344787 := by
  unfold tailWord_6543437
  simp only [CollatzResearch.WordTrace]
  refine ⟨238658753995252753913596565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159105835996835169275731043 238658753995252753913596565)
  ·
    refine ⟨11187129093527472839699839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238658753995252753913596565 11187129093527472839699839)
    ·
      refine ⟨16780693640291209259549759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187129093527472839699839 16780693640291209259549759)
      ·
        refine ⟨25171040460436813889324639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780693640291209259549759 25171040460436813889324639)
        ·
          refine ⟨37756560690655220833986959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25171040460436813889324639 37756560690655220833986959)
          ·
            refine ⟨56634841035982831250980439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37756560690655220833986959 56634841035982831250980439)
            ·
              refine ⟨84952261553974246876470659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56634841035982831250980439 84952261553974246876470659)
              ·
                refine ⟨127428392330961370314705989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84952261553974246876470659 127428392330961370314705989)
                ·
                  refine ⟨23892823562055256934007373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127428392330961370314705989 23892823562055256934007373)
                  ·
                    refine ⟨8959808835770721350252765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23892823562055256934007373 8959808835770721350252765)
                    ·
                      refine ⟨3359928313414020506344787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959808835770721350252765 3359928313414020506344787)
                      ·
                        rfl

theorem cell23_6543437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6543437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543437 prefixEnd_6543437 := by exact prefixLift 6543437
  have htrace : WordTrace (prefixWord ++ tailWord_6543437) baseStart_6543437 baseEnd_6543437 := by
    simpa [prefixWord, tailWord_6543437, baseEnd_6543437] using wordTrace_append hprefix tailTrace_6543437
  have hstable : (prefixWord ++ tailWord_6543437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543437).length < 2 ^ (prefixWord ++ tailWord_6543437).sum := by decide
  have hdescent : baseEnd_6543437 < baseStart_6543437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543460 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_6543460 : Nat := 118140960795 + 6543460 * 2 ^ 59
def prefixEnd_6543460 : Nat := 4983230072969 + 3 ^ 40 * 6543460 * 2
def baseEnd_6543460 : Nat := 3359940123469073916357181

theorem tailTrace_6543460 : CollatzResearch.WordTrace tailWord_6543460 prefixEnd_6543460 3359940123469073916357181 := by
  unfold tailWord_6543460
  simp only [CollatzResearch.WordTrace]
  refine ⟨119329796437084714420841917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159106395249446285894455889 119329796437084714420841917)
  ·
    refine ⟨44748673663906767907815719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119329796437084714420841917 44748673663906767907815719)
    ·
      refine ⟨67123010495860151861723579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44748673663906767907815719 67123010495860151861723579)
      ·
        refine ⟨100684515743790227792585369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67123010495860151861723579 100684515743790227792585369)
        ·
          refine ⟨75513386807842670844439027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100684515743790227792585369 75513386807842670844439027)
          ·
            refine ⟨113270080211764006266658541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75513386807842670844439027 113270080211764006266658541)
            ·
              refine ⟨42476280079411502349996953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113270080211764006266658541 42476280079411502349996953)
              ·
                refine ⟨31857210059558626762497715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42476280079411502349996953 31857210059558626762497715)
                ·
                  refine ⟨47785815089337940143746573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31857210059558626762497715 47785815089337940143746573)
                  ·
                    refine ⟨17919680658501727553904965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47785815089337940143746573 17919680658501727553904965)
                    ·
                      refine ⟨3359940123469073916357181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17919680658501727553904965 3359940123469073916357181)
                      ·
                        rfl

theorem cell23_6543460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_6543460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543460 prefixEnd_6543460 := by exact prefixLift 6543460
  have htrace : WordTrace (prefixWord ++ tailWord_6543460) baseStart_6543460 baseEnd_6543460 := by
    simpa [prefixWord, tailWord_6543460, baseEnd_6543460] using wordTrace_append hprefix tailTrace_6543460
  have hstable : (prefixWord ++ tailWord_6543460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543460).length < 2 ^ (prefixWord ++ tailWord_6543460).sum := by decide
  have hdescent : baseEnd_6543460 < baseStart_6543460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543470 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6543470 : Nat := 118140960795 + 6543470 * 2 ^ 59
def prefixEnd_6543470 : Nat := 4983230072969 + 3 ^ 40 * 6543470 * 2
def baseEnd_6543470 : Nat := 1119981752758539625744045

theorem tailTrace_6543470 : CollatzResearch.WordTrace tailWord_6543470 prefixEnd_6543470 1119981752758539625744045 := by
  unfold tailWord_6543470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29832494700516650068693483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159106638402755467033031909 29832494700516650068693483)
  ·
    refine ⟨44748742050774975103040225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29832494700516650068693483 44748742050774975103040225)
    ·
      refine ⟨33561556538081231327280169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44748742050774975103040225 33561556538081231327280169)
      ·
        refine ⟨25171167403560923495460127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33561556538081231327280169 25171167403560923495460127)
        ·
          refine ⟨37756751105341385243190191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25171167403560923495460127 37756751105341385243190191)
          ·
            refine ⟨56635126658012077864785287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37756751105341385243190191 56635126658012077864785287)
            ·
              refine ⟨84952689987018116797177931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56635126658012077864785287 84952689987018116797177931)
              ·
                refine ⟨127429034980527175195766897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84952689987018116797177931 127429034980527175195766897)
                ·
                  refine ⟨95571776235395381396825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127429034980527175195766897 95571776235395381396825173)
                  ·
                    refine ⟨1119981752758539625744045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95571776235395381396825173 1119981752758539625744045)
                    ·
                      rfl

theorem cell23_6543470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6543470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543470 prefixEnd_6543470 := by exact prefixLift 6543470
  have htrace : WordTrace (prefixWord ++ tailWord_6543470) baseStart_6543470 baseEnd_6543470 := by
    simpa [prefixWord, tailWord_6543470, baseEnd_6543470] using wordTrace_append hprefix tailTrace_6543470
  have hstable : (prefixWord ++ tailWord_6543470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543470).length < 2 ^ (prefixWord ++ tailWord_6543470).sum := by decide
  have hdescent : baseEnd_6543470 < baseStart_6543470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543497 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_6543497 : Nat := 118140960795 + 6543497 * 2 ^ 59
def prefixEnd_6543497 : Nat := 4983230072969 + 3 ^ 40 * 6543497 * 2
def baseEnd_6543497 : Nat := 3359959122253290271594511

theorem tailTrace_6543497 : CollatzResearch.WordTrace tailWord_6543497 prefixEnd_6543497 3359959122253290271594511 := by
  unfold tailWord_6543497
  simp only [CollatzResearch.WordTrace]
  refine ⟨238660942375035384160780745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159107294916690256107187163 238660942375035384160780745)
  ·
    refine ⟨178995706781276538120585559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238660942375035384160780745 178995706781276538120585559)
    ·
      refine ⟨268493560171914807180878339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178995706781276538120585559 268493560171914807180878339)
      ·
        refine ⟨402740340257872210771317509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268493560171914807180878339 402740340257872210771317509)
        ·
          refine ⟨75513813798351039519622033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402740340257872210771317509 75513813798351039519622033)
          ·
            refine ⟨56635360348763279639716525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75513813798351039519622033 56635360348763279639716525)
            ·
              refine ⟨21238260130786229864893697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56635360348763279639716525 21238260130786229864893697)
              ·
                refine ⟨15928695098089672398670273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21238260130786229864893697 15928695098089672398670273)
                ·
                  refine ⟨11946521323567254299002705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15928695098089672398670273 11946521323567254299002705)
                  ·
                    refine ⟨8959890992675440724252029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11946521323567254299002705 8959890992675440724252029)
                    ·
                      refine ⟨3359959122253290271594511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8959890992675440724252029 3359959122253290271594511)
                      ·
                        rfl

theorem cell23_6543497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_6543497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543497 prefixEnd_6543497 := by exact prefixLift 6543497
  have htrace : WordTrace (prefixWord ++ tailWord_6543497) baseStart_6543497 baseEnd_6543497 := by
    simpa [prefixWord, tailWord_6543497, baseEnd_6543497] using wordTrace_append hprefix tailTrace_6543497
  have hstable : (prefixWord ++ tailWord_6543497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543497).length < 2 ^ (prefixWord ++ tailWord_6543497).sum := by decide
  have hdescent : baseEnd_6543497 < baseStart_6543497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543517 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 6]
def baseStart_6543517 : Nat := 118140960795 + 6543517 * 2 ^ 59
def prefixEnd_6543517 : Nat := 4983230072969 + 3 ^ 40 * 6543517 * 2
def baseEnd_6543517 : Nat := 373329932429597799260491

theorem tailTrace_6543517 : CollatzResearch.WordTrace tailWord_6543517 prefixEnd_6543517 373329932429597799260491 := by
  unfold tailWord_6543517
  simp only [CollatzResearch.WordTrace]
  refine ⟨238661671834962927576508805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159107781223308618384339203 238661671834962927576508805)
  ·
    refine ⟨44749063469055548920595401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238661671834962927576508805 44749063469055548920595401)
    ·
      refine ⟨33561797601791661690446551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44749063469055548920595401 33561797601791661690446551)
      ·
        refine ⟨50342696402687492535669827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33561797601791661690446551 50342696402687492535669827)
        ·
          refine ⟨75514044604031238803504741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50342696402687492535669827 75514044604031238803504741)
          ·
            refine ⟨14158883363255857275657139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75514044604031238803504741 14158883363255857275657139)
            ·
              refine ⟨21238325044883785913485709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158883363255857275657139 21238325044883785913485709)
              ·
                refine ⟨7964371891831419717557141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21238325044883785913485709 7964371891831419717557141)
                ·
                  refine ⟨373329932429597799260491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7964371891831419717557141 373329932429597799260491)
                  ·
                    rfl

theorem cell23_6543517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_6543517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543517 prefixEnd_6543517 := by exact prefixLift 6543517
  have htrace : WordTrace (prefixWord ++ tailWord_6543517) baseStart_6543517 baseEnd_6543517 := by
    simpa [prefixWord, tailWord_6543517, baseEnd_6543517] using wordTrace_append hprefix tailTrace_6543517
  have hstable : (prefixWord ++ tailWord_6543517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543517).length < 2 ^ (prefixWord ++ tailWord_6543517).sum := by decide
  have hdescent : baseEnd_6543517 < baseStart_6543517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543560 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_6543560 : Nat := 118140960795 + 6543560 * 2 ^ 59
def prefixEnd_6543560 : Nat := 4983230072969 + 3 ^ 40 * 6543560 * 2
def baseEnd_6543560 : Nat := 1119997157178174508368907

theorem tailTrace_6543560 : CollatzResearch.WordTrace tailWord_6543560 prefixEnd_6543560 1119997157178174508368907 := by
  unfold tailWord_6543560
  simp only [CollatzResearch.WordTrace]
  refine ⟨119331620086903572960162067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159108826782538097280216089 119331620086903572960162067)
  ·
    refine ⟨178997430130355359440243101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119331620086903572960162067 178997430130355359440243101)
    ·
      refine ⟨67124036298883259790091163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178997430130355359440243101 67124036298883259790091163)
      ·
        refine ⟨100686054448324889685136745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67124036298883259790091163 100686054448324889685136745)
        ·
          refine ⟨75514540836243667263852559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100686054448324889685136745 75514540836243667263852559)
          ·
            refine ⟨113271811254365500895778839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75514540836243667263852559 113271811254365500895778839)
            ·
              refine ⟨169907716881548251343668259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113271811254365500895778839 169907716881548251343668259)
              ·
                refine ⟨254861575322322377015502389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169907716881548251343668259 254861575322322377015502389)
                ·
                  refine ⟨23893272686467722845203349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254861575322322377015502389 23893272686467722845203349)
                  ·
                    refine ⟨1119997157178174508368907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23893272686467722845203349 1119997157178174508368907)
                    ·
                      rfl

theorem cell23_6543560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_6543560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543560 prefixEnd_6543560 := by exact prefixLift 6543560
  have htrace : WordTrace (prefixWord ++ tailWord_6543560) baseStart_6543560 baseEnd_6543560 := by
    simpa [prefixWord, tailWord_6543560, baseEnd_6543560] using wordTrace_append hprefix tailTrace_6543560
  have hstable : (prefixWord ++ tailWord_6543560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543560).length < 2 ^ (prefixWord ++ tailWord_6543560).sum := by decide
  have hdescent : baseEnd_6543560 < baseStart_6543560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543618 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_6543618 : Nat := 118140960795 + 6543618 * 2 ^ 59
def prefixEnd_6543618 : Nat := 4983230072969 + 3 ^ 40 * 6543618 * 2
def baseEnd_6543618 : Nat := 3360021253412484298181455

theorem tailTrace_6543618 : CollatzResearch.WordTrace tailWord_6543618 prefixEnd_6543618 3360021253412484298181455 := by
  unfold tailWord_6543618
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666338901899255456483877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159110237071731347883957005 59666338901899255456483877)
  ·
    refine ⟨11187438544106110398090727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59666338901899255456483877 11187438544106110398090727)
    ·
      refine ⟨16781157816159165597136091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187438544106110398090727 16781157816159165597136091)
      ·
        refine ⟨25171736724238748395704137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781157816159165597136091 25171736724238748395704137)
        ·
          refine ⟨18878802543179061296778103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25171736724238748395704137 18878802543179061296778103)
          ·
            refine ⟨28318203814768591945167155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18878802543179061296778103 28318203814768591945167155)
            ·
              refine ⟨42477305722152887917750733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28318203814768591945167155 42477305722152887917750733)
              ·
                refine ⟨15928989645807332969156525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42477305722152887917750733 15928989645807332969156525)
                ·
                  refine ⟨5973371117177749863433697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15928989645807332969156525 5973371117177749863433697)
                  ·
                    refine ⟨4480028337883312397575273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5973371117177749863433697 4480028337883312397575273)
                    ·
                      refine ⟨3360021253412484298181455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480028337883312397575273 3360021253412484298181455)
                      ·
                        rfl

theorem cell23_6543618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_6543618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543618 prefixEnd_6543618 := by exact prefixLift 6543618
  have htrace : WordTrace (prefixWord ++ tailWord_6543618) baseStart_6543618 baseEnd_6543618 := by
    simpa [prefixWord, tailWord_6543618, baseEnd_6543618] using wordTrace_append hprefix tailTrace_6543618
  have hstable : (prefixWord ++ tailWord_6543618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543618).length < 2 ^ (prefixWord ++ tailWord_6543618).sum := by decide
  have hdescent : baseEnd_6543618 < baseStart_6543618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543647 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_6543647 : Nat := 118140960795 + 6543647 * 2 ^ 59
def prefixEnd_6543647 : Nat := 4983230072969 + 3 ^ 40 * 6543647 * 2
def baseEnd_6543647 : Nat := 3360036144351464684718821

theorem tailTrace_6543647 : CollatzResearch.WordTrace tailWord_6543647 prefixEnd_6543647 3360036144351464684718821 := by
  unfold tailWord_6543647
  simp only [CollatzResearch.WordTrace]
  refine ⟨238666413324491959778741195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159110942216327973185827463 238666413324491959778741195)
  ·
    refine ⟨357999619986737939668111793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238666413324491959778741195 357999619986737939668111793)
    ·
      refine ⟨268499714990053454751083845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357999619986737939668111793 268499714990053454751083845)
      ·
        refine ⟨50343696560635022765828221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268499714990053454751083845 50343696560635022765828221)
        ·
          refine ⟨18878886210238133537185583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50343696560635022765828221 18878886210238133537185583)
          ·
            refine ⟨28318329315357200305778375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18878886210238133537185583 28318329315357200305778375)
            ·
              refine ⟨42477493973035800458667563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28318329315357200305778375 42477493973035800458667563)
              ·
                refine ⟨63716240959553700688001345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42477493973035800458667563 63716240959553700688001345)
                ·
                  refine ⟨47787180719665275516001009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63716240959553700688001345 47787180719665275516001009)
                  ·
                    refine ⟨35840385539748956637000757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47787180719665275516001009 35840385539748956637000757)
                    ·
                      refine ⟨3360036144351464684718821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35840385539748956637000757 3360036144351464684718821)
                      ·
                        rfl

theorem cell23_6543647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_6543647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543647 prefixEnd_6543647 := by exact prefixLift 6543647
  have htrace : WordTrace (prefixWord ++ tailWord_6543647) baseStart_6543647 baseEnd_6543647 := by
    simpa [prefixWord, tailWord_6543647, baseEnd_6543647] using wordTrace_append hprefix tailTrace_6543647
  have hstable : (prefixWord ++ tailWord_6543647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543647).length < 2 ^ (prefixWord ++ tailWord_6543647).sum := by decide
  have hdescent : baseEnd_6543647 < baseStart_6543647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543687 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_6543687 : Nat := 118140960795 + 6543687 * 2 ^ 59
def prefixEnd_6543687 : Nat := 4983230072969 + 3 ^ 40 * 6543687 * 2
def baseEnd_6543687 : Nat := 3360056683577644528218637

theorem tailTrace_6543687 : CollatzResearch.WordTrace tailWord_6543687 prefixEnd_6543687 3360056683577644528218637 := by
  unfold tailWord_6543687
  simp only [CollatzResearch.WordTrace]
  refine ⟨238667872244347046610197315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159111914829564697740131543 238667872244347046610197315)
  ·
    refine ⟨358001808366520569915295973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238667872244347046610197315 358001808366520569915295973)
    ·
      refine ⟨67125339068722606859117995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358001808366520569915295973 67125339068722606859117995)
      ·
        refine ⟨100688008603083910288676993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67125339068722606859117995 100688008603083910288676993)
        ·
          refine ⟨75516006452312932716507745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100688008603083910288676993 75516006452312932716507745)
          ·
            refine ⟨56637004839234699537380809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75516006452312932716507745 56637004839234699537380809)
            ·
              refine ⟨42477753629426024653035607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56637004839234699537380809 42477753629426024653035607)
              ·
                refine ⟨63716630444139036979553411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42477753629426024653035607 63716630444139036979553411)
                ·
                  refine ⟨95574945666208555469330117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63716630444139036979553411 95574945666208555469330117)
                  ·
                    refine ⟨17920302312414104150499397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95574945666208555469330117 17920302312414104150499397)
                    ·
                      refine ⟨3360056683577644528218637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17920302312414104150499397 3360056683577644528218637)
                      ·
                        rfl

theorem cell23_6543687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_6543687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543687 prefixEnd_6543687 := by exact prefixLift 6543687
  have htrace : WordTrace (prefixWord ++ tailWord_6543687) baseStart_6543687 baseEnd_6543687 := by
    simpa [prefixWord, tailWord_6543687, baseEnd_6543687] using wordTrace_append hprefix tailTrace_6543687
  have hstable : (prefixWord ++ tailWord_6543687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543687).length < 2 ^ (prefixWord ++ tailWord_6543687).sum := by decide
  have hdescent : baseEnd_6543687 < baseStart_6543687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543727 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 4, 5]
def baseStart_6543727 : Nat := 118140960795 + 6543727 * 2 ^ 59
def prefixEnd_6543727 : Nat := 4983230072969 + 3 ^ 40 * 6543727 * 2
def baseEnd_6543727 : Nat := 1120025740934608123906151

theorem tailTrace_6543727 : CollatzResearch.WordTrace tailWord_6543727 prefixEnd_6543727 1120025740934608123906151 := by
  unfold tailWord_6543727
  simp only [CollatzResearch.WordTrace]
  refine ⟨238669331164202133441653435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159112887442801422294435623 238669331164202133441653435)
  ·
    refine ⟨358003996746303200162480153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238669331164202133441653435 358003996746303200162480153)
    ·
      refine ⟨268502997559727400121860115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358003996746303200162480153 268502997559727400121860115)
      ·
        refine ⟨402754496339591100182790173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268502997559727400121860115 402754496339591100182790173)
        ·
          refine ⟨151032936127346662568546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402754496339591100182790173 151032936127346662568546315)
          ·
            refine ⟨226549404191019993852819473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151032936127346662568546315 226549404191019993852819473)
            ·
              refine ⟨169912053143264995389614605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226549404191019993852819473 169912053143264995389614605)
              ·
                refine ⟨63717019928724373271105477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169912053143264995389614605 63717019928724373271105477)
                ·
                  refine ⟨11946941236635819988332277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63717019928724373271105477 11946941236635819988332277)
                  ·
                    refine ⟨1120025740934608123906151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11946941236635819988332277 1120025740934608123906151)
                    ·
                      rfl

theorem cell23_6543727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_6543727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543727 prefixEnd_6543727 := by exact prefixLift 6543727
  have htrace : WordTrace (prefixWord ++ tailWord_6543727) baseStart_6543727 baseEnd_6543727 := by
    simpa [prefixWord, tailWord_6543727, baseEnd_6543727] using wordTrace_append hprefix tailTrace_6543727
  have hstable : (prefixWord ++ tailWord_6543727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543727).length < 2 ^ (prefixWord ++ tailWord_6543727).sum := by decide
  have hdescent : baseEnd_6543727 < baseStart_6543727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543827 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_6543827 : Nat := 118140960795 + 6543827 * 2 ^ 59
def prefixEnd_6543827 : Nat := 4983230072969 + 3 ^ 40 * 6543827 * 2
def baseEnd_6543827 : Nat := 3360128570869273980467993

theorem tailTrace_6543827 : CollatzResearch.WordTrace tailWord_6543827 prefixEnd_6543827 3360128570869273980467993 := by
  unfold tailWord_6543827
  simp only [CollatzResearch.WordTrace]
  refine ⟨238672978463839850520293735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159115318975893233680195823 238672978463839850520293735)
  ·
    refine ⟨358009467695759775780440603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238672978463839850520293735 358009467695759775780440603)
    ·
      refine ⟨537014201543639663670660905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358009467695759775780440603 537014201543639663670660905)
      ·
        refine ⟨402760651157729747752995679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537014201543639663670660905 402760651157729747752995679)
        ·
          refine ⟨604140976736594621629493519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402760651157729747752995679 604140976736594621629493519)
          ·
            refine ⟨906211465104891932444240279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604140976736594621629493519 906211465104891932444240279)
            ·
              refine ⟨1359317197657337898666360419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906211465104891932444240279 1359317197657337898666360419)
              ·
                refine ⟨2038975796486006847999540629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359317197657337898666360419 2038975796486006847999540629)
                ·
                  refine ⟨95576990460281570999978467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2038975796486006847999540629 95576990460281570999978467)
                  ·
                    refine ⟨143365485690422356499967701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95576990460281570999978467 143365485690422356499967701)
                    ·
                      refine ⟨3360128570869273980467993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143365485690422356499967701 3360128570869273980467993)
                      ·
                        rfl

theorem cell23_6543827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_6543827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543827 prefixEnd_6543827 := by exact prefixLift 6543827
  have htrace : WordTrace (prefixWord ++ tailWord_6543827) baseStart_6543827 baseEnd_6543827 := by
    simpa [prefixWord, tailWord_6543827, baseEnd_6543827] using wordTrace_append hprefix tailTrace_6543827
  have hstable : (prefixWord ++ tailWord_6543827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543827).length < 2 ^ (prefixWord ++ tailWord_6543827).sum := by decide
  have hdescent : baseEnd_6543827 < baseStart_6543827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543842 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6543842 : Nat := 118140960795 + 6543842 * 2 ^ 59
def prefixEnd_6543842 : Nat := 4983230072969 + 3 ^ 40 * 6543842 * 2
def baseEnd_6543842 : Nat := 1120045424359697140593475

theorem tailTrace_6543842 : CollatzResearch.WordTrace tailWord_6543842 prefixEnd_6543842 1120045424359697140593475 := by
  unfold tailWord_6543842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668381389696377020522445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159115683705857005388059853 59668381389696377020522445)
  ·
    refine ⟨22375643021136141382695917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59668381389696377020522445 22375643021136141382695917)
    ·
      refine ⟨8390866132926053018510969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22375643021136141382695917 8390866132926053018510969)
      ·
        refine ⟨6293149599694539763883227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8390866132926053018510969 6293149599694539763883227)
        ·
          refine ⟨9439724399541809645824841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293149599694539763883227 9439724399541809645824841)
          ·
            refine ⟨7079793299656357234368631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439724399541809645824841 7079793299656357234368631)
            ·
              refine ⟨10619689949484535851552947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079793299656357234368631 10619689949484535851552947)
              ·
                refine ⟨15929534924226803777329421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619689949484535851552947 15929534924226803777329421)
                ·
                  refine ⟨5973575596585051416498533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15929534924226803777329421 5973575596585051416498533)
                  ·
                    refine ⟨1120045424359697140593475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5973575596585051416498533 1120045424359697140593475)
                    ·
                      rfl

theorem cell23_6543842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6543842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543842 prefixEnd_6543842 := by exact prefixLift 6543842
  have htrace : WordTrace (prefixWord ++ tailWord_6543842) baseStart_6543842 baseEnd_6543842 := by
    simpa [prefixWord, tailWord_6543842, baseEnd_6543842] using wordTrace_append hprefix tailTrace_6543842
  have hstable : (prefixWord ++ tailWord_6543842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543842).length < 2 ^ (prefixWord ++ tailWord_6543842).sum := by decide
  have hdescent : baseEnd_6543842 < baseStart_6543842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543848 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6543848 : Nat := 118140960795 + 6543848 * 2 ^ 59
def prefixEnd_6543848 : Nat := 4983230072969 + 3 ^ 40 * 6543848 * 2
def baseEnd_6543848 : Nat := 3360139353963018398305397

theorem tailTrace_6543848 : CollatzResearch.WordTrace tailWord_6543848 prefixEnd_6543848 3360139353963018398305397 := by
  unfold tailWord_6543848
  simp only [CollatzResearch.WordTrace]
  refine ⟨119336872198381885553404099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159115829597842514071205465 119336872198381885553404099)
  ·
    refine ⟨179005308297572828330106149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119336872198381885553404099 179005308297572828330106149)
    ·
      refine ⟨33563495305794905311894903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179005308297572828330106149 33563495305794905311894903)
      ·
        refine ⟨50345242958692357967842355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33563495305794905311894903 50345242958692357967842355)
        ·
          refine ⟨75517864438038536951763533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50345242958692357967842355 75517864438038536951763533)
          ·
            refine ⟨28319199164264451356911325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75517864438038536951763533 28319199164264451356911325)
            ·
              refine ⟨10619699686599169258841747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28319199164264451356911325 10619699686599169258841747)
              ·
                refine ⟨15929549529898753888262621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619699686599169258841747 15929549529898753888262621)
                ·
                  refine ⟨5973581073712032708098483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15929549529898753888262621 5973581073712032708098483)
                  ·
                    refine ⟨8960371610568049062147725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973581073712032708098483 8960371610568049062147725)
                    ·
                      refine ⟨3360139353963018398305397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960371610568049062147725 3360139353963018398305397)
                      ·
                        rfl

theorem cell23_6543848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6543848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543848 prefixEnd_6543848 := by exact prefixLift 6543848
  have htrace : WordTrace (prefixWord ++ tailWord_6543848) baseStart_6543848 baseEnd_6543848 := by
    simpa [prefixWord, tailWord_6543848, baseEnd_6543848] using wordTrace_append hprefix tailTrace_6543848
  have hstable : (prefixWord ++ tailWord_6543848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543848).length < 2 ^ (prefixWord ++ tailWord_6543848).sum := by decide
  have hdescent : baseEnd_6543848 < baseStart_6543848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543864 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_6543864 : Nat := 118140960795 + 6543864 * 2 ^ 59
def prefixEnd_6543864 : Nat := 4983230072969 + 3 ^ 40 * 6543864 * 2
def baseEnd_6543864 : Nat := 1120049189884496778568441

theorem tailTrace_6543864 : CollatzResearch.WordTrace tailWord_6543864 prefixEnd_6543864 1120049189884496778568441 := by
  unfold tailWord_6543864
  simp only [CollatzResearch.WordTrace]
  refine ⟨119337163982352902919695323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159116218643137203892927097 119337163982352902919695323)
  ·
    refine ⟨179005745973529354379542985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119337163982352902919695323 179005745973529354379542985)
    ·
      refine ⟨134254309480147015784657239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179005745973529354379542985 134254309480147015784657239)
      ·
        refine ⟨201381464220220523676985859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134254309480147015784657239 201381464220220523676985859)
        ·
          refine ⟨302072196330330785515478789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201381464220220523676985859 302072196330330785515478789)
          ·
            refine ⟨56638536811937022284152273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302072196330330785515478789 56638536811937022284152273)
            ·
              refine ⟨42478902608952766713114205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56638536811937022284152273 42478902608952766713114205)
              ·
                refine ⟨15929588478357287517417827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42478902608952766713114205 15929588478357287517417827)
                ·
                  refine ⟨23894382717535931276126741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15929588478357287517417827 23894382717535931276126741)
                  ·
                    refine ⟨1120049189884496778568441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23894382717535931276126741 1120049189884496778568441)
                    ·
                      rfl

theorem cell23_6543864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_6543864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543864 prefixEnd_6543864 := by exact prefixLift 6543864
  have htrace : WordTrace (prefixWord ++ tailWord_6543864) baseStart_6543864 baseEnd_6543864 := by
    simpa [prefixWord, tailWord_6543864, baseEnd_6543864] using wordTrace_append hprefix tailTrace_6543864
  have hstable : (prefixWord ++ tailWord_6543864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543864).length < 2 ^ (prefixWord ++ tailWord_6543864).sum := by decide
  have hdescent : baseEnd_6543864 < baseStart_6543864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543921 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_6543921 : Nat := 118140960795 + 6543921 * 2 ^ 59
def prefixEnd_6543921 : Nat := 4983230072969 + 3 ^ 40 * 6543921 * 2
def baseEnd_6543921 : Nat := 3360176838050796612692561

theorem tailTrace_6543921 : CollatzResearch.WordTrace tailWord_6543921 prefixEnd_6543921 3360176838050796612692561 := by
  unfold tailWord_6543921
  simp only [CollatzResearch.WordTrace]
  refine ⟨238676406925499304574215617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159117604616999536382810411 238676406925499304574215617)
  ·
    refine ⟨179007305194124478430661713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238676406925499304574215617 179007305194124478430661713)
    ·
      refine ⟨134255478895593358822996285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179007305194124478430661713 134255478895593358822996285)
      ·
        refine ⟨50345804585847509558623607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134255478895593358822996285 50345804585847509558623607)
        ·
          refine ⟨75518706878771264337935411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50345804585847509558623607 75518706878771264337935411)
          ·
            refine ⟨113278060318156896506903117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75518706878771264337935411 113278060318156896506903117)
            ·
              refine ⟨42479272619308836190088669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113278060318156896506903117 42479272619308836190088669)
              ·
                refine ⟨15929727232240813571283251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42479272619308836190088669 15929727232240813571283251)
                ·
                  refine ⟨23894590848361220356924877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15929727232240813571283251 23894590848361220356924877)
                  ·
                    refine ⟨8960471568135457633846829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23894590848361220356924877 8960471568135457633846829)
                    ·
                      refine ⟨3360176838050796612692561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960471568135457633846829 3360176838050796612692561)
                      ·
                        rfl

theorem cell23_6543921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_6543921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543921 prefixEnd_6543921 := by exact prefixLift 6543921
  have htrace : WordTrace (prefixWord ++ tailWord_6543921) baseStart_6543921 baseEnd_6543921 := by
    simpa [prefixWord, tailWord_6543921, baseEnd_6543921] using wordTrace_append hprefix tailTrace_6543921
  have hstable : (prefixWord ++ tailWord_6543921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543921).length < 2 ^ (prefixWord ++ tailWord_6543921).sum := by decide
  have hdescent : baseEnd_6543921 < baseStart_6543921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543942 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6543942 : Nat := 118140960795 + 6543942 * 2 ^ 59
def prefixEnd_6543942 : Nat := 4983230072969 + 3 ^ 40 * 6543942 * 2
def baseEnd_6543942 : Nat := 3360187621144541030529965

theorem tailTrace_6543942 : CollatzResearch.WordTrace tailWord_6543942 prefixEnd_6543942 3360187621144541030529965 := by
  unfold tailWord_6543942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458661651825725786272815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159118115238948816773820053 7458661651825725786272815)
  ·
    refine ⟨11187992477738588679409223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7458661651825725786272815 11187992477738588679409223)
    ·
      refine ⟨16781988716607883019113835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187992477738588679409223 16781988716607883019113835)
      ·
        refine ⟨25172983074911824528670753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781988716607883019113835 25172983074911824528670753)
        ·
          refine ⟨18879737306183868396503065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25172983074911824528670753 18879737306183868396503065)
          ·
            refine ⟨14159802979637901297377299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18879737306183868396503065 14159802979637901297377299)
            ·
              refine ⟨21239704469456851946065949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14159802979637901297377299 21239704469456851946065949)
              ·
                refine ⟨7964889176046319479774731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21239704469456851946065949 7964889176046319479774731)
                ·
                  refine ⟨11947333764069479219662097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964889176046319479774731 11947333764069479219662097)
                  ·
                    refine ⟨8960500323052109414746573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11947333764069479219662097 8960500323052109414746573)
                    ·
                      refine ⟨3360187621144541030529965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960500323052109414746573 3360187621144541030529965)
                      ·
                        rfl

theorem cell23_6543942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6543942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543942 prefixEnd_6543942 := by exact prefixLift 6543942
  have htrace : WordTrace (prefixWord ++ tailWord_6543942) baseStart_6543942 baseEnd_6543942 := by
    simpa [prefixWord, tailWord_6543942, baseEnd_6543942] using wordTrace_append hprefix tailTrace_6543942
  have hstable : (prefixWord ++ tailWord_6543942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543942).length < 2 ^ (prefixWord ++ tailWord_6543942).sum := by decide
  have hdescent : baseEnd_6543942 < baseStart_6543942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543961 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 8, 2]
def baseStart_6543961 : Nat := 118140960795 + 6543961 * 2 ^ 59
def prefixEnd_6543961 : Nat := 4983230072969 + 3 ^ 40 * 6543961 * 2
def baseEnd_6543961 : Nat := 3360197377276976456192377

theorem tailTrace_6543961 : CollatzResearch.WordTrace tailWord_6543961 prefixEnd_6543961 3360197377276976456192377 := by
  unfold tailWord_6543961
  simp only [CollatzResearch.WordTrace]
  refine ⟨238677865845354391405671737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159118577230236260937114491 238677865845354391405671737)
  ·
    refine ⟨179008399384015793554253803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238677865845354391405671737 179008399384015793554253803)
    ·
      refine ⟨268512599076023690331380705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179008399384015793554253803 268512599076023690331380705)
      ·
        refine ⟨201384449307017767748535529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268512599076023690331380705 201384449307017767748535529)
        ·
          refine ⟨151038336980263325811401647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201384449307017767748535529 151038336980263325811401647)
          ·
            refine ⟨226557505470394988717102471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151038336980263325811401647 226557505470394988717102471)
            ·
              refine ⟨339836258205592483075653707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226557505470394988717102471 339836258205592483075653707)
              ·
                refine ⟨509754387308388724613480561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339836258205592483075653707 509754387308388724613480561)
                ·
                  refine ⟨382315790481291543460110421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509754387308388724613480561 382315790481291543460110421)
                  ·
                    refine ⟨4480263169702635274923169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 382315790481291543460110421 4480263169702635274923169)
                    ·
                      refine ⟨3360197377276976456192377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480263169702635274923169 3360197377276976456192377)
                      ·
                        rfl

theorem cell23_6543961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_6543961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543961 prefixEnd_6543961 := by exact prefixLift 6543961
  have htrace : WordTrace (prefixWord ++ tailWord_6543961) baseStart_6543961 baseEnd_6543961 := by
    simpa [prefixWord, tailWord_6543961, baseEnd_6543961] using wordTrace_append hprefix tailTrace_6543961
  have hstable : (prefixWord ++ tailWord_6543961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543961).length < 2 ^ (prefixWord ++ tailWord_6543961).sum := by decide
  have hdescent : baseEnd_6543961 < baseStart_6543961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543966 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6543966 : Nat := 118140960795 + 6543966 * 2 ^ 59
def prefixEnd_6543966 : Nat := 4983230072969 + 3 ^ 40 * 6543966 * 2
def baseEnd_6543966 : Nat := 1120066648226749645543285

theorem tailTrace_6543966 : CollatzResearch.WordTrace tailWord_6543966 prefixEnd_6543966 1120066648226749645543285 := by
  unfold tailWord_6543966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29834756026292034657450469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159118698806890851506402501 29834756026292034657450469)
  ·
    refine ⟨5594016754929756498271963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29834756026292034657450469 5594016754929756498271963)
    ·
      refine ⟨8391025132394634747407945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594016754929756498271963 8391025132394634747407945)
      ·
        refine ⟨6293268849295976060555959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8391025132394634747407945 6293268849295976060555959)
        ·
          refine ⟨9439903273943964090833939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293268849295976060555959 9439903273943964090833939)
          ·
            refine ⟨14159854910915946136250909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9439903273943964090833939 14159854910915946136250909)
            ·
              refine ⟨5309945591593479801094091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14159854910915946136250909 5309945591593479801094091)
              ·
                refine ⟨7964918387390219701641137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309945591593479801094091 7964918387390219701641137)
                ·
                  refine ⟨5973688790542664776230853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7964918387390219701641137 5973688790542664776230853)
                  ·
                    refine ⟨1120066648226749645543285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5973688790542664776230853 1120066648226749645543285)
                    ·
                      rfl

theorem cell23_6543966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6543966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543966 prefixEnd_6543966 := by exact prefixLift 6543966
  have htrace : WordTrace (prefixWord ++ tailWord_6543966) baseStart_6543966 baseEnd_6543966 := by
    simpa [prefixWord, tailWord_6543966, baseEnd_6543966] using wordTrace_append hprefix tailTrace_6543966
  have hstable : (prefixWord ++ tailWord_6543966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543966).length < 2 ^ (prefixWord ++ tailWord_6543966).sum := by decide
  have hdescent : baseEnd_6543966 < baseStart_6543966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6543982 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6543982 : Nat := 118140960795 + 6543982 * 2 ^ 59
def prefixEnd_6543982 : Nat := 4983230072969 + 3 ^ 40 * 6543982 * 2
def baseEnd_6543982 : Nat := 3360208160370720874029781

theorem tailTrace_6543982 : CollatzResearch.WordTrace tailWord_6543982 prefixEnd_6543982 3360208160370720874029781 := by
  unfold tailWord_6543982
  simp only [CollatzResearch.WordTrace]
  refine ⟨29834828972284788999023275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159119087852185541328124133 29834828972284788999023275)
  ·
    refine ⟨44752243458427183498534913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29834828972284788999023275 44752243458427183498534913)
    ·
      refine ⟨33564182593820387623901185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44752243458427183498534913 33564182593820387623901185)
      ·
        refine ⟨25173136945365290717925889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33564182593820387623901185 25173136945365290717925889)
        ·
          refine ⟨18879852709023968038444417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25173136945365290717925889 18879852709023968038444417)
          ·
            refine ⟨14159889531767976028833313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18879852709023968038444417 14159889531767976028833313)
            ·
              refine ⟨10619917148825982021624985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14159889531767976028833313 10619917148825982021624985)
              ·
                refine ⟨7964937861619486516218739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10619917148825982021624985 7964937861619486516218739)
                ·
                  refine ⟨11947406792429229774328109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964937861619486516218739 11947406792429229774328109)
                  ·
                    refine ⟨4480277547160961165373041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11947406792429229774328109 4480277547160961165373041)
                    ·
                      refine ⟨3360208160370720874029781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480277547160961165373041 3360208160370720874029781)
                      ·
                        rfl

theorem cell23_6543982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6543982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6543982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6543982 prefixEnd_6543982 := by exact prefixLift 6543982
  have htrace : WordTrace (prefixWord ++ tailWord_6543982) baseStart_6543982 baseEnd_6543982 := by
    simpa [prefixWord, tailWord_6543982, baseEnd_6543982] using wordTrace_append hprefix tailTrace_6543982
  have hstable : (prefixWord ++ tailWord_6543982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6543982).length < 2 ^ (prefixWord ++ tailWord_6543982).sum := by decide
  have hdescent : baseEnd_6543982 < baseStart_6543982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6543982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544011 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3]
def baseStart_6544011 : Nat := 118140960795 + 6544011 * 2 ^ 59
def prefixEnd_6544011 : Nat := 4983230072969 + 3 ^ 40 * 6544011 * 2
def baseEnd_6544011 : Nat := 3360223051309701260567147

theorem tailTrace_6544011 : CollatzResearch.WordTrace tailWord_6544011 prefixEnd_6544011 3360223051309701260567147 := by
  unfold tailWord_6544011
  simp only [CollatzResearch.WordTrace]
  refine ⟨238679689495173249944991887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159119792996782166629994591 238679689495173249944991887)
  ·
    refine ⟨358019534242759874917487831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238679689495173249944991887 358019534242759874917487831)
    ·
      refine ⟨537029301364139812376231747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358019534242759874917487831 537029301364139812376231747)
      ·
        refine ⟨805543952046209718564347621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537029301364139812376231747 805543952046209718564347621)
        ·
          refine ⟨151039491008664322230815179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 805543952046209718564347621 151039491008664322230815179)
          ·
            refine ⟨226559236512996483346222769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151039491008664322230815179 226559236512996483346222769)
            ·
              refine ⟨169919427384747362509667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226559236512996483346222769 169919427384747362509667077)
              ·
                refine ⟨31859892634640130470562577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169919427384747362509667077 31859892634640130470562577)
                ·
                  refine ⟨23894919475980097852921933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31859892634640130470562577 23894919475980097852921933)
                  ·
                    refine ⟨8960594803492536694845725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23894919475980097852921933 8960594803492536694845725)
                    ·
                      refine ⟨3360223051309701260567147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960594803492536694845725 3360223051309701260567147)
                      ·
                        rfl

theorem cell23_6544011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].length) (baseStart_6544011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544011 prefixEnd_6544011 := by exact prefixLift 6544011
  have htrace : WordTrace (prefixWord ++ tailWord_6544011) baseStart_6544011 baseEnd_6544011 := by
    simpa [prefixWord, tailWord_6544011, baseEnd_6544011] using wordTrace_append hprefix tailTrace_6544011
  have hstable : (prefixWord ++ tailWord_6544011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544011).length < 2 ^ (prefixWord ++ tailWord_6544011).sum := by decide
  have hdescent : baseEnd_6544011 < baseStart_6544011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544018 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_6544018 : Nat := 118140960795 + 6544018 * 2 ^ 59
def prefixEnd_6544018 : Nat := 4983230072969 + 3 ^ 40 * 6544018 * 2
def baseEnd_6544018 : Nat := 373358516186031414797735

theorem tailTrace_6544018 : CollatzResearch.WordTrace tailWord_6544018 prefixEnd_6544018 373358516186031414797735 := by
  unfold tailWord_6544018
  simp only [CollatzResearch.WordTrace]
  refine ⟨59669986201536972535124177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159119963204098593426997805 59669986201536972535124177)
  ·
    refine ⟨44752489651152729401343133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59669986201536972535124177 44752489651152729401343133)
    ·
      refine ⟨16782183619182273525503675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44752489651152729401343133 16782183619182273525503675)
      ·
        refine ⟨25173275428773410288255513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782183619182273525503675 25173275428773410288255513)
        ·
          refine ⟨18879956571580057716191635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25173275428773410288255513 18879956571580057716191635)
          ·
            refine ⟨28319934857370086574287453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18879956571580057716191635 28319934857370086574287453)
            ·
              refine ⟨10619975571513782465357795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28319934857370086574287453 10619975571513782465357795)
              ·
                refine ⟨15929963357270673698036693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619975571513782465357795 15929963357270673698036693)
                ·
                  refine ⟨373358516186031414797735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15929963357270673698036693 373358516186031414797735)
                  ·
                    rfl

theorem cell23_6544018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_6544018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544018 prefixEnd_6544018 := by exact prefixLift 6544018
  have htrace : WordTrace (prefixWord ++ tailWord_6544018) baseStart_6544018 baseEnd_6544018 := by
    simpa [prefixWord, tailWord_6544018, baseEnd_6544018] using wordTrace_append hprefix tailTrace_6544018
  have hstable : (prefixWord ++ tailWord_6544018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544018).length < 2 ^ (prefixWord ++ tailWord_6544018).sum := by decide
  have hdescent : baseEnd_6544018 < baseStart_6544018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544128 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2]
def baseStart_6544128 : Nat := 118140960795 + 6544128 * 2 ^ 59
def prefixEnd_6544128 : Nat := 4983230072969 + 3 ^ 40 * 6544128 * 2
def baseEnd_6544128 : Nat := 3360283128546277302804109

theorem tailTrace_6544128 : CollatzResearch.WordTrace tailWord_6544128 prefixEnd_6544128 3360283128546277302804109 := by
  unfold tailWord_6544128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119341978417874689463500519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159122637890499585951334025 119341978417874689463500519)
  ·
    refine ⟨179012967626812034195250779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119341978417874689463500519 179012967626812034195250779)
    ·
      refine ⟨268519451440218051292876169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179012967626812034195250779 268519451440218051292876169)
      ·
        refine ⟨201389588580163538469657127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268519451440218051292876169 201389588580163538469657127)
        ·
          refine ⟨302084382870245307704485691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201389588580163538469657127 302084382870245307704485691)
          ·
            refine ⟨453126574305367961556728537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302084382870245307704485691 453126574305367961556728537)
            ·
              refine ⟨339844930729025971167546403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453126574305367961556728537 339844930729025971167546403)
              ·
                refine ⟨509767396093538956751319605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339844930729025971167546403 509767396093538956751319605)
                ·
                  refine ⟨47790693383769277195436213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509767396093538956751319605 47790693383769277195436213)
                  ·
                    refine ⟨4480377504728369737072145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47790693383769277195436213 4480377504728369737072145)
                    ·
                      refine ⟨3360283128546277302804109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480377504728369737072145 3360283128546277302804109)
                      ·
                        rfl

theorem cell23_6544128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_6544128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544128 prefixEnd_6544128 := by exact prefixLift 6544128
  have htrace : WordTrace (prefixWord ++ tailWord_6544128) baseStart_6544128 baseEnd_6544128 := by
    simpa [prefixWord, tailWord_6544128, baseEnd_6544128] using wordTrace_append hprefix tailTrace_6544128
  have hstable : (prefixWord ++ tailWord_6544128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544128).length < 2 ^ (prefixWord ++ tailWord_6544128).sum := by decide
  have hdescent : baseEnd_6544128 < baseStart_6544128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544168 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6544168 : Nat := 118140960795 + 6544168 * 2 ^ 59
def prefixEnd_6544168 : Nat := 4983230072969 + 3 ^ 40 * 6544168 * 2
def baseEnd_6544168 : Nat := 1120101222590819048767975

theorem tailTrace_6544168 : CollatzResearch.WordTrace tailWord_6544168 prefixEnd_6544168 1120101222590819048767975 := by
  unfold tailWord_6544168
  simp only [CollatzResearch.WordTrace]
  refine ⟨119342707877802232879228579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159123610503736310505638105 119342707877802232879228579)
  ·
    refine ⟨179014061816703349318842869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119342707877802232879228579 179014061816703349318842869)
    ·
      refine ⟨16782568295315938998641519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179014061816703349318842869 16782568295315938998641519)
      ·
        refine ⟨25173852442973908497962279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782568295315938998641519 25173852442973908497962279)
        ·
          refine ⟨37760778664460862746943419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25173852442973908497962279 37760778664460862746943419)
          ·
            refine ⟨56641167996691294120415129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37760778664460862746943419 56641167996691294120415129)
            ·
              refine ⟨42480875997518470590311347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56641167996691294120415129 42480875997518470590311347)
              ·
                refine ⟨63721313996277705885467021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42480875997518470590311347 63721313996277705885467021)
                ·
                  refine ⟨23895492748604139707050133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63721313996277705885467021 23895492748604139707050133)
                  ·
                    refine ⟨1120101222590819048767975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23895492748604139707050133 1120101222590819048767975)
                    ·
                      rfl

theorem cell23_6544168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6544168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544168 prefixEnd_6544168 := by exact prefixLift 6544168
  have htrace : WordTrace (prefixWord ++ tailWord_6544168) baseStart_6544168 baseEnd_6544168 := by
    simpa [prefixWord, tailWord_6544168, baseEnd_6544168] using wordTrace_append hprefix tailTrace_6544168
  have hstable : (prefixWord ++ tailWord_6544168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544168).length < 2 ^ (prefixWord ++ tailWord_6544168).sum := by decide
  have hdescent : baseEnd_6544168 < baseStart_6544168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544171 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6]
def baseStart_6544171 : Nat := 118140960795 + 6544171 * 2 ^ 59
def prefixEnd_6544171 : Nat := 4983230072969 + 3 ^ 40 * 6544171 * 2
def baseEnd_6544171 : Nat := 3360305208214420634566411

theorem tailTrace_6544171 : CollatzResearch.WordTrace tailWord_6544171 prefixEnd_6544171 3360305208214420634566411 := by
  unfold tailWord_6544171
  simp only [CollatzResearch.WordTrace]
  refine ⟨238685525174593597270816367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159123683449729064847210911 238685525174593597270816367)
  ·
    refine ⟨358028287761890395906224551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238685525174593597270816367 358028287761890395906224551)
    ·
      refine ⟨537042431642835593859336827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358028287761890395906224551 537042431642835593859336827)
      ·
        refine ⟨805563647464253390789005241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537042431642835593859336827 805563647464253390789005241)
        ·
          refine ⟨604172735598190043091753931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805563647464253390789005241 604172735598190043091753931)
          ·
            refine ⟨906259103397285064637630897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604172735598190043091753931 906259103397285064637630897)
            ·
              refine ⟨679694327547963798478223173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906259103397285064637630897 679694327547963798478223173)
              ·
                refine ⟨127442686415243212214666845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679694327547963798478223173 127442686415243212214666845)
                ·
                  refine ⟨47791007405716204580500067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127442686415243212214666845 47791007405716204580500067)
                  ·
                    refine ⟨71686511108574306870750101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47791007405716204580500067 71686511108574306870750101)
                    ·
                      refine ⟨3360305208214420634566411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71686511108574306870750101 3360305208214420634566411)
                      ·
                        rfl

theorem cell23_6544171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_6544171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544171 prefixEnd_6544171 := by exact prefixLift 6544171
  have htrace : WordTrace (prefixWord ++ tailWord_6544171) baseStart_6544171 baseEnd_6544171 := by
    simpa [prefixWord, tailWord_6544171, baseEnd_6544171] using wordTrace_append hprefix tailTrace_6544171
  have hstable : (prefixWord ++ tailWord_6544171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544171).length < 2 ^ (prefixWord ++ tailWord_6544171).sum := by decide
  have hdescent : baseEnd_6544171 < baseStart_6544171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544186 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_6544186 : Nat := 118140960795 + 6544186 * 2 ^ 59
def prefixEnd_6544186 : Nat := 4983230072969 + 3 ^ 40 * 6544186 * 2
def baseEnd_6544186 : Nat := 3360312910424238075878843

theorem tailTrace_6544186 : CollatzResearch.WordTrace tailWord_6544186 prefixEnd_6544186 3360312910424238075878843 := by
  unfold tailWord_6544186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59671518067384813708153103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159124048179692836555074941 59671518067384813708153103)
  ·
    refine ⟨89507277101077220562229655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59671518067384813708153103 89507277101077220562229655)
    ·
      refine ⟨134260915651615830843344483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89507277101077220562229655 134260915651615830843344483)
      ·
        refine ⟨201391373477423746265016725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134260915651615830843344483 201391373477423746265016725)
        ·
          refine ⟨9440220631754238106172659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201391373477423746265016725 9440220631754238106172659)
          ·
            refine ⟨14160330947631357159258989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440220631754238106172659 14160330947631357159258989)
            ·
              refine ⟨5310124105361758934722121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14160330947631357159258989 5310124105361758934722121)
              ·
                refine ⟨3982593079021319201041591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310124105361758934722121 3982593079021319201041591)
                ·
                  refine ⟨5973889618531978801562387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982593079021319201041591 5973889618531978801562387)
                  ·
                    refine ⟨8960834427797968202343581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973889618531978801562387 8960834427797968202343581)
                    ·
                      refine ⟨3360312910424238075878843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960834427797968202343581 3360312910424238075878843)
                      ·
                        rfl

theorem cell23_6544186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_6544186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544186 prefixEnd_6544186 := by exact prefixLift 6544186
  have htrace : WordTrace (prefixWord ++ tailWord_6544186) baseStart_6544186 baseEnd_6544186 := by
    simpa [prefixWord, tailWord_6544186, baseEnd_6544186] using wordTrace_append hprefix tailTrace_6544186
  have hstable : (prefixWord ++ tailWord_6544186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544186).length < 2 ^ (prefixWord ++ tailWord_6544186).sum := by decide
  have hdescent : baseEnd_6544186 < baseStart_6544186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544209 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_6544209 : Nat := 118140960795 + 6544209 * 2 ^ 59
def prefixEnd_6544209 : Nat := 4983230072969 + 3 ^ 40 * 6544209 * 2
def baseEnd_6544209 : Nat := 3360324720479291485891237

theorem tailTrace_6544209 : CollatzResearch.WordTrace tailWord_6544209 prefixEnd_6544209 3360324720479291485891237 := by
  unfold tailWord_6544209
  simp only [CollatzResearch.WordTrace]
  refine ⟨238686911148455929760699681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159124607432303953173799787 238686911148455929760699681)
  ·
    refine ⟨179015183361341947320524761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238686911148455929760699681 179015183361341947320524761)
    ·
      refine ⟨134261387521006460490393571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179015183361341947320524761 134261387521006460490393571)
      ·
        refine ⟨201392081281509690735590357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134261387521006460490393571 201392081281509690735590357)
        ·
          refine ⟨4720126905035383376615399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 201392081281509690735590357 4720126905035383376615399)
          ·
            refine ⟨7080190357553075064923099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720126905035383376615399 7080190357553075064923099)
            ·
              refine ⟨10620285536329612597384649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080190357553075064923099 10620285536329612597384649)
              ·
                refine ⟨7965214152247209448038487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620285536329612597384649 7965214152247209448038487)
                ·
                  refine ⟨11947821228370814172057731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7965214152247209448038487 11947821228370814172057731)
                  ·
                    refine ⟨17921731842556221258086597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11947821228370814172057731 17921731842556221258086597)
                    ·
                      refine ⟨3360324720479291485891237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17921731842556221258086597 3360324720479291485891237)
                      ·
                        rfl

theorem cell23_6544209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_6544209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544209 prefixEnd_6544209 := by exact prefixLift 6544209
  have htrace : WordTrace (prefixWord ++ tailWord_6544209) baseStart_6544209 baseEnd_6544209 := by
    simpa [prefixWord, tailWord_6544209, baseEnd_6544209] using wordTrace_append hprefix tailTrace_6544209
  have hstable : (prefixWord ++ tailWord_6544209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544209).length < 2 ^ (prefixWord ++ tailWord_6544209).sum := by decide
  have hdescent : baseEnd_6544209 < baseStart_6544209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544212 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_6544212 : Nat := 118140960795 + 6544212 * 2 ^ 59
def prefixEnd_6544212 : Nat := 4983230072969 + 3 ^ 40 * 6544212 * 2
def baseEnd_6544212 : Nat := 3360326260921254974153723

theorem tailTrace_6544212 : CollatzResearch.WordTrace tailWord_6544212 prefixEnd_6544212 3360326260921254974153723 := by
  unfold tailWord_6544212
  simp only [CollatzResearch.WordTrace]
  refine ⟨119343510283722530636529445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159124680378296707515372593 119343510283722530636529445)
  ·
    refine ⟨22376908178197974494349271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119343510283722530636529445 22376908178197974494349271)
    ·
      refine ⟨33565362267296961741523907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22376908178197974494349271 33565362267296961741523907)
      ·
        refine ⟨50348043400945442612285861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33565362267296961741523907 50348043400945442612285861)
        ·
          refine ⟨9440258137677270489803599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50348043400945442612285861 9440258137677270489803599)
          ·
            refine ⟨14160387206515905734705399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440258137677270489803599 14160387206515905734705399)
            ·
              refine ⟨21240580809773858602058099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14160387206515905734705399 21240580809773858602058099)
              ·
                refine ⟨31860871214660787903087149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21240580809773858602058099 31860871214660787903087149)
                ·
                  refine ⟨11947826705497795463657681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31860871214660787903087149 11947826705497795463657681)
                  ·
                    refine ⟨8960870029123346597743261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11947826705497795463657681 8960870029123346597743261)
                    ·
                      refine ⟨3360326260921254974153723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960870029123346597743261 3360326260921254974153723)
                      ·
                        rfl

theorem cell23_6544212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_6544212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544212 prefixEnd_6544212 := by exact prefixLift 6544212
  have htrace : WordTrace (prefixWord ++ tailWord_6544212) baseStart_6544212 baseEnd_6544212 := by
    simpa [prefixWord, tailWord_6544212, baseEnd_6544212] using wordTrace_append hprefix tailTrace_6544212
  have hstable : (prefixWord ++ tailWord_6544212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544212).length < 2 ^ (prefixWord ++ tailWord_6544212).sum := by decide
  have hdescent : baseEnd_6544212 < baseStart_6544212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544225 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_6544225 : Nat := 118140960795 + 6544225 * 2 ^ 59
def prefixEnd_6544225 : Nat := 4983230072969 + 3 ^ 40 * 6544225 * 2
def baseEnd_6544225 : Nat := 3360332936169763423291163

theorem tailTrace_6544225 : CollatzResearch.WordTrace tailWord_6544225 prefixEnd_6544225 3360332936169763423291163 := by
  unfold tailWord_6544225
  simp only [CollatzResearch.WordTrace]
  refine ⟨238687494716397964493282129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159124996477598642995521419 238687494716397964493282129)
  ·
    refine ⟨179015621037298473369961597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238687494716397964493282129 179015621037298473369961597)
    ·
      refine ⟨67130857888986927513735599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179015621037298473369961597 67130857888986927513735599)
      ·
        refine ⟨100696286833480391270603399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67130857888986927513735599 100696286833480391270603399)
        ·
          refine ⟨151044430250220586905905099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100696286833480391270603399 151044430250220586905905099)
          ·
            refine ⟨226566645375330880358857649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151044430250220586905905099 226566645375330880358857649)
            ·
              refine ⟨169924984031498160269143237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226566645375330880358857649 169924984031498160269143237)
              ·
                refine ⟨31860934505905905050464357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169924984031498160269143237 31860934505905905050464357)
                ·
                  refine ⟨5973925219857357196962067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31860934505905905050464357 5973925219857357196962067)
                  ·
                    refine ⟨8960887829786035795443101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973925219857357196962067 8960887829786035795443101)
                    ·
                      refine ⟨3360332936169763423291163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960887829786035795443101 3360332936169763423291163)
                      ·
                        rfl

theorem cell23_6544225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_6544225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544225 prefixEnd_6544225 := by exact prefixLift 6544225
  have htrace : WordTrace (prefixWord ++ tailWord_6544225) baseStart_6544225 baseEnd_6544225 := by
    simpa [prefixWord, tailWord_6544225, baseEnd_6544225] using wordTrace_append hprefix tailTrace_6544225
  have hstable : (prefixWord ++ tailWord_6544225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544225).length < 2 ^ (prefixWord ++ tailWord_6544225).sum := by decide
  have hdescent : baseEnd_6544225 < baseStart_6544225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544242 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_6544242 : Nat := 118140960795 + 6544242 * 2 ^ 59
def prefixEnd_6544242 : Nat := 4983230072969 + 3 ^ 40 * 6544242 * 2
def baseEnd_6544242 : Nat := 3360341665340889856778585

theorem tailTrace_6544242 : CollatzResearch.WordTrace tailWord_6544242 prefixEnd_6544242 3360341665340889856778585 := by
  unfold tailWord_6544242
  simp only [CollatzResearch.WordTrace]
  refine ⟨59672028689334094099162745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159125409838224250931100653 59672028689334094099162745)
  ·
    refine ⟨44754021517000570574372059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59672028689334094099162745 44754021517000570574372059)
    ·
      refine ⟨67131032275500855861558089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44754021517000570574372059 67131032275500855861558089)
      ·
        refine ⟨50348274206625641896168567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67131032275500855861558089 50348274206625641896168567)
        ·
          refine ⟨75522411309938462844252851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50348274206625641896168567 75522411309938462844252851)
          ·
            refine ⟨113283616964907694266379277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75522411309938462844252851 113283616964907694266379277)
            ·
              refine ⟨42481356361840385349892229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113283616964907694266379277 42481356361840385349892229)
              ·
                refine ⟨7965254317845072253104793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42481356361840385349892229 7965254317845072253104793)
                ·
                  refine ⟨5973940738383804189828595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965254317845072253104793 5973940738383804189828595)
                  ·
                    refine ⟨8960911107575706284742893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973940738383804189828595 8960911107575706284742893)
                    ·
                      refine ⟨3360341665340889856778585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8960911107575706284742893 3360341665340889856778585)
                      ·
                        rfl

theorem cell23_6544242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_6544242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544242 prefixEnd_6544242 := by exact prefixLift 6544242
  have htrace : WordTrace (prefixWord ++ tailWord_6544242) baseStart_6544242 baseEnd_6544242 := by
    simpa [prefixWord, tailWord_6544242, baseEnd_6544242] using wordTrace_append hprefix tailTrace_6544242
  have hstable : (prefixWord ++ tailWord_6544242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544242).length < 2 ^ (prefixWord ++ tailWord_6544242).sum := by decide
  have hdescent : baseEnd_6544242 < baseStart_6544242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544268 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6544268 : Nat := 118140960795 + 6544268 * 2 ^ 59
def prefixEnd_6544268 : Nat := 4983230072969 + 3 ^ 40 * 6544268 * 2
def baseEnd_6544268 : Nat := 3360355015837906755053465

theorem tailTrace_6544268 : CollatzResearch.WordTrace tailWord_6544268 prefixEnd_6544268 3360355015837906755053465 := by
  unfold tailWord_6544268
  simp only [CollatzResearch.WordTrace]
  refine ⟨119344531527621091418548729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159126042036828121891398305 119344531527621091418548729)
  ·
    refine ⟨89508398645715818563911547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119344531527621091418548729 89508398645715818563911547)
    ·
      refine ⟨134262597968573727845867321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89508398645715818563911547 134262597968573727845867321)
      ·
        refine ⟨100696948476430295884400491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134262597968573727845867321 100696948476430295884400491)
        ·
          refine ⟨151045422714645443826600737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100696948476430295884400491 151045422714645443826600737)
          ·
            refine ⟨113284067035984082869950553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151045422714645443826600737 113284067035984082869950553)
            ·
              refine ⟨84963050276988062152462915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113284067035984082869950553 84963050276988062152462915)
              ·
                refine ⟨127444575415482093228694373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84963050276988062152462915 127444575415482093228694373)
                ·
                  refine ⟨23895857890402892480380195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127444575415482093228694373 23895857890402892480380195)
                  ·
                    refine ⟨35843786835604338720570293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23895857890402892480380195 35843786835604338720570293)
                    ·
                      refine ⟨3360355015837906755053465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35843786835604338720570293 3360355015837906755053465)
                      ·
                        rfl

theorem cell23_6544268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6544268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544268 prefixEnd_6544268 := by exact prefixLift 6544268
  have htrace : WordTrace (prefixWord ++ tailWord_6544268) baseStart_6544268 baseEnd_6544268 := by
    simpa [prefixWord, tailWord_6544268, baseEnd_6544268] using wordTrace_append hprefix tailTrace_6544268
  have hstable : (prefixWord ++ tailWord_6544268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544268).length < 2 ^ (prefixWord ++ tailWord_6544268).sum := by decide
  have hdescent : baseEnd_6544268 < baseStart_6544268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544310 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6544310 : Nat := 118140960795 + 6544310 * 2 ^ 59
def prefixEnd_6544310 : Nat := 4983230072969 + 3 ^ 40 * 6544310 * 2
def baseEnd_6544310 : Nat := 3360376582025395590728273

theorem tailTrace_6544310 : CollatzResearch.WordTrace tailWord_6544310 prefixEnd_6544310 3360376582025395590728273 := by
  unfold tailWord_6544310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918162182568126500632899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159127063280726682673417589 14918162182568126500632899)
  ·
    refine ⟨22377243273852189750949349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918162182568126500632899 22377243273852189750949349)
    ·
      refine ⟨4195733113847285578303003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22377243273852189750949349 4195733113847285578303003)
      ·
        refine ⟨6293599670770928367454505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195733113847285578303003 6293599670770928367454505)
        ·
          refine ⟨4720199753078196275590879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6293599670770928367454505 4720199753078196275590879)
          ·
            refine ⟨7080299629617294413386319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720199753078196275590879 7080299629617294413386319)
            ·
              refine ⟨10620449444425941620079479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080299629617294413386319 10620449444425941620079479)
              ·
                refine ⟨15930674166638912430119219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10620449444425941620079479 15930674166638912430119219)
                ·
                  refine ⟨23896011249958368645178829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15930674166638912430119219 23896011249958368645178829)
                  ·
                    refine ⟨8961004218734388241942061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23896011249958368645178829 8961004218734388241942061)
                    ·
                      refine ⟨3360376582025395590728273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8961004218734388241942061 3360376582025395590728273)
                      ·
                        rfl

theorem cell23_6544310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6544310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544310 prefixEnd_6544310 := by exact prefixLift 6544310
  have htrace : WordTrace (prefixWord ++ tailWord_6544310) baseStart_6544310 baseEnd_6544310 := by
    simpa [prefixWord, tailWord_6544310, baseEnd_6544310] using wordTrace_append hprefix tailTrace_6544310
  have hstable : (prefixWord ++ tailWord_6544310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544310).length < 2 ^ (prefixWord ++ tailWord_6544310).sum := by decide
  have hdescent : baseEnd_6544310 < baseStart_6544310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544325 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_6544325 : Nat := 118140960795 + 6544325 * 2 ^ 59
def prefixEnd_6544325 : Nat := 4983230072969 + 3 ^ 40 * 6544325 * 2
def baseEnd_6544325 : Nat := 3360384284235213032040703

theorem tailTrace_6544325 : CollatzResearch.WordTrace tailWord_6544325 prefixEnd_6544325 3360384284235213032040703 := by
  unfold tailWord_6544325
  simp only [CollatzResearch.WordTrace]
  refine ⟨238691142016035681571922429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159127428010690454381281619 238691142016035681571922429)
  ·
    refine ⟨89509178256013380589470911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238691142016035681571922429 89509178256013380589470911)
    ·
      refine ⟨134263767384020070884206367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89509178256013380589470911 134263767384020070884206367)
      ·
        refine ⟨201395651076030106326309551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134263767384020070884206367 201395651076030106326309551)
        ·
          refine ⟨302093476614045159489464327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201395651076030106326309551 302093476614045159489464327)
          ·
            refine ⟨453140214921067739234196491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302093476614045159489464327 453140214921067739234196491)
            ·
              refine ⟨679710322381601608851294737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453140214921067739234196491 679710322381601608851294737)
              ·
                refine ⟨509782741786201206638471053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679710322381601608851294737 509782741786201206638471053)
                ·
                  refine ⟨191168528169825452489426645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509782741786201206638471053 191168528169825452489426645)
                  ·
                    refine ⟨4480512378980284042720937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191168528169825452489426645 4480512378980284042720937)
                    ·
                      refine ⟨3360384284235213032040703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480512378980284042720937 3360384284235213032040703)
                      ·
                        rfl

theorem cell23_6544325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_6544325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544325 prefixEnd_6544325 := by exact prefixLift 6544325
  have htrace : WordTrace (prefixWord ++ tailWord_6544325) baseStart_6544325 baseEnd_6544325 := by
    simpa [prefixWord, tailWord_6544325, baseEnd_6544325] using wordTrace_append hprefix tailTrace_6544325
  have hstable : (prefixWord ++ tailWord_6544325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544325).length < 2 ^ (prefixWord ++ tailWord_6544325).sum := by decide
  have hdescent : baseEnd_6544325 < baseStart_6544325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544386 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_6544386 : Nat := 118140960795 + 6544386 * 2 ^ 59
def prefixEnd_6544386 : Nat := 4983230072969 + 3 ^ 40 * 6544386 * 2
def baseEnd_6544386 : Nat := 1120138535518379097792641

theorem tailTrace_6544386 : CollatzResearch.WordTrace tailWord_6544386 prefixEnd_6544386 1120138535518379097792641 := by
  unfold tailWord_6544386
  simp only [CollatzResearch.WordTrace]
  refine ⟨59673341717203672247473253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159128911245876459326595341 59673341717203672247473253)
  ·
    refine ⟨11188751571975688546401235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59673341717203672247473253 11188751571975688546401235)
    ·
      refine ⟨16783127357963532819601853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11188751571975688546401235 16783127357963532819601853)
      ·
        refine ⟨6293672759236324807350695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16783127357963532819601853 6293672759236324807350695)
        ·
          refine ⟨9440509138854487211026043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293672759236324807350695 9440509138854487211026043)
          ·
            refine ⟨14160763708281730816539065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440509138854487211026043 14160763708281730816539065)
            ·
              refine ⟨10620572781211298112404299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14160763708281730816539065 10620572781211298112404299)
              ·
                refine ⟨15930859171816947168606449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10620572781211298112404299 15930859171816947168606449)
                ·
                  refine ⟨11948144378862710376454837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15930859171816947168606449 11948144378862710376454837)
                  ·
                    refine ⟨1120138535518379097792641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11948144378862710376454837 1120138535518379097792641)
                    ·
                      rfl

theorem cell23_6544386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_6544386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544386 prefixEnd_6544386 := by exact prefixLift 6544386
  have htrace : WordTrace (prefixWord ++ tailWord_6544386) baseStart_6544386 baseEnd_6544386 := by
    simpa [prefixWord, tailWord_6544386, baseEnd_6544386] using wordTrace_append hprefix tailTrace_6544386
  have hstable : (prefixWord ++ tailWord_6544386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544386).length < 2 ^ (prefixWord ++ tailWord_6544386).sum := by decide
  have hdescent : baseEnd_6544386 < baseStart_6544386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544392 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_6544392 : Nat := 118140960795 + 6544392 * 2 ^ 59
def prefixEnd_6544392 : Nat := 4983230072969 + 3 ^ 40 * 6544392 * 2
def baseEnd_6544392 : Nat := 3360418687439064269902895

theorem tailTrace_6544392 : CollatzResearch.WordTrace tailWord_6544392 prefixEnd_6544392 3360418687439064269902895 := by
  unfold tailWord_6544392
  simp only [CollatzResearch.WordTrace]
  refine ⟨119346792853396476007305715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159129057137861968009740953 119346792853396476007305715)
  ·
    refine ⟨179020189280094714010958573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119346792853396476007305715 179020189280094714010958573)
    ·
      refine ⟨67132570980035517754109465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179020189280094714010958573 67132570980035517754109465)
      ·
        refine ⟨50349428235026638315582099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67132570980035517754109465 50349428235026638315582099)
        ·
          refine ⟨75524142352539957473373149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50349428235026638315582099 75524142352539957473373149)
          ·
            refine ⟨28321553382202484052514931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75524142352539957473373149 28321553382202484052514931)
            ·
              refine ⟨42482330073303726078772397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28321553382202484052514931 42482330073303726078772397)
              ·
                refine ⟨15930873777488897279539649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42482330073303726078772397 15930873777488897279539649)
                ·
                  refine ⟨11948155333116672959654737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15930873777488897279539649 11948155333116672959654737)
                  ·
                    refine ⟨8961116499837504719741053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11948155333116672959654737 8961116499837504719741053)
                    ·
                      refine ⟨3360418687439064269902895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8961116499837504719741053 3360418687439064269902895)
                      ·
                        rfl

theorem cell23_6544392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_6544392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544392 prefixEnd_6544392 := by exact prefixLift 6544392
  have htrace : WordTrace (prefixWord ++ tailWord_6544392) baseStart_6544392 baseEnd_6544392 := by
    simpa [prefixWord, tailWord_6544392, baseEnd_6544392] using wordTrace_append hprefix tailTrace_6544392
  have hstable : (prefixWord ++ tailWord_6544392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544392).length < 2 ^ (prefixWord ++ tailWord_6544392).sum := by decide
  have hdescent : baseEnd_6544392 < baseStart_6544392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544432 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2]
def baseStart_6544432 : Nat := 118140960795 + 6544432 * 2 ^ 59
def prefixEnd_6544432 : Nat := 4983230072969 + 3 ^ 40 * 6544432 * 2
def baseEnd_6544432 : Nat := 3360439226665244113402711

theorem tailTrace_6544432 : CollatzResearch.WordTrace tailWord_6544432 prefixEnd_6544432 3360439226665244113402711 := by
  unfold tailWord_6544432
  simp only [CollatzResearch.WordTrace]
  refine ⟨119347522313324019423033775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159130029751098692564045033 119347522313324019423033775)
  ·
    refine ⟨179021283469986029134550663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119347522313324019423033775 179021283469986029134550663)
    ·
      refine ⟨268531925204979043701825995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179021283469986029134550663 268531925204979043701825995)
      ·
        refine ⟨402797887807468565552738993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268531925204979043701825995 402797887807468565552738993)
        ·
          refine ⟨302098415855601424164554245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402797887807468565552738993 302098415855601424164554245)
          ·
            refine ⟨56643452972925267030853921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302098415855601424164554245 56643452972925267030853921)
            ·
              refine ⟨42482589729693950273140441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56643452972925267030853921 42482589729693950273140441)
              ·
                refine ⟨31861942297270462704855331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42482589729693950273140441 31861942297270462704855331)
                ·
                  refine ⟨47792913445905694057282997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31861942297270462704855331 47792913445905694057282997)
                  ·
                    refine ⟨4480585635553658817870281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47792913445905694057282997 4480585635553658817870281)
                    ·
                      refine ⟨3360439226665244113402711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480585635553658817870281 3360439226665244113402711)
                      ·
                        rfl

theorem cell23_6544432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2].length) (baseStart_6544432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544432 prefixEnd_6544432 := by exact prefixLift 6544432
  have htrace : WordTrace (prefixWord ++ tailWord_6544432) baseStart_6544432 baseEnd_6544432 := by
    simpa [prefixWord, tailWord_6544432, baseEnd_6544432] using wordTrace_append hprefix tailTrace_6544432
  have hstable : (prefixWord ++ tailWord_6544432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544432).length < 2 ^ (prefixWord ++ tailWord_6544432).sum := by decide
  have hdescent : baseEnd_6544432 < baseStart_6544432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544456 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_6544456 : Nat := 118140960795 + 6544456 * 2 ^ 59
def prefixEnd_6544456 : Nat := 4983230072969 + 3 ^ 40 * 6544456 * 2
def baseEnd_6544456 : Nat := 3360451550200952019502601

theorem tailTrace_6544456 : CollatzResearch.WordTrace tailWord_6544456 prefixEnd_6544456 3360451550200952019502601 := by
  unfold tailWord_6544456
  simp only [CollatzResearch.WordTrace]
  refine ⟨119347959989280545472470611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159130613319040727296627481 119347959989280545472470611)
  ·
    refine ⟨179021939983920818208705917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119347959989280545472470611 179021939983920818208705917)
    ·
      refine ⟨67133227493970306828264719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179021939983920818208705917 67133227493970306828264719)
      ·
        refine ⟨100699841240955460242397079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67133227493970306828264719 100699841240955460242397079)
        ·
          refine ⟨151049761861433190363595619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100699841240955460242397079 151049761861433190363595619)
          ·
            refine ⟨226574642792149785545393429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151049761861433190363595619 226574642792149785545393429)
            ·
              refine ⟨10620686380882021197440317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226574642792149785545393429 10620686380882021197440317)
              ·
                refine ⟨3982757392830757949040119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10620686380882021197440317 3982757392830757949040119)
                ·
                  refine ⟨5974136089246136923560179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982757392830757949040119 5974136089246136923560179)
                  ·
                    refine ⟨8961204133869205385340269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974136089246136923560179 8961204133869205385340269)
                    ·
                      refine ⟨3360451550200952019502601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8961204133869205385340269 3360451550200952019502601)
                      ·
                        rfl

theorem cell23_6544456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_6544456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544456 prefixEnd_6544456 := by exact prefixLift 6544456
  have htrace : WordTrace (prefixWord ++ tailWord_6544456) baseStart_6544456 baseEnd_6544456 := by
    simpa [prefixWord, tailWord_6544456, baseEnd_6544456] using wordTrace_append hprefix tailTrace_6544456
  have hstable : (prefixWord ++ tailWord_6544456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544456).length < 2 ^ (prefixWord ++ tailWord_6544456).sum := by decide
  have hdescent : baseEnd_6544456 < baseStart_6544456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544472 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 4, 4]
def baseStart_6544472 : Nat := 118140960795 + 6544472 * 2 ^ 59
def prefixEnd_6544472 : Nat := 4983230072969 + 3 ^ 40 * 6544472 * 2
def baseEnd_6544472 : Nat := 1120153255297141318967509

theorem tailTrace_6544472 : CollatzResearch.WordTrace tailWord_6544472 prefixEnd_6544472 1120153255297141318967509 := by
  unfold tailWord_6544472
  simp only [CollatzResearch.WordTrace]
  refine ⟨119348251773251562838761835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159131002364335417118349113 119348251773251562838761835)
  ·
    refine ⟨179022377659877344258142753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119348251773251562838761835 179022377659877344258142753)
    ·
      refine ⟨134266783244908008193607065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179022377659877344258142753 134266783244908008193607065)
      ·
        refine ⟨100700087433681006145205299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134266783244908008193607065 100700087433681006145205299)
        ·
          refine ⟨151050131150521509217807949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100700087433681006145205299 151050131150521509217807949)
          ·
            refine ⟨56643799181445565956677981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151050131150521509217807949 56643799181445565956677981)
            ·
              refine ⟨21241424693042087233754243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56643799181445565956677981 21241424693042087233754243)
              ·
                refine ⟨31862137039563130850631365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21241424693042087233754243 31862137039563130850631365)
                ·
                  refine ⟨5974150694918087034493381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31862137039563130850631365 5974150694918087034493381)
                  ·
                    refine ⟨1120153255297141318967509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974150694918087034493381 1120153255297141318967509)
                    ·
                      rfl

theorem cell23_6544472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_6544472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544472 prefixEnd_6544472 := by exact prefixLift 6544472
  have htrace : WordTrace (prefixWord ++ tailWord_6544472) baseStart_6544472 baseEnd_6544472 := by
    simpa [prefixWord, tailWord_6544472, baseEnd_6544472] using wordTrace_append hprefix tailTrace_6544472
  have hstable : (prefixWord ++ tailWord_6544472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544472).length < 2 ^ (prefixWord ++ tailWord_6544472).sum := by decide
  have hdescent : baseEnd_6544472 < baseStart_6544472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544485 : List Nat := [1, 3, 1, 3, 2, 1, 2, 10]
def baseStart_6544485 : Nat := 118140960795 + 6544485 * 2 ^ 59
def prefixEnd_6544485 : Nat := 4983230072969 + 3 ^ 40 * 6544485 * 2
def baseEnd_6544485 : Nat := 124461720042219718742221

theorem tailTrace_6544485 : CollatzResearch.WordTrace tailWord_6544485 prefixEnd_6544485 124461720042219718742221 := by
  unfold tailWord_6544485
  simp only [CollatzResearch.WordTrace]
  refine ⟨238696977695456028897746909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159131318463637352598497939 238696977695456028897746909)
  ·
    refine ⟨89511366635796010836655091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238696977695456028897746909 89511366635796010836655091)
    ·
      refine ⟨134267049953694016254982637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89511366635796010836655091 134267049953694016254982637)
      ·
        refine ⟨50350143732635256095618489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134267049953694016254982637 50350143732635256095618489)
        ·
          refine ⟨37762607799476442071713867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50350143732635256095618489 37762607799476442071713867)
          ·
            refine ⟨56643911699214663107570801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37762607799476442071713867 56643911699214663107570801)
            ·
              refine ⟨42482933774410997330678101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56643911699214663107570801 42482933774410997330678101)
              ·
                refine ⟨124461720042219718742221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42482933774410997330678101 124461720042219718742221)
                ·
                  rfl

theorem cell23_6544485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 10].length) (baseStart_6544485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544485 prefixEnd_6544485 := by exact prefixLift 6544485
  have htrace : WordTrace (prefixWord ++ tailWord_6544485) baseStart_6544485 baseEnd_6544485 := by
    simpa [prefixWord, tailWord_6544485, baseEnd_6544485] using wordTrace_append hprefix tailTrace_6544485
  have hstable : (prefixWord ++ tailWord_6544485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544485).length < 2 ^ (prefixWord ++ tailWord_6544485).sum := by decide
  have hdescent : baseEnd_6544485 < baseStart_6544485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544502 : List Nat := [5, 1, 1, 2, 1, 1, 3, 9]
def baseStart_6544502 : Nat := 118140960795 + 6544502 * 2 ^ 59
def prefixEnd_6544502 : Nat := 4983230072969 + 3 ^ 40 * 6544502 * 2
def baseEnd_6544502 : Nat := 124462043344854031093607

theorem tailTrace_6544502 : CollatzResearch.WordTrace tailWord_6544502 prefixEnd_6544502 124462043344854031093607 := by
  unfold tailWord_6544502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918599858524652550069735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159131731824262960534077173 14918599858524652550069735)
  ·
    refine ⟨22377899787786978825104603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918599858524652550069735 22377899787786978825104603)
    ·
      refine ⟨33566849681680468237656905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22377899787786978825104603 33566849681680468237656905)
      ·
        refine ⟨25175137261260351178242679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33566849681680468237656905 25175137261260351178242679)
        ·
          refine ⟨37762705891890526767364019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25175137261260351178242679 37762705891890526767364019)
          ·
            refine ⟨56644058837835790151046029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37762705891890526767364019 56644058837835790151046029)
            ·
              refine ⟨21241522064188421306642261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56644058837835790151046029 21241522064188421306642261)
              ·
                refine ⟨124462043344854031093607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21241522064188421306642261 124462043344854031093607)
                ·
                  rfl

theorem cell23_6544502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_6544502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544502 prefixEnd_6544502 := by exact prefixLift 6544502
  have htrace : WordTrace (prefixWord ++ tailWord_6544502) baseStart_6544502 baseEnd_6544502 := by
    simpa [prefixWord, tailWord_6544502, baseEnd_6544502] using wordTrace_append hprefix tailTrace_6544502
  have hstable : (prefixWord ++ tailWord_6544502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544502).length < 2 ^ (prefixWord ++ tailWord_6544502).sum := by decide
  have hdescent : baseEnd_6544502 < baseStart_6544502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544512 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3]
def baseStart_6544512 : Nat := 118140960795 + 6544512 * 2 ^ 59
def prefixEnd_6544512 : Nat := 4983230072969 + 3 ^ 40 * 6544512 * 2
def baseEnd_6544512 : Nat := 3360480305117603800402343

theorem tailTrace_6544512 : CollatzResearch.WordTrace tailWord_6544512 prefixEnd_6544512 3360480305117603800402343 := by
  unfold tailWord_6544512
  simp only [CollatzResearch.WordTrace]
  refine ⟨119348981233179106254489895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159131974977572141672653193 119348981233179106254489895)
  ·
    refine ⟨179023471849768659381734843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119348981233179106254489895 179023471849768659381734843)
    ·
      refine ⟨268535207774652989072602265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179023471849768659381734843 268535207774652989072602265)
      ·
        refine ⟨201401405830989741804451699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268535207774652989072602265 201401405830989741804451699)
        ·
          refine ⟨302102108746484612706677549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201401405830989741804451699 302102108746484612706677549)
          ·
            refine ⟨113288290779931729765004081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302102108746484612706677549 113288290779931729765004081)
            ·
              refine ⟨84966218084948797323753061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113288290779931729765004081 84966218084948797323753061)
              ·
                refine ⟨15931165890927899498203699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84966218084948797323753061 15931165890927899498203699)
                ·
                  refine ⟨23896748836391849247305549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15931165890927899498203699 23896748836391849247305549)
                  ·
                    refine ⟨8961280813646943467739581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23896748836391849247305549 8961280813646943467739581)
                    ·
                      refine ⟨3360480305117603800402343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8961280813646943467739581 3360480305117603800402343)
                      ·
                        rfl

theorem cell23_6544512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_6544512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544512 prefixEnd_6544512 := by exact prefixLift 6544512
  have htrace : WordTrace (prefixWord ++ tailWord_6544512) baseStart_6544512 baseEnd_6544512 := by
    simpa [prefixWord, tailWord_6544512, baseEnd_6544512] using wordTrace_append hprefix tailTrace_6544512
  have hstable : (prefixWord ++ tailWord_6544512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544512).length < 2 ^ (prefixWord ++ tailWord_6544512).sum := by decide
  have hdescent : baseEnd_6544512 < baseStart_6544512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544555 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_6544555 : Nat := 118140960795 + 6544555 * 2 ^ 59
def prefixEnd_6544555 : Nat := 4983230072969 + 3 ^ 40 * 6544555 * 2
def baseEnd_6544555 : Nat := 3360502384785747132164645

theorem tailTrace_6544555 : CollatzResearch.WordTrace tailWord_6544555 prefixEnd_6544555 3360502384785747132164645 := by
  unfold tailWord_6544555
  simp only [CollatzResearch.WordTrace]
  refine ⟨238699530805202430852795119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159133020536801620568530079 238699530805202430852795119)
  ·
    refine ⟨358049296207803646279192679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238699530805202430852795119 358049296207803646279192679)
    ·
      refine ⟨537073944311705469418789019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358049296207803646279192679 537073944311705469418789019)
      ·
        refine ⟨805610916467558204128183529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537073944311705469418789019 805610916467558204128183529)
        ·
          refine ⟨604208187350668653096137647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805610916467558204128183529 604208187350668653096137647)
          ·
            refine ⟨906312281026002979644206471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604208187350668653096137647 906312281026002979644206471)
            ·
              refine ⟨1359468421539004469466309707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906312281026002979644206471 1359468421539004469466309707)
              ·
                refine ⟨2039202632308506704199464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359468421539004469466309707 2039202632308506704199464561)
                ·
                  refine ⟨1529401974231380028149598421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039202632308506704199464561 1529401974231380028149598421)
                  ·
                    refine ⟨35845358771047969409756213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1529401974231380028149598421 35845358771047969409756213)
                    ·
                      refine ⟨3360502384785747132164645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35845358771047969409756213 3360502384785747132164645)
                      ·
                        rfl

theorem cell23_6544555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_6544555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544555 prefixEnd_6544555 := by exact prefixLift 6544555
  have htrace : WordTrace (prefixWord ++ tailWord_6544555) baseStart_6544555 baseEnd_6544555 := by
    simpa [prefixWord, tailWord_6544555, baseEnd_6544555] using wordTrace_append hprefix tailTrace_6544555
  have hstable : (prefixWord ++ tailWord_6544555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544555).length < 2 ^ (prefixWord ++ tailWord_6544555).sum := by decide
  have hdescent : baseEnd_6544555 < baseStart_6544555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544569 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6544569 : Nat := 118140960795 + 6544569 * 2 ^ 59
def prefixEnd_6544569 : Nat := 4983230072969 + 3 ^ 40 * 6544569 * 2
def baseEnd_6544569 : Nat := 3360509573514910077389581

theorem tailTrace_6544569 : CollatzResearch.WordTrace tailWord_6544569 prefixEnd_6544569 3360509573514910077389581 := by
  unfold tailWord_6544569
  simp only [CollatzResearch.WordTrace]
  refine ⟨238700041427151711243804761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159133360951434474162536507 238700041427151711243804761)
  ·
    refine ⟨179025031070363783432853571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238700041427151711243804761 179025031070363783432853571)
    ·
      refine ⟨268537546605545675149280357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179025031070363783432853571 268537546605545675149280357)
      ·
        refine ⟨50350789988539814090490067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268537546605545675149280357 50350789988539814090490067)
        ·
          refine ⟨75526184982809721135735101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50350789988539814090490067 75526184982809721135735101)
          ·
            refine ⟨28322319368553645425900663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75526184982809721135735101 28322319368553645425900663)
            ·
              refine ⟨42483479052830468138850995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28322319368553645425900663 42483479052830468138850995)
              ·
                refine ⟨63725218579245702208276493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42483479052830468138850995 63725218579245702208276493)
                ·
                  refine ⟨23896956967217138328103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63725218579245702208276493 23896956967217138328103685)
                  ·
                    refine ⟨4480679431353213436519441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23896956967217138328103685 4480679431353213436519441)
                    ·
                      refine ⟨3360509573514910077389581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480679431353213436519441 3360509573514910077389581)
                      ·
                        rfl

theorem cell23_6544569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6544569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544569 prefixEnd_6544569 := by exact prefixLift 6544569
  have htrace : WordTrace (prefixWord ++ tailWord_6544569) baseStart_6544569 baseEnd_6544569 := by
    simpa [prefixWord, tailWord_6544569, baseEnd_6544569] using wordTrace_append hprefix tailTrace_6544569
  have hstable : (prefixWord ++ tailWord_6544569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544569).length < 2 ^ (prefixWord ++ tailWord_6544569).sum := by decide
  have hdescent : baseEnd_6544569 < baseStart_6544569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544596 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6544596 : Nat := 118140960795 + 6544596 * 2 ^ 59
def prefixEnd_6544596 : Nat := 4983230072969 + 3 ^ 40 * 6544596 * 2
def baseEnd_6544596 : Nat := 1120174479164193823917319

theorem tailTrace_6544596 : CollatzResearch.WordTrace tailWord_6544596 prefixEnd_6544596 1120174479164193823917319 := by
  unfold tailWord_6544596
  simp only [CollatzResearch.WordTrace]
  refine ⟨119350513099026947427518821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159134017465369263236691761 119350513099026947427518821)
  ·
    refine ⟨22378221206067552642659779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119350513099026947427518821 22378221206067552642659779)
    ·
      refine ⟨33567331809101328963989669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22378221206067552642659779 33567331809101328963989669)
      ·
        refine ⟨6293874714206499180748063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33567331809101328963989669 6293874714206499180748063)
        ·
          refine ⟨9440812071309748771122095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293874714206499180748063 9440812071309748771122095)
          ·
            refine ⟨14161218106964623156683143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440812071309748771122095 14161218106964623156683143)
            ·
              refine ⟨21241827160446934735024715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14161218106964623156683143 21241827160446934735024715)
              ·
                refine ⟨31862740740670402102537073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21241827160446934735024715 31862740740670402102537073)
                ·
                  refine ⟨23897055555502801576902805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31862740740670402102537073 23897055555502801576902805)
                  ·
                    refine ⟨1120174479164193823917319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23897055555502801576902805 1120174479164193823917319)
                    ·
                      rfl

theorem cell23_6544596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6544596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544596 prefixEnd_6544596 := by exact prefixLift 6544596
  have htrace : WordTrace (prefixWord ++ tailWord_6544596) baseStart_6544596 baseEnd_6544596 := by
    simpa [prefixWord, tailWord_6544596, baseEnd_6544596] using wordTrace_append hprefix tailTrace_6544596
  have hstable : (prefixWord ++ tailWord_6544596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544596).length < 2 ^ (prefixWord ++ tailWord_6544596).sum := by decide
  have hdescent : baseEnd_6544596 < baseStart_6544596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544712 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 9]
def baseStart_6544712 : Nat := 118140960795 + 6544712 * 2 ^ 59
def prefixEnd_6544712 : Nat := 4983230072969 + 3 ^ 40 * 6544712 * 2
def baseEnd_6544712 : Nat := 1120194333749501005967141

theorem tailTrace_6544712 : CollatzResearch.WordTrace tailWord_6544712 prefixEnd_6544712 1120194333749501005967141 := by
  unfold tailWord_6544712
  simp only [CollatzResearch.WordTrace]
  refine ⟨119352628532816823333130195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159136838043755764444173593 119352628532816823333130195)
  ·
    refine ⟨179028942799225234999695293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119352628532816823333130195 179028942799225234999695293)
    ·
      refine ⟨67135853549709463124885735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179028942799225234999695293 67135853549709463124885735)
      ·
        refine ⟨100703780324564194687328603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67135853549709463124885735 100703780324564194687328603)
        ·
          refine ⟨151055670486846292030992905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100703780324564194687328603 151055670486846292030992905)
          ·
            refine ⟨113291752865134719023244679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151055670486846292030992905 113291752865134719023244679)
            ·
              refine ⟨169937629297702078534867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113291752865134719023244679 169937629297702078534867019)
              ·
                refine ⟨254906443946553117802300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169937629297702078534867019 254906443946553117802300529)
                ·
                  refine ⟨191179832959914838351725397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254906443946553117802300529 191179832959914838351725397)
                  ·
                    refine ⟨1120194333749501005967141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 191179832959914838351725397 1120194333749501005967141)
                    ·
                      rfl

theorem cell23_6544712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_6544712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544712 prefixEnd_6544712 := by exact prefixLift 6544712
  have htrace : WordTrace (prefixWord ++ tailWord_6544712) baseStart_6544712 baseEnd_6544712 := by
    simpa [prefixWord, tailWord_6544712, baseEnd_6544712] using wordTrace_append hprefix tailTrace_6544712
  have hstable : (prefixWord ++ tailWord_6544712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544712).length < 2 ^ (prefixWord ++ tailWord_6544712).sum := by decide
  have hdescent : baseEnd_6544712 < baseStart_6544712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544716 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 6]
def baseStart_6544716 : Nat := 118140960795 + 6544716 * 2 ^ 59
def prefixEnd_6544716 : Nat := 4983230072969 + 3 ^ 40 * 6544716 * 2
def baseEnd_6544716 : Nat := 373398339463457889139045

theorem tailTrace_6544716 : CollatzResearch.WordTrace tailWord_6544716 prefixEnd_6544716 373398339463457889139045 := by
  unfold tailWord_6544716
  simp only [CollatzResearch.WordTrace]
  refine ⟨119352701478809577674703001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159136935305079436899604001 119352701478809577674703001)
  ·
    refine ⟨89514526109107183256027251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119352701478809577674703001 89514526109107183256027251)
    ·
      refine ⟨134271789163660774884040877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89514526109107183256027251 134271789163660774884040877)
      ·
        refine ⟨50351920936372790581515329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134271789163660774884040877 50351920936372790581515329)
        ·
          refine ⟨37763940702279592936136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50351920936372790581515329 37763940702279592936136497)
          ·
            refine ⟨28322955526709694702102373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37763940702279592936136497 28322955526709694702102373)
            ·
              refine ⟨5310554161258067756644195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28322955526709694702102373 5310554161258067756644195)
              ·
                refine ⟨7965831241887101634966293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310554161258067756644195 7965831241887101634966293)
                ·
                  refine ⟨373398339463457889139045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7965831241887101634966293 373398339463457889139045)
                  ·
                    rfl

theorem cell23_6544716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_6544716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544716 prefixEnd_6544716 := by exact prefixLift 6544716
  have htrace : WordTrace (prefixWord ++ tailWord_6544716) baseStart_6544716 baseEnd_6544716 := by
    simpa [prefixWord, tailWord_6544716, baseEnd_6544716] using wordTrace_append hprefix tailTrace_6544716
  have hstable : (prefixWord ++ tailWord_6544716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544716).length < 2 ^ (prefixWord ++ tailWord_6544716).sum := by decide
  have hdescent : baseEnd_6544716 < baseStart_6544716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544776 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_6544776 : Nat := 118140960795 + 6544776 * 2 ^ 59
def prefixEnd_6544776 : Nat := 4983230072969 + 3 ^ 40 * 6544776 * 2
def baseEnd_6544776 : Nat := 1120205288003463589167043

theorem tailTrace_6544776 : CollatzResearch.WordTrace tailWord_6544776 prefixEnd_6544776 1120205288003463589167043 := by
  unfold tailWord_6544776
  simp only [CollatzResearch.WordTrace]
  refine ⟨119353795668700892798295091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159138394224934523731060121 119353795668700892798295091)
  ·
    refine ⟨179030693503051339197442637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119353795668700892798295091 179030693503051339197442637)
    ·
      refine ⟨67136510063644252199040989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179030693503051339197442637 67136510063644252199040989)
      ·
        refine ⟨25176191273866594574640371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67136510063644252199040989 25176191273866594574640371)
        ·
          refine ⟨37764286910799891861960557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176191273866594574640371 37764286910799891861960557)
          ·
            refine ⟨14161607591549959448235209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37764286910799891861960557 14161607591549959448235209)
            ·
              refine ⟨10621205693662469586176407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14161607591549959448235209 10621205693662469586176407)
              ·
                refine ⟨15931808540493704379264611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621205693662469586176407 15931808540493704379264611)
                ·
                  refine ⟨23897712810740556568896917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15931808540493704379264611 23897712810740556568896917)
                  ·
                    refine ⟨1120205288003463589167043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23897712810740556568896917 1120205288003463589167043)
                    ·
                      rfl

theorem cell23_6544776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_6544776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544776 prefixEnd_6544776 := by exact prefixLift 6544776
  have htrace : WordTrace (prefixWord ++ tailWord_6544776) baseStart_6544776 baseEnd_6544776 := by
    simpa [prefixWord, tailWord_6544776, baseEnd_6544776] using wordTrace_append hprefix tailTrace_6544776
  have hstable : (prefixWord ++ tailWord_6544776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544776).length < 2 ^ (prefixWord ++ tailWord_6544776).sum := by decide
  have hdescent : baseEnd_6544776 < baseStart_6544776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544843 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 1, 3, 2]
def baseStart_6544843 : Nat := 118140960795 + 6544843 * 2 ^ 59
def prefixEnd_6544843 : Nat := 4983230072969 + 3 ^ 40 * 6544843 * 2
def baseEnd_6544843 : Nat := 3360650267214242005363321

theorem tailTrace_6544843 : CollatzResearch.WordTrace tailWord_6544843 prefixEnd_6544843 3360650267214242005363321 := by
  unfold tailWord_6544843
  simp only [CollatzResearch.WordTrace]
  refine ⟨238710035028159056039279183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159140023352106037359519455 238710035028159056039279183)
  ·
    refine ⟨358065052542238584058918775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238710035028159056039279183 358065052542238584058918775)
    ·
      refine ⟨537097578813357876088378163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358065052542238584058918775 537097578813357876088378163)
      ·
        refine ⟨805646368220036814132567245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537097578813357876088378163 805646368220036814132567245)
        ·
          refine ⟨302117388082513805299712717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805646368220036814132567245 302117388082513805299712717)
          ·
            refine ⟨113294020530942676987392269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302117388082513805299712717 113294020530942676987392269)
            ·
              refine ⟨42485257699103503870272101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113294020530942676987392269 42485257699103503870272101)
              ·
                refine ⟨7965985818581906975676019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42485257699103503870272101 7965985818581906975676019)
                ·
                  refine ⟨11948978727872860463514029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7965985818581906975676019 11948978727872860463514029)
                  ·
                    refine ⟨4480867022952322673817761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11948978727872860463514029 4480867022952322673817761)
                    ·
                      refine ⟨3360650267214242005363321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480867022952322673817761 3360650267214242005363321)
                      ·
                        rfl

theorem cell23_6544843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 3, 2].length) (baseStart_6544843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544843 prefixEnd_6544843 := by exact prefixLift 6544843
  have htrace : WordTrace (prefixWord ++ tailWord_6544843) baseStart_6544843 baseEnd_6544843 := by
    simpa [prefixWord, tailWord_6544843, baseEnd_6544843] using wordTrace_append hprefix tailTrace_6544843
  have hstable : (prefixWord ++ tailWord_6544843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544843).length < 2 ^ (prefixWord ++ tailWord_6544843).sum := by decide
  have hdescent : baseEnd_6544843 < baseStart_6544843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544890 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_6544890 : Nat := 118140960795 + 6544890 * 2 ^ 59
def prefixEnd_6544890 : Nat := 4983230072969 + 3 ^ 40 * 6544890 * 2
def baseEnd_6544890 : Nat := 3360674400805003321475605

theorem tailTrace_6544890 : CollatzResearch.WordTrace tailWord_6544890 prefixEnd_6544890 3360674400805003321475605 := by
  unfold tailWord_6544890
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677937314747195766560031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159141166172659188710826749 59677937314747195766560031)
  ·
    refine ⟨89516905972120793649840047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59677937314747195766560031 89516905972120793649840047)
    ·
      refine ⟨134275358958181190474760071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89516905972120793649840047 134275358958181190474760071)
      ·
        refine ⟨201413038437271785712140107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134275358958181190474760071 201413038437271785712140107)
        ·
          refine ⟨302119557655907678568210161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201413038437271785712140107 302119557655907678568210161)
          ·
            refine ⟨226589668241930758926157621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302119557655907678568210161 226589668241930758926157621)
            ·
              refine ⟨21242781397681008649327277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226589668241930758926157621 21242781397681008649327277)
              ·
                refine ⟨7966043024130378243497729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21242781397681008649327277 7966043024130378243497729)
                ·
                  refine ⟨5974532268097783682623297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966043024130378243497729 5974532268097783682623297)
                  ·
                    refine ⟨4480899201073337761967473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974532268097783682623297 4480899201073337761967473)
                    ·
                      refine ⟨3360674400805003321475605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4480899201073337761967473 3360674400805003321475605)
                      ·
                        rfl

theorem cell23_6544890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_6544890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544890 prefixEnd_6544890 := by exact prefixLift 6544890
  have htrace : WordTrace (prefixWord ++ tailWord_6544890) baseStart_6544890 baseEnd_6544890 := by
    simpa [prefixWord, tailWord_6544890, baseEnd_6544890] using wordTrace_append hprefix tailTrace_6544890
  have hstable : (prefixWord ++ tailWord_6544890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544890).length < 2 ^ (prefixWord ++ tailWord_6544890).sum := by decide
  have hdescent : baseEnd_6544890 < baseStart_6544890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544930 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_6544930 : Nat := 118140960795 + 6544930 * 2 ^ 59
def prefixEnd_6544930 : Nat := 4983230072969 + 3 ^ 40 * 6544930 * 2
def baseEnd_6544930 : Nat := 373410548892353684997269

theorem tailTrace_6544930 : CollatzResearch.WordTrace tailWord_6544930 prefixEnd_6544930 373410548892353684997269 := by
  unfold tailWord_6544930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678302044710967474424061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159142138785895913265130829 59678302044710967474424061)
  ·
    refine ⟨22379363266766612802909023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59678302044710967474424061 22379363266766612802909023)
    ·
      refine ⟨33569044900149919204363535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22379363266766612802909023 33569044900149919204363535)
      ·
        refine ⟨50353567350224878806545303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33569044900149919204363535 50353567350224878806545303)
        ·
          refine ⟨75530351025337318209817955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50353567350224878806545303 75530351025337318209817955)
          ·
            refine ⟨113295526538005977314726933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75530351025337318209817955 113295526538005977314726933)
            ·
              refine ⟨5310727806469030186627825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113295526538005977314726933 5310727806469030186627825)
              ·
                refine ⟨3983045854851772639970869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310727806469030186627825 3983045854851772639970869)
                ·
                  refine ⟨373410548892353684997269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983045854851772639970869 373410548892353684997269)
                  ·
                    rfl

theorem cell23_6544930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_6544930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544930 prefixEnd_6544930 := by exact prefixLift 6544930
  have htrace : WordTrace (prefixWord ++ tailWord_6544930) baseStart_6544930 baseEnd_6544930 := by
    simpa [prefixWord, tailWord_6544930, baseEnd_6544930] using wordTrace_append hprefix tailTrace_6544930
  have hstable : (prefixWord ++ tailWord_6544930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544930).length < 2 ^ (prefixWord ++ tailWord_6544930).sum := by decide
  have hdescent : baseEnd_6544930 < baseStart_6544930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544939 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 8]
def baseStart_6544939 : Nat := 118140960795 + 6544939 * 2 ^ 59
def prefixEnd_6544939 : Nat := 4983230072969 + 3 ^ 40 * 6544939 * 2
def baseEnd_6544939 : Nat := 1120233187119024543254293

theorem tailTrace_6544939 : CollatzResearch.WordTrace tailWord_6544939 prefixEnd_6544939 1120233187119024543254293 := by
  unfold tailWord_6544939
  simp only [CollatzResearch.WordTrace]
  refine ⟨238713536435811264434773871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159142357623874176289849247 238713536435811264434773871)
  ·
    refine ⟨358070304653716896652160807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238713536435811264434773871 358070304653716896652160807)
    ·
      refine ⟨537105456980575344978241211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358070304653716896652160807 537105456980575344978241211)
      ·
        refine ⟨805658185470863017467361817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537105456980575344978241211 805658185470863017467361817)
        ·
          refine ⟨604243639103147263100521363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805658185470863017467361817 604243639103147263100521363)
          ·
            refine ⟨906365458654720894650782045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604243639103147263100521363 906365458654720894650782045)
            ·
              refine ⟨339887046995520335494043267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906365458654720894650782045 339887046995520335494043267)
              ·
                refine ⟨509830570493280503241064901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339887046995520335494043267 509830570493280503241064901)
                ·
                  refine ⟨95593231967490094357699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 509830570493280503241064901 95593231967490094357699669)
                  ·
                    refine ⟨1120233187119024543254293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95593231967490094357699669 1120233187119024543254293)
                    ·
                      rfl

theorem cell23_6544939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_6544939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544939 prefixEnd_6544939 := by exact prefixLift 6544939
  have htrace : WordTrace (prefixWord ++ tailWord_6544939) baseStart_6544939 baseEnd_6544939 := by
    simpa [prefixWord, tailWord_6544939, baseEnd_6544939] using wordTrace_append hprefix tailTrace_6544939
  have hstable : (prefixWord ++ tailWord_6544939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544939).length < 2 ^ (prefixWord ++ tailWord_6544939).sum := by decide
  have hdescent : baseEnd_6544939 < baseStart_6544939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6544946 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6544946 : Nat := 118140960795 + 6544946 * 2 ^ 59
def prefixEnd_6544946 : Nat := 4983230072969 + 3 ^ 40 * 6544946 * 2
def baseEnd_6544946 : Nat := 3360703155721655102375347

theorem tailTrace_6544946 : CollatzResearch.WordTrace tailWord_6544946 prefixEnd_6544946 3360703155721655102375347 := by
  unfold tailWord_6544946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678447936696476157569673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159142527831190603086852461 59678447936696476157569673)
  ·
    refine ⟨44758835952522357118177255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59678447936696476157569673 44758835952522357118177255)
    ·
      refine ⟨67138253928783535677265883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44758835952522357118177255 67138253928783535677265883)
      ·
        refine ⟨100707380893175303515898825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67138253928783535677265883 100707380893175303515898825)
        ·
          refine ⟨75530535669881477636924119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100707380893175303515898825 75530535669881477636924119)
          ·
            refine ⟨113295803504822216455386179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75530535669881477636924119 113295803504822216455386179)
            ·
              refine ⟨169943705257233324683079269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113295803504822216455386179 169943705257233324683079269)
              ·
                refine ⟨31864444735731248378077363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169943705257233324683079269 31864444735731248378077363)
                ·
                  refine ⟨47796667103596872567116045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31864444735731248378077363 47796667103596872567116045)
                  ·
                    refine ⟨17923750163848827212668517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47796667103596872567116045 17923750163848827212668517)
                    ·
                      refine ⟨3360703155721655102375347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17923750163848827212668517 3360703155721655102375347)
                      ·
                        rfl

theorem cell23_6544946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6544946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6544946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6544946 prefixEnd_6544946 := by exact prefixLift 6544946
  have htrace : WordTrace (prefixWord ++ tailWord_6544946) baseStart_6544946 baseEnd_6544946 := by
    simpa [prefixWord, tailWord_6544946, baseEnd_6544946] using wordTrace_append hprefix tailTrace_6544946
  have hstable : (prefixWord ++ tailWord_6544946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6544946).length < 2 ^ (prefixWord ++ tailWord_6544946).sum := by decide
  have hdescent : baseEnd_6544946 < baseStart_6544946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6544946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545033 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_6545033 : Nat := 118140960795 + 6545033 * 2 ^ 59
def prefixEnd_6545033 : Nat := 4983230072969 + 3 ^ 40 * 6545033 * 2
def baseEnd_6545033 : Nat := 1120249276179532087329149

theorem tailTrace_6545033 : CollatzResearch.WordTrace tailWord_6545033 prefixEnd_6545033 1120249276179532087329149 := by
  unfold tailWord_6545033
  simp only [CollatzResearch.WordTrace]
  refine ⟨238716964897470718488695753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159144643264980478992463835 238716964897470718488695753)
  ·
    refine ⟨179037723673103038866521815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238716964897470718488695753 179037723673103038866521815)
    ·
      refine ⟨268556585509654558299782723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179037723673103038866521815 268556585509654558299782723)
      ·
        refine ⟨402834878264481837449674085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268556585509654558299782723 402834878264481837449674085)
        ·
          refine ⟨75531539674590344521813891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402834878264481837449674085 75531539674590344521813891)
          ·
            refine ⟨113297309511885516782720837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75531539674590344521813891 113297309511885516782720837)
            ·
              refine ⟨21243245533478534396760157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113297309511885516782720837 21243245533478534396760157)
              ·
                refine ⟨7966217075054450398785059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21243245533478534396760157 7966217075054450398785059)
                ·
                  refine ⟨11949325612581675598177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7966217075054450398785059 11949325612581675598177589)
                  ·
                    refine ⟨1120249276179532087329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11949325612581675598177589 1120249276179532087329149)
                    ·
                      rfl

theorem cell23_6545033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_6545033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545033 prefixEnd_6545033 := by exact prefixLift 6545033
  have htrace : WordTrace (prefixWord ++ tailWord_6545033) baseStart_6545033 baseEnd_6545033 := by
    simpa [prefixWord, tailWord_6545033, baseEnd_6545033] using wordTrace_append hprefix tailTrace_6545033
  have hstable : (prefixWord ++ tailWord_6545033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545033).length < 2 ^ (prefixWord ++ tailWord_6545033).sum := by decide
  have hdescent : baseEnd_6545033 < baseStart_6545033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545047 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_6545047 : Nat := 118140960795 + 6545047 * 2 ^ 59
def prefixEnd_6545047 : Nat := 4983230072969 + 3 ^ 40 * 6545047 * 2
def baseEnd_6545047 : Nat := 3360755017267759207212383

theorem tailTrace_6545047 : CollatzResearch.WordTrace tailWord_6545047 prefixEnd_6545047 3360755017267759207212383 := by
  unfold tailWord_6545047
  simp only [CollatzResearch.WordTrace]
  refine ⟨238717475519419998879705395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159144983679613332586470263 238717475519419998879705395)
  ·
    refine ⟨358076213279129998319558093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238717475519419998879705395 358076213279129998319558093)
    ·
      refine ⟨134278579979673749369834285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358076213279129998319558093 134278579979673749369834285)
      ·
        refine ⟨50354467492377656013687857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134278579979673749369834285 50354467492377656013687857)
        ·
          refine ⟨37765850619283242010265893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50354467492377656013687857 37765850619283242010265893)
          ·
            refine ⟨7081096991115607876924855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37765850619283242010265893 7081096991115607876924855)
            ·
              refine ⟨10621645486673411815387283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081096991115607876924855 10621645486673411815387283)
              ·
                refine ⟨15932468230010117723080925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621645486673411815387283 15932468230010117723080925)
                ·
                  refine ⟨5974675586253794146155347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15932468230010117723080925 5974675586253794146155347)
                  ·
                    refine ⟨8962013379380691219233021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974675586253794146155347 8962013379380691219233021)
                    ·
                      refine ⟨3360755017267759207212383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962013379380691219233021 3360755017267759207212383)
                      ·
                        rfl

theorem cell23_6545047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_6545047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545047 prefixEnd_6545047 := by exact prefixLift 6545047
  have htrace : WordTrace (prefixWord ++ tailWord_6545047) baseStart_6545047 baseEnd_6545047 := by
    simpa [prefixWord, tailWord_6545047, baseEnd_6545047] using wordTrace_append hprefix tailTrace_6545047
  have hstable : (prefixWord ++ tailWord_6545047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545047).length < 2 ^ (prefixWord ++ tailWord_6545047).sum := by decide
  have hdescent : baseEnd_6545047 < baseStart_6545047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545053 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_6545053 : Nat := 118140960795 + 6545053 * 2 ^ 59
def prefixEnd_6545053 : Nat := 4983230072969 + 3 ^ 40 * 6545053 * 2
def baseEnd_6545053 : Nat := 3360758098151686183737355

theorem tailTrace_6545053 : CollatzResearch.WordTrace tailWord_6545053 prefixEnd_6545053 3360758098151686183737355 := by
  unfold tailWord_6545053
  simp only [CollatzResearch.WordTrace]
  refine ⟨238717694357398261904423813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159145129571598841269615875 238717694357398261904423813)
  ·
    refine ⟨44759567692012174107079465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238717694357398261904423813 44759567692012174107079465)
    ·
      refine ⟨33569675769009130580309599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44759567692012174107079465 33569675769009130580309599)
      ·
        refine ⟨50354513653513695870464399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33569675769009130580309599 50354513653513695870464399)
        ·
          refine ⟨75531770480270543805696599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50354513653513695870464399 75531770480270543805696599)
          ·
            refine ⟨113297655720405815708544899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75531770480270543805696599 113297655720405815708544899)
            ·
              refine ⟨169946483580608723562817349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113297655720405815708544899 169946483580608723562817349)
              ·
                refine ⟨31864965671364135668028253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169946483580608723562817349 31864965671364135668028253)
                ·
                  refine ⟨11949362126761550875510595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31864965671364135668028253 11949362126761550875510595)
                  ·
                    refine ⟨17924043190142326313265893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11949362126761550875510595 17924043190142326313265893)
                    ·
                      refine ⟨3360758098151686183737355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17924043190142326313265893 3360758098151686183737355)
                      ·
                        rfl

theorem cell23_6545053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_6545053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545053 prefixEnd_6545053 := by exact prefixLift 6545053
  have htrace : WordTrace (prefixWord ++ tailWord_6545053) baseStart_6545053 baseEnd_6545053 := by
    simpa [prefixWord, tailWord_6545053, baseEnd_6545053] using wordTrace_append hprefix tailTrace_6545053
  have hstable : (prefixWord ++ tailWord_6545053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545053).length < 2 ^ (prefixWord ++ tailWord_6545053).sum := by decide
  have hdescent : baseEnd_6545053 < baseStart_6545053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545098 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_6545098 : Nat := 118140960795 + 6545098 * 2 ^ 59
def prefixEnd_6545098 : Nat := 4983230072969 + 3 ^ 40 * 6545098 * 2
def baseEnd_6545098 : Nat := 3360781204781138507674649

theorem tailTrace_6545098 : CollatzResearch.WordTrace tailWord_6545098 prefixEnd_6545098 3360781204781138507674649 := by
  unfold tailWord_6545098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59679833910558808647452987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159146223761490156393207965 59679833910558808647452987)
  ·
    refine ⟨89519750865838212971179481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59679833910558808647452987 89519750865838212971179481)
    ·
      refine ⟨67139813149378659728384611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89519750865838212971179481 67139813149378659728384611)
      ·
        refine ⟨100709719724067989592576917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67139813149378659728384611 100709719724067989592576917)
        ·
          refine ⟨4720768112065687012152043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100709719724067989592576917 4720768112065687012152043)
          ·
            refine ⟨7081152168098530518228065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720768112065687012152043 7081152168098530518228065)
            ·
              refine ⟨5310864126073897888671049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7081152168098530518228065 5310864126073897888671049)
              ·
                refine ⟨3983148094555423416503287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310864126073897888671049 3983148094555423416503287)
                ·
                  refine ⟨5974722141833135124754931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983148094555423416503287 5974722141833135124754931)
                  ·
                    refine ⟨8962083212749702687132397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974722141833135124754931 8962083212749702687132397)
                    ·
                      refine ⟨3360781204781138507674649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962083212749702687132397 3360781204781138507674649)
                      ·
                        rfl

theorem cell23_6545098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_6545098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545098 prefixEnd_6545098 := by exact prefixLift 6545098
  have htrace : WordTrace (prefixWord ++ tailWord_6545098) baseStart_6545098 baseEnd_6545098 := by
    simpa [prefixWord, tailWord_6545098, baseEnd_6545098] using wordTrace_append hprefix tailTrace_6545098
  have hstable : (prefixWord ++ tailWord_6545098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545098).length < 2 ^ (prefixWord ++ tailWord_6545098).sum := by decide
  have hdescent : baseEnd_6545098 < baseStart_6545098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545127 : List Nat := [1, 1, 5, 4, 1, 1, 3, 7]
def baseStart_6545127 : Nat := 118140960795 + 6545127 * 2 ^ 59
def prefixEnd_6545127 : Nat := 4983230072969 + 3 ^ 40 * 6545127 * 2
def baseEnd_6545127 : Nat := 124473929471115514600445

theorem tailTrace_6545127 : CollatzResearch.WordTrace tailWord_6545127 prefixEnd_6545127 124473929471115514600445 := by
  unfold tailWord_6545127
  simp only [CollatzResearch.WordTrace]
  refine ⟨238720393359130172542617635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159146928906086781695078423 238720393359130172542617635)
  ·
    refine ⟨358080590038695258813926453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238720393359130172542617635 358080590038695258813926453)
    ·
      refine ⟨33570055316127680513805605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 358080590038695258813926453 33570055316127680513805605)
      ·
        refine ⟨6294385371773940096338551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33570055316127680513805605 6294385371773940096338551)
        ·
          refine ⟨9441578057660910144507827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294385371773940096338551 9441578057660910144507827)
          ·
            refine ⟨14162367086491365216761741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441578057660910144507827 14162367086491365216761741)
            ·
              refine ⟨5310887657434261956285653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14162367086491365216761741 5310887657434261956285653)
              ·
                refine ⟨124473929471115514600445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5310887657434261956285653 124473929471115514600445)
                ·
                  rfl

theorem cell23_6545127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 7].length) (baseStart_6545127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545127 prefixEnd_6545127 := by exact prefixLift 6545127
  have htrace : WordTrace (prefixWord ++ tailWord_6545127) baseStart_6545127 baseEnd_6545127 := by
    simpa [prefixWord, tailWord_6545127, baseEnd_6545127] using wordTrace_append hprefix tailTrace_6545127
  have hstable : (prefixWord ++ tailWord_6545127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545127).length < 2 ^ (prefixWord ++ tailWord_6545127).sum := by decide
  have hdescent : baseEnd_6545127 < baseStart_6545127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545153 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6545153 : Nat := 118140960795 + 6545153 * 2 ^ 59
def prefixEnd_6545153 : Nat := 4983230072969 + 3 ^ 40 * 6545153 * 2
def baseEnd_6545153 : Nat := 1120269815405711930828965

theorem tailTrace_6545153 : CollatzResearch.WordTrace tailWord_6545153 prefixEnd_6545153 1120269815405711930828965 := by
  unfold tailWord_6545153
  simp only [CollatzResearch.WordTrace]
  refine ⟨238721341657035978983064113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159147561104690652655376075 238721341657035978983064113)
  ·
    refine ⟨179041006242776984237298085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238721341657035978983064113 179041006242776984237298085)
    ·
      refine ⟨33570188670520684544493391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179041006242776984237298085 33570188670520684544493391)
      ·
        refine ⟨50355283005781026816740087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33570188670520684544493391 50355283005781026816740087)
        ·
          refine ⟨75532924508671540225110131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50355283005781026816740087 75532924508671540225110131)
          ·
            refine ⟨113299386763007310337665197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75532924508671540225110131 113299386763007310337665197)
            ·
              refine ⟨42487270036127741376624449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113299386763007310337665197 42487270036127741376624449)
              ·
                refine ⟨31865452527095806032468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42487270036127741376624449 31865452527095806032468337)
                ·
                  refine ⟨23899089395321854524351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31865452527095806032468337 23899089395321854524351253)
                  ·
                    refine ⟨1120269815405711930828965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23899089395321854524351253 1120269815405711930828965)
                    ·
                      rfl

theorem cell23_6545153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6545153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545153 prefixEnd_6545153 := by exact prefixLift 6545153
  have htrace : WordTrace (prefixWord ++ tailWord_6545153) baseStart_6545153 baseEnd_6545153 := by
    simpa [prefixWord, tailWord_6545153, baseEnd_6545153] using wordTrace_append hprefix tailTrace_6545153
  have hstable : (prefixWord ++ tailWord_6545153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545153).length < 2 ^ (prefixWord ++ tailWord_6545153).sum := by decide
  have hdescent : baseEnd_6545153 < baseStart_6545153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545158 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6545158 : Nat := 118140960795 + 6545158 * 2 ^ 59
def prefixEnd_6545158 : Nat := 4983230072969 + 3 ^ 40 * 6545158 * 2
def baseEnd_6545158 : Nat := 3360812013620408272924373

theorem tailTrace_6545158 : CollatzResearch.WordTrace tailWord_6545158 prefixEnd_6545158 3360812013620408272924373 := by
  unfold tailWord_6545158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460047625688058276156129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159147682681345243224664085 7460047625688058276156129)
  ·
    refine ⟨5595035719266043707117097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460047625688058276156129 5595035719266043707117097)
    ·
      refine ⟨4196276789449532780337823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5595035719266043707117097 4196276789449532780337823)
      ·
        refine ⟨6294415184174299170506735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196276789449532780337823 6294415184174299170506735)
        ·
          refine ⟨9441622776261448755760103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294415184174299170506735 9441622776261448755760103)
          ·
            refine ⟨14162434164392173133640155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441622776261448755760103 14162434164392173133640155)
            ·
              refine ⟨21243651246588259700460233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162434164392173133640155 21243651246588259700460233)
              ·
                refine ⟨15932738434941194775345175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21243651246588259700460233 15932738434941194775345175)
                ·
                  refine ⟨23899107652411792163017763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15932738434941194775345175 23899107652411792163017763)
                  ·
                    refine ⟨35848661478617688244526645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23899107652411792163017763 35848661478617688244526645)
                    ·
                      refine ⟨3360812013620408272924373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35848661478617688244526645 3360812013620408272924373)
                      ·
                        rfl

theorem cell23_6545158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6545158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545158 prefixEnd_6545158 := by exact prefixLift 6545158
  have htrace : WordTrace (prefixWord ++ tailWord_6545158) baseStart_6545158 baseEnd_6545158 := by
    simpa [prefixWord, tailWord_6545158, baseEnd_6545158] using wordTrace_append hprefix tailTrace_6545158
  have hstable : (prefixWord ++ tailWord_6545158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545158).length < 2 ^ (prefixWord ++ tailWord_6545158).sum := by decide
  have hdescent : baseEnd_6545158 < baseStart_6545158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545163 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3]
def baseStart_6545163 : Nat := 118140960795 + 6545163 * 2 ^ 59
def prefixEnd_6545163 : Nat := 4983230072969 + 3 ^ 40 * 6545163 * 2
def baseEnd_6545163 : Nat := 3360814581023680753361849

theorem tailTrace_6545163 : CollatzResearch.WordTrace tailWord_6545163 prefixEnd_6545163 3360814581023680753361849 := by
  unfold tailWord_6545163
  simp only [CollatzResearch.WordTrace]
  refine ⟨238721706386999750690928143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159147804257999833793952095 238721706386999750690928143)
  ·
    refine ⟨358082559580499626036392215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238721706386999750690928143 358082559580499626036392215)
    ·
      refine ⟨537123839370749439054588323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358082559580499626036392215 537123839370749439054588323)
      ·
        refine ⟨805685759056124158581882485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537123839370749439054588323 805685759056124158581882485)
        ·
          refine ⟨75533039911511639867051483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 805685759056124158581882485 75533039911511639867051483)
          ·
            refine ⟨113299559867267459800577225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75533039911511639867051483 113299559867267459800577225)
            ·
              refine ⟨84974669900450594850432919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113299559867267459800577225 84974669900450594850432919)
              ·
                refine ⟨127462004850675892275649379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84974669900450594850432919 127462004850675892275649379)
                ·
                  refine ⟨191193007276013838413474069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127462004850675892275649379 191193007276013838413474069)
                  ·
                    refine ⟨8962172216063148675631597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191193007276013838413474069 8962172216063148675631597)
                    ·
                      refine ⟨3360814581023680753361849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962172216063148675631597 3360814581023680753361849)
                      ·
                        rfl

theorem cell23_6545163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 3].length) (baseStart_6545163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545163 prefixEnd_6545163 := by exact prefixLift 6545163
  have htrace : WordTrace (prefixWord ++ tailWord_6545163) baseStart_6545163 baseEnd_6545163 := by
    simpa [prefixWord, tailWord_6545163, baseEnd_6545163] using wordTrace_append hprefix tailTrace_6545163
  have hstable : (prefixWord ++ tailWord_6545163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545163).length < 2 ^ (prefixWord ++ tailWord_6545163).sum := by decide
  have hdescent : baseEnd_6545163 < baseStart_6545163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545165 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6545165 : Nat := 118140960795 + 6545165 * 2 ^ 59
def prefixEnd_6545165 : Nat := 4983230072969 + 3 ^ 40 * 6545165 * 2
def baseEnd_6545165 : Nat := 1120271869328329915178947

theorem tailTrace_6545165 : CollatzResearch.WordTrace tailWord_6545165 prefixEnd_6545165 1120271869328329915178947 := by
  unfold tailWord_6545165
  simp only [CollatzResearch.WordTrace]
  refine ⟨238721779332992505032500949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159147852888661670021667299 238721779332992505032500949)
  ·
    refine ⟨5595041703117011836699241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 238721779332992505032500949 5595041703117011836699241)
    ·
      refine ⟨4196281277337758877524431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5595041703117011836699241 4196281277337758877524431)
      ·
        refine ⟨6294421916006638316286647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196281277337758877524431 6294421916006638316286647)
        ·
          refine ⟨9441632874009957474429971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294421916006638316286647 9441632874009957474429971)
          ·
            refine ⟨14162449311014936211644957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441632874009957474429971 14162449311014936211644957)
            ·
              refine ⟨5310918491630601079366859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14162449311014936211644957 5310918491630601079366859)
              ·
                refine ⟨7966377737445901619050289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310918491630601079366859 7966377737445901619050289)
                ·
                  refine ⟨5974783303084426214287717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966377737445901619050289 5974783303084426214287717)
                  ·
                    refine ⟨1120271869328329915178947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974783303084426214287717 1120271869328329915178947)
                    ·
                      rfl

theorem cell23_6545165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6545165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545165 prefixEnd_6545165 := by exact prefixLift 6545165
  have htrace : WordTrace (prefixWord ++ tailWord_6545165) baseStart_6545165 baseEnd_6545165 := by
    simpa [prefixWord, tailWord_6545165, baseEnd_6545165] using wordTrace_append hprefix tailTrace_6545165
  have hstable : (prefixWord ++ tailWord_6545165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545165).length < 2 ^ (prefixWord ++ tailWord_6545165).sum := by decide
  have hdescent : baseEnd_6545165 < baseStart_6545165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545183 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 7]
def baseStart_6545183 : Nat := 118140960795 + 6545183 * 2 ^ 59
def prefixEnd_6545183 : Nat := 4983230072969 + 3 ^ 40 * 6545183 * 2
def baseEnd_6545183 : Nat := 373424983404085630567973

theorem tailTrace_6545183 : CollatzResearch.WordTrace tailWord_6545183 prefixEnd_6545183 373424983404085630567973 := by
  unfold tailWord_6545183
  simp only [CollatzResearch.WordTrace]
  refine ⟨238722435846927294106656203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159148290564618196071104135 238722435846927294106656203)
  ·
    refine ⟨358083653770390941159984305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238722435846927294106656203 358083653770390941159984305)
    ·
      refine ⟨268562740327793205869988229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358083653770390941159984305 268562740327793205869988229)
      ·
        refine ⟨50355513811461226100622793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268562740327793205869988229 50355513811461226100622793)
        ·
          refine ⟨37766635358595919575467095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50355513811461226100622793 37766635358595919575467095)
          ·
            refine ⟨56649953037893879363200643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37766635358595919575467095 56649953037893879363200643)
            ·
              refine ⟨84974929556840819044800965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56649953037893879363200643 84974929556840819044800965)
              ·
                refine ⟨15932799291907653570900181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84974929556840819044800965 15932799291907653570900181)
                ·
                  refine ⟨373424983404085630567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15932799291907653570900181 373424983404085630567973)
                  ·
                    rfl

theorem cell23_6545183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 7].length) (baseStart_6545183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545183 prefixEnd_6545183 := by exact prefixLift 6545183
  have htrace : WordTrace (prefixWord ++ tailWord_6545183) baseStart_6545183 baseEnd_6545183 := by
    simpa [prefixWord, tailWord_6545183, baseEnd_6545183] using wordTrace_append hprefix tailTrace_6545183
  have hstable : (prefixWord ++ tailWord_6545183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545183).length < 2 ^ (prefixWord ++ tailWord_6545183).sum := by decide
  have hdescent : baseEnd_6545183 < baseStart_6545183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545223 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_6545223 : Nat := 118140960795 + 6545223 * 2 ^ 59
def prefixEnd_6545223 : Nat := 4983230072969 + 3 ^ 40 * 6545223 * 2
def baseEnd_6545223 : Nat := 3360845389862950518611573

theorem tailTrace_6545223 : CollatzResearch.WordTrace tailWord_6545223 prefixEnd_6545223 3360845389862950518611573 := by
  unfold tailWord_6545223
  simp only [CollatzResearch.WordTrace]
  refine ⟨238723894766782380938112323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159149263177854920625408215 238723894766782380938112323)
  ·
    refine ⟨358085842150173571407168485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238723894766782380938112323 358085842150173571407168485)
    ·
      refine ⟨67141095403157544638844091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358085842150173571407168485 67141095403157544638844091)
      ·
        refine ⟨100711643104736316958266137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67141095403157544638844091 100711643104736316958266137)
        ·
          refine ⟨75533732328552237718699603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100711643104736316958266137 75533732328552237718699603)
          ·
            refine ⟨113300598492828356578049405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75533732328552237718699603 113300598492828356578049405)
            ·
              refine ⟨42487724434810633716768527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113300598492828356578049405 42487724434810633716768527)
              ·
                refine ⟨63731586652215950575152791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42487724434810633716768527 63731586652215950575152791)
                ·
                  refine ⟨95597379978323925862729187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63731586652215950575152791 95597379978323925862729187)
                  ·
                    refine ⟨143396069967485888794093781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95597379978323925862729187 143396069967485888794093781)
                    ·
                      refine ⟨3360845389862950518611573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143396069967485888794093781 3360845389862950518611573)
                      ·
                        rfl

theorem cell23_6545223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_6545223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545223 prefixEnd_6545223 := by exact prefixLift 6545223
  have htrace : WordTrace (prefixWord ++ tailWord_6545223) baseStart_6545223 baseEnd_6545223 := by
    simpa [prefixWord, tailWord_6545223, baseEnd_6545223] using wordTrace_append hprefix tailTrace_6545223
  have hstable : (prefixWord ++ tailWord_6545223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545223).length < 2 ^ (prefixWord ++ tailWord_6545223).sum := by decide
  have hdescent : baseEnd_6545223 < baseStart_6545223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545228 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6545228 : Nat := 118140960795 + 6545228 * 2 ^ 59
def prefixEnd_6545228 : Nat := 4983230072969 + 3 ^ 40 * 6545228 * 2
def baseEnd_6545228 : Nat := 3360847957266222999049051

theorem tailTrace_6545228 : CollatzResearch.WordTrace tailWord_6545228 prefixEnd_6545228 3360847957266222999049051 := by
  unfold tailWord_6545228
  simp only [CollatzResearch.WordTrace]
  refine ⟨119362038565882133396022169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159149384754509511194696225 119362038565882133396022169)
  ·
    refine ⟨89521528924411600047016627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119362038565882133396022169 89521528924411600047016627)
    ·
      refine ⟨134282293386617400070524941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89521528924411600047016627 134282293386617400070524941)
      ·
        refine ⟨50355860019981525026446853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134282293386617400070524941 50355860019981525026446853)
        ·
          refine ⟨9441723753746535942458785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50355860019981525026446853 9441723753746535942458785)
          ·
            refine ⟨7081292815309901956844089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9441723753746535942458785 7081292815309901956844089)
            ·
              refine ⟨5310969611482426467633067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7081292815309901956844089 5310969611482426467633067)
              ·
                refine ⟨7966454417223639701449601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310969611482426467633067 7966454417223639701449601)
                ·
                  refine ⟨5974840812917729776087201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966454417223639701449601 5974840812917729776087201)
                  ·
                    refine ⟨4481130609688297332065401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974840812917729776087201 4481130609688297332065401)
                    ·
                      refine ⟨3360847957266222999049051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481130609688297332065401 3360847957266222999049051)
                      ·
                        rfl

theorem cell23_6545228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6545228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545228 prefixEnd_6545228 := by exact prefixLift 6545228
  have htrace : WordTrace (prefixWord ++ tailWord_6545228) baseStart_6545228 baseEnd_6545228 := by
    simpa [prefixWord, tailWord_6545228, baseEnd_6545228] using wordTrace_append hprefix tailTrace_6545228
  have hstable : (prefixWord ++ tailWord_6545228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545228).length < 2 ^ (prefixWord ++ tailWord_6545228).sum := by decide
  have hdescent : baseEnd_6545228 < baseStart_6545228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545304 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6545304 : Nat := 118140960795 + 6545304 * 2 ^ 59
def prefixEnd_6545304 : Nat := 4983230072969 + 3 ^ 40 * 6545304 * 2
def baseEnd_6545304 : Nat := 3360886981795964701698701

theorem tailTrace_6545304 : CollatzResearch.WordTrace tailWord_6545304 prefixEnd_6545304 3360886981795964701698701 := by
  unfold tailWord_6545304
  simp only [CollatzResearch.WordTrace]
  refine ⟨119363424539744465885905483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159151232719659287847873977 119363424539744465885905483)
  ·
    refine ⟨179045136809616698828858225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119363424539744465885905483 179045136809616698828858225)
    ·
      refine ⟨134283852607212524121643669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179045136809616698828858225 134283852607212524121643669)
      ·
        refine ⟨6294555590963087068202047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134283852607212524121643669 6294555590963087068202047)
        ·
          refine ⟨9441833386444630602303071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294555590963087068202047 9441833386444630602303071)
          ·
            refine ⟨14162750079666945903454607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441833386444630602303071 14162750079666945903454607)
            ·
              refine ⟨21244125119500418855181911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162750079666945903454607 21244125119500418855181911)
              ·
                refine ⟨31866187679250628282772867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21244125119500418855181911 31866187679250628282772867)
                ·
                  refine ⟨47799281518875942424159301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31866187679250628282772867 47799281518875942424159301)
                  ·
                    refine ⟨8962365284789239204529869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47799281518875942424159301 8962365284789239204529869)
                    ·
                      refine ⟨3360886981795964701698701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962365284789239204529869 3360886981795964701698701)
                      ·
                        rfl

theorem cell23_6545304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6545304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545304 prefixEnd_6545304 := by exact prefixLift 6545304
  have htrace : WordTrace (prefixWord ++ tailWord_6545304) baseStart_6545304 baseEnd_6545304 := by
    simpa [prefixWord, tailWord_6545304, baseEnd_6545304] using wordTrace_append hprefix tailTrace_6545304
  have hstable : (prefixWord ++ tailWord_6545304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545304).length < 2 ^ (prefixWord ++ tailWord_6545304).sum := by decide
  have hdescent : baseEnd_6545304 < baseStart_6545304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545311 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 1, 4]
def baseStart_6545311 : Nat := 118140960795 + 6545311 * 2 ^ 59
def prefixEnd_6545311 : Nat := 4983230072969 + 3 ^ 40 * 6545311 * 2
def baseEnd_6545311 : Nat := 1120296858720182058103723

theorem tailTrace_6545311 : CollatzResearch.WordTrace tailWord_6545311 prefixEnd_6545311 1120296858720182058103723 := by
  unfold tailWord_6545311
  simp only [CollatzResearch.WordTrace]
  refine ⟨238727104390463571967315787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159151402926975714644877191 238727104390463571967315787)
  ·
    refine ⟨358090656585695357950973681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238727104390463571967315787 358090656585695357950973681)
    ·
      refine ⟨268567992439271518463230261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358090656585695357950973681 268567992439271518463230261)
      ·
        refine ⟨25178249291181704855927837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268567992439271518463230261 25178249291181704855927837)
        ·
          refine ⟨9441843484193139320972939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25178249291181704855927837 9441843484193139320972939)
          ·
            refine ⟨14162765226289708981459409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441843484193139320972939 14162765226289708981459409)
            ·
              refine ⟨10622073919717281736094557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14162765226289708981459409 10622073919717281736094557)
              ·
                refine ⟨3983277719893980651035459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10622073919717281736094557 3983277719893980651035459)
                ·
                  refine ⟨5974916579840970976553189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983277719893980651035459 5974916579840970976553189)
                  ·
                    refine ⟨1120296858720182058103723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974916579840970976553189 1120296858720182058103723)
                    ·
                      rfl

theorem cell23_6545311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_6545311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545311 prefixEnd_6545311 := by exact prefixLift 6545311
  have htrace : WordTrace (prefixWord ++ tailWord_6545311) baseStart_6545311 baseEnd_6545311 := by
    simpa [prefixWord, tailWord_6545311, baseEnd_6545311] using wordTrace_append hprefix tailTrace_6545311
  have hstable : (prefixWord ++ tailWord_6545311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545311).length < 2 ^ (prefixWord ++ tailWord_6545311).sum := by decide
  have hdescent : baseEnd_6545311 < baseStart_6545311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545327 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 4, 3, 2]
def baseStart_6545327 : Nat := 118140960795 + 6545327 * 2 ^ 59
def prefixEnd_6545327 : Nat := 4983230072969 + 3 ^ 40 * 6545327 * 2
def baseEnd_6545327 : Nat := 3360898791851018111711095

theorem tailTrace_6545327 : CollatzResearch.WordTrace tailWord_6545327 prefixEnd_6545327 3360898791851018111711095 := by
  unfold tailWord_6545327
  simp only [CollatzResearch.WordTrace]
  refine ⟨238727687958405606699898235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159151791972270404466598823 238727687958405606699898235)
  ·
    refine ⟨358091531937608410049847353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238727687958405606699898235 358091531937608410049847353)
    ·
      refine ⟨268568648953206307537385515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358091531937608410049847353 268568648953206307537385515)
      ·
        refine ⟨402852973429809461306078273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268568648953206307537385515 402852973429809461306078273)
        ·
          refine ⟨302139730072357095979558705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402852973429809461306078273 302139730072357095979558705)
          ·
            refine ⟨226604797554267821984669029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302139730072357095979558705 226604797554267821984669029)
            ·
              refine ⟨42488399541425216622125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226604797554267821984669029 42488399541425216622125443)
              ·
                refine ⟨63732599312137824933188165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42488399541425216622125443 63732599312137824933188165)
                ·
                  refine ⟨11949862371025842174972781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63732599312137824933188165 11949862371025842174972781)
                  ·
                    refine ⟨4481198389134690815614793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11949862371025842174972781 4481198389134690815614793)
                    ·
                      refine ⟨3360898791851018111711095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481198389134690815614793 3360898791851018111711095)
                      ·
                        rfl

theorem cell23_6545327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3, 2].length) (baseStart_6545327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545327 prefixEnd_6545327 := by exact prefixLift 6545327
  have htrace : WordTrace (prefixWord ++ tailWord_6545327) baseStart_6545327 baseEnd_6545327 := by
    simpa [prefixWord, tailWord_6545327, baseEnd_6545327] using wordTrace_append hprefix tailTrace_6545327
  have hstable : (prefixWord ++ tailWord_6545327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545327).length < 2 ^ (prefixWord ++ tailWord_6545327).sum := by decide
  have hdescent : baseEnd_6545327 < baseStart_6545327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545378 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6545378 : Nat := 118140960795 + 6545378 * 2 ^ 59
def prefixEnd_6545378 : Nat := 4983230072969 + 3 ^ 40 * 6545378 * 2
def baseEnd_6545378 : Nat := 3360924979364397412173361

theorem tailTrace_6545378 : CollatzResearch.WordTrace tailWord_6545378 prefixEnd_6545378 3360924979364397412173361 := by
  unfold tailWord_6545378
  simp only [CollatzResearch.WordTrace]
  refine ⟨59682387020305210602501197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159153032054147228273336525 59682387020305210602501197)
  ·
    refine ⟨22380895132614453975937949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59682387020305210602501197 22380895132614453975937949)
    ·
      refine ⟨8392835674730420240976731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22380895132614453975937949 8392835674730420240976731)
      ·
        refine ⟨12589253512095630361465097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8392835674730420240976731 12589253512095630361465097)
        ·
          refine ⟨9441940134071722771098823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12589253512095630361465097 9441940134071722771098823)
          ·
            refine ⟨14162910201107584156648235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441940134071722771098823 14162910201107584156648235)
            ·
              refine ⟨21244365301661376234972353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162910201107584156648235 21244365301661376234972353)
              ·
                refine ⟨15933273976246032176229265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21244365301661376234972353 15933273976246032176229265)
                ·
                  refine ⟨11949955482184524132171949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15933273976246032176229265 11949955482184524132171949)
                  ·
                    refine ⟨4481233305819196549564481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11949955482184524132171949 4481233305819196549564481)
                    ·
                      refine ⟨3360924979364397412173361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481233305819196549564481 3360924979364397412173361)
                      ·
                        rfl

theorem cell23_6545378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6545378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545378 prefixEnd_6545378 := by exact prefixLift 6545378
  have htrace : WordTrace (prefixWord ++ tailWord_6545378) baseStart_6545378 baseEnd_6545378 := by
    simpa [prefixWord, tailWord_6545378, baseEnd_6545378] using wordTrace_append hprefix tailTrace_6545378
  have hstable : (prefixWord ++ tailWord_6545378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545378).length < 2 ^ (prefixWord ++ tailWord_6545378).sum := by decide
  have hdescent : baseEnd_6545378 < baseStart_6545378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545401 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_6545401 : Nat := 118140960795 + 6545401 * 2 ^ 59
def prefixEnd_6545401 : Nat := 4983230072969 + 3 ^ 40 * 6545401 * 2
def baseEnd_6545401 : Nat := 1120312263139816940728585

theorem tailTrace_6545401 : CollatzResearch.WordTrace tailWord_6545401 prefixEnd_6545401 1120312263139816940728585 := by
  unfold tailWord_6545401
  simp only [CollatzResearch.WordTrace]
  refine ⟨238730386960137517338092057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159153591306758344892061371 238730386960137517338092057)
  ·
    refine ⟨179047790220103138003569043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238730386960137517338092057 179047790220103138003569043)
    ·
      refine ⟨268571685330154707005353565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179047790220103138003569043 268571685330154707005353565)
      ·
        refine ⟨100714381998808015127007587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268571685330154707005353565 100714381998808015127007587)
        ·
          refine ⟨151071572998212022690511381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100714381998808015127007587 151071572998212022690511381)
          ·
            refine ⟨7081479984291188563617721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151071572998212022690511381 7081479984291188563617721)
            ·
              refine ⟨5311109988218391422713291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7081479984291188563617721 5311109988218391422713291)
              ·
                refine ⟨7966664982327587134069937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311109988218391422713291 7966664982327587134069937)
                ·
                  refine ⟨5974998736745690350552453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966664982327587134069937 5974998736745690350552453)
                  ·
                    refine ⟨1120312263139816940728585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974998736745690350552453 1120312263139816940728585)
                    ·
                      rfl

theorem cell23_6545401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_6545401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545401 prefixEnd_6545401 := by exact prefixLift 6545401
  have htrace : WordTrace (prefixWord ++ tailWord_6545401) baseStart_6545401 baseEnd_6545401 := by
    simpa [prefixWord, tailWord_6545401, baseEnd_6545401] using wordTrace_append hprefix tailTrace_6545401
  have hstable : (prefixWord ++ tailWord_6545401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545401).length < 2 ^ (prefixWord ++ tailWord_6545401).sum := by decide
  have hdescent : baseEnd_6545401 < baseStart_6545401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545428 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6545428 : Nat := 118140960795 + 6545428 * 2 ^ 59
def prefixEnd_6545428 : Nat := 4983230072969 + 3 ^ 40 * 6545428 * 2
def baseEnd_6545428 : Nat := 3360950653397122216548131

theorem tailTrace_6545428 : CollatzResearch.WordTrace tailWord_6545428 prefixEnd_6545428 3360950653397122216548131 := by
  unfold tailWord_6545428
  simp only [CollatzResearch.WordTrace]
  refine ⟨119365685865519850474662469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159154247820693133966216625 119365685865519850474662469)
  ·
    refine ⟨22381066099784971963999213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119365685865519850474662469 22381066099784971963999213)
    ·
      refine ⟨8392899787419364486499705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22381066099784971963999213 8392899787419364486499705)
      ·
        refine ⟨6294674840564523364874779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8392899787419364486499705 6294674840564523364874779)
        ·
          refine ⟨9442012260846785047312169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294674840564523364874779 9442012260846785047312169)
          ·
            refine ⟨7081509195635088785484127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9442012260846785047312169 7081509195635088785484127)
            ·
              refine ⟨10622263793452633178226191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081509195635088785484127 10622263793452633178226191)
              ·
                refine ⟨15933395690178949767339287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10622263793452633178226191 15933395690178949767339287)
                ·
                  refine ⟨23900093535268424651008931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15933395690178949767339287 23900093535268424651008931)
                  ·
                    refine ⟨35850140302902636976513397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23900093535268424651008931 35850140302902636976513397)
                    ·
                      refine ⟨3360950653397122216548131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35850140302902636976513397 3360950653397122216548131)
                      ·
                        rfl

theorem cell23_6545428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6545428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545428 prefixEnd_6545428 := by exact prefixLift 6545428
  have htrace : WordTrace (prefixWord ++ tailWord_6545428) baseStart_6545428 baseEnd_6545428 := by
    simpa [prefixWord, tailWord_6545428, baseEnd_6545428] using wordTrace_append hprefix tailTrace_6545428
  have hstable : (prefixWord ++ tailWord_6545428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545428).length < 2 ^ (prefixWord ++ tailWord_6545428).sum := by decide
  have hdescent : baseEnd_6545428 < baseStart_6545428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545457 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_6545457 : Nat := 118140960795 + 6545457 * 2 ^ 59
def prefixEnd_6545457 : Nat := 4983230072969 + 3 ^ 40 * 6545457 * 2
def baseEnd_6545457 : Nat := 1120321848112034201028499

theorem tailTrace_6545457 : CollatzResearch.WordTrace tailWord_6545457 prefixEnd_6545457 1120321848112034201028499 := by
  unfold tailWord_6545457
  simp only [CollatzResearch.WordTrace]
  refine ⟨238732429447934638902130625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159154952965289759268087083 238732429447934638902130625)
  ·
    refine ⟨179049322085950979176597969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238732429447934638902130625 179049322085950979176597969)
    ·
      refine ⟨134286991564463234382448477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179049322085950979176597969 134286991564463234382448477)
      ·
        refine ⟨50357621836673712893418179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134286991564463234382448477 50357621836673712893418179)
        ·
          refine ⟨75536432755010569340127269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50357621836673712893418179 75536432755010569340127269)
          ·
            refine ⟨14163081141564481751273863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75536432755010569340127269 14163081141564481751273863)
            ·
              refine ⟨21244621712346722626910795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14163081141564481751273863 21244621712346722626910795)
              ·
                refine ⟨31866932568520083940366193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21244621712346722626910795 31866932568520083940366193)
                ·
                  refine ⟨23900199426390062955274645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31866932568520083940366193 23900199426390062955274645)
                  ·
                    refine ⟨1120321848112034201028499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23900199426390062955274645 1120321848112034201028499)
                    ·
                      rfl

theorem cell23_6545457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_6545457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545457 prefixEnd_6545457 := by exact prefixLift 6545457
  have htrace : WordTrace (prefixWord ++ tailWord_6545457) baseStart_6545457 baseEnd_6545457 := by
    simpa [prefixWord, tailWord_6545457, baseEnd_6545457] using wordTrace_append hprefix tailTrace_6545457
  have hstable : (prefixWord ++ tailWord_6545457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545457).length < 2 ^ (prefixWord ++ tailWord_6545457).sum := by decide
  have hdescent : baseEnd_6545457 < baseStart_6545457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545497 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_6545497 : Nat := 118140960795 + 6545497 * 2 ^ 59
def prefixEnd_6545497 : Nat := 4983230072969 + 3 ^ 40 * 6545497 * 2
def baseEnd_6545497 : Nat := 3360986083562282446585313

theorem tailTrace_6545497 : CollatzResearch.WordTrace tailWord_6545497 prefixEnd_6545497 3360986083562282446585313 := by
  unfold tailWord_6545497
  simp only [CollatzResearch.WordTrace]
  refine ⟨238733888367789725733586745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159155925578526483822391163 238733888367789725733586745)
  ·
    refine ⟨179050416275842294300190059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238733888367789725733586745 179050416275842294300190059)
    ·
      refine ⟨268575624413763441450285089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179050416275842294300190059 268575624413763441450285089)
      ·
        refine ⟨201431718310322581087713817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268575624413763441450285089 201431718310322581087713817)
        ·
          refine ⟨151073788732741935815785363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201431718310322581087713817 151073788732741935815785363)
          ·
            refine ⟨226610683099112903723678045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151073788732741935815785363 226610683099112903723678045)
            ·
              refine ⟨84979006162167338896379267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226610683099112903723678045 84979006162167338896379267)
              ·
                refine ⟨127468509243251008344568901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84979006162167338896379267 127468509243251008344568901)
                ·
                  refine ⟨23900345483109564064606669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127468509243251008344568901 23900345483109564064606669)
                  ·
                    refine ⟨8962629556166086524227501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23900345483109564064606669 8962629556166086524227501)
                    ·
                      refine ⟨3360986083562282446585313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962629556166086524227501 3360986083562282446585313)
                      ·
                        rfl

theorem cell23_6545497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_6545497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545497 prefixEnd_6545497 := by exact prefixLift 6545497
  have htrace : WordTrace (prefixWord ++ tailWord_6545497) baseStart_6545497 baseEnd_6545497 := by
    simpa [prefixWord, tailWord_6545497, baseEnd_6545497] using wordTrace_append hprefix tailTrace_6545497
  have hstable : (prefixWord ++ tailWord_6545497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545497).length < 2 ^ (prefixWord ++ tailWord_6545497).sum := by decide
  have hdescent : baseEnd_6545497 < baseStart_6545497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545504 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 5]
def baseStart_6545504 : Nat := 118140960795 + 6545504 * 2 ^ 59
def prefixEnd_6545504 : Nat := 4983230072969 + 3 ^ 40 * 6545504 * 2
def baseEnd_6545504 : Nat := 373443297547429324355309

theorem tailTrace_6545504 : CollatzResearch.WordTrace tailWord_6545504 prefixEnd_6545504 373443297547429324355309 := by
  unfold tailWord_6545504
  simp only [CollatzResearch.WordTrace]
  refine ⟨119367071839382182964545783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159156095785842910619394377 119367071839382182964545783)
  ·
    refine ⟨179050607759073274446818675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119367071839382182964545783 179050607759073274446818675)
    ·
      refine ⟨268575911638609911670228013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179050607759073274446818675 268575911638609911670228013)
      ·
        refine ⟨100715966864478716876335505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268575911638609911670228013 100715966864478716876335505)
        ·
          refine ⟨75536975148359037657251629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100715966864478716876335505 75536975148359037657251629)
          ·
            refine ⟨28326365680634639121469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75536975148359037657251629 28326365680634639121469361)
            ·
              refine ⟨21244774260475979341102021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28326365680634639121469361 21244774260475979341102021)
              ·
                refine ⟨3983395173839246126456629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21244774260475979341102021 3983395173839246126456629)
                ·
                  refine ⟨373443297547429324355309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983395173839246126456629 373443297547429324355309)
                  ·
                    rfl

theorem cell23_6545504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 5].length) (baseStart_6545504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545504 prefixEnd_6545504 := by exact prefixLift 6545504
  have htrace : WordTrace (prefixWord ++ tailWord_6545504) baseStart_6545504 baseEnd_6545504 := by
    simpa [prefixWord, tailWord_6545504, baseEnd_6545504] using wordTrace_append hprefix tailTrace_6545504
  have hstable : (prefixWord ++ tailWord_6545504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545504).length < 2 ^ (prefixWord ++ tailWord_6545504).sum := by decide
  have hdescent : baseEnd_6545504 < baseStart_6545504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545517 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_6545517 : Nat := 118140960795 + 6545517 * 2 ^ 59
def prefixEnd_6545517 : Nat := 4983230072969 + 3 ^ 40 * 6545517 * 2
def baseEnd_6545517 : Nat := 1120332117725124122778407

theorem tailTrace_6545517 : CollatzResearch.WordTrace tailWord_6545517 prefixEnd_6545517 1120332117725124122778407 := by
  unfold tailWord_6545517
  simp only [CollatzResearch.WordTrace]
  refine ⟨238734617827717269149314805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159156411885144846099543203 238734617827717269149314805)
  ·
    refine ⟨22381370421348493982748263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238734617827717269149314805 22381370421348493982748263)
    ·
      refine ⟨33572055632022740974122395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22381370421348493982748263 33572055632022740974122395)
      ·
        refine ⟨50358083448034111461183593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33572055632022740974122395 50358083448034111461183593)
        ·
          refine ⟨37768562586025583595887695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50358083448034111461183593 37768562586025583595887695)
          ·
            refine ⟨56652843879038375393831543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37768562586025583595887695 56652843879038375393831543)
            ·
              refine ⟨84979265818557563090747315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56652843879038375393831543 84979265818557563090747315)
              ·
                refine ⟨127468898727836344636120973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84979265818557563090747315 127468898727836344636120973)
                ·
                  refine ⟨47800837022938629238545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127468898727836344636120973 47800837022938629238545365)
                  ·
                    refine ⟨1120332117725124122778407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47800837022938629238545365 1120332117725124122778407)
                    ·
                      rfl

theorem cell23_6545517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_6545517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545517 prefixEnd_6545517 := by exact prefixLift 6545517
  have htrace : WordTrace (prefixWord ++ tailWord_6545517) baseStart_6545517 baseEnd_6545517 := by
    simpa [prefixWord, tailWord_6545517, baseEnd_6545517] using wordTrace_append hprefix tailTrace_6545517
  have hstable : (prefixWord ++ tailWord_6545517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545517).length < 2 ^ (prefixWord ++ tailWord_6545517).sum := by decide
  have hdescent : baseEnd_6545517 < baseStart_6545517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545591 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_6545591 : Nat := 118140960795 + 6545591 * 2 ^ 59
def prefixEnd_6545591 : Nat := 4983230072969 + 3 ^ 40 * 6545591 * 2
def baseEnd_6545591 : Nat := 3361034350743805078809881

theorem tailTrace_6545591 : CollatzResearch.WordTrace tailWord_6545591 prefixEnd_6545591 3361034350743805078809881 := by
  unfold tailWord_6545591
  simp only [CollatzResearch.WordTrace]
  refine ⟨238737316829449179787508627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159158211219632786525005751 238737316829449179787508627)
  ·
    refine ⟨358105975244173769681262941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238737316829449179787508627 358105975244173769681262941)
    ·
      refine ⟨134289740716565163630473603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358105975244173769681262941 134289740716565163630473603)
      ·
        refine ⟨201434611074847745445710405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134289740716565163630473603 201434611074847745445710405)
        ·
          refine ⟨37768989576533952271070701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201434611074847745445710405 37768989576533952271070701)
          ·
            refine ⟨14163371091200232101651513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37768989576533952271070701 14163371091200232101651513)
            ·
              refine ⟨10622528318400174076238635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14163371091200232101651513 10622528318400174076238635)
              ·
                refine ⟨15933792477600261114357953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10622528318400174076238635 15933792477600261114357953)
                ·
                  refine ⟨11950344358200195835768465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15933792477600261114357953 11950344358200195835768465)
                  ·
                    refine ⟨8962758268650146876826349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11950344358200195835768465 8962758268650146876826349)
                    ·
                      refine ⟨3361034350743805078809881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962758268650146876826349 3361034350743805078809881)
                      ·
                        rfl

theorem cell23_6545591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_6545591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545591 prefixEnd_6545591 := by exact prefixLift 6545591
  have htrace : WordTrace (prefixWord ++ tailWord_6545591) baseStart_6545591 baseEnd_6545591 := by
    simpa [prefixWord, tailWord_6545591, baseEnd_6545591] using wordTrace_append hprefix tailTrace_6545591
  have hstable : (prefixWord ++ tailWord_6545591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545591).length < 2 ^ (prefixWord ++ tailWord_6545591).sum := by decide
  have hdescent : baseEnd_6545591 < baseStart_6545591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6545597 : Nat := 118140960795 + 6545597 * 2 ^ 59
def prefixEnd_6545597 : Nat := 4983230072969 + 3 ^ 40 * 6545597 * 2
def baseEnd_6545597 : Nat := 3361037431627732055334853

theorem tailTrace_6545597 : CollatzResearch.WordTrace tailWord_6545597 prefixEnd_6545597 3361037431627732055334853 := by
  unfold tailWord_6545597
  simp only [CollatzResearch.WordTrace]
  refine ⟨238737535667427442812227045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159158357111618295208151363 238737535667427442812227045)
  ·
    refine ⟨44763287937642645527292571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238737535667427442812227045 44763287937642645527292571)
    ·
      refine ⟨67144931906463968290938857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44763287937642645527292571 67144931906463968290938857)
      ·
        refine ⟨50358698929847976218204143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67144931906463968290938857 50358698929847976218204143)
        ·
          refine ⟨75538048394771964327306215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50358698929847976218204143 75538048394771964327306215)
          ·
            refine ⟨113307072592157946490959323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75538048394771964327306215 113307072592157946490959323)
            ·
              refine ⟨169960608888236919736438985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113307072592157946490959323 169960608888236919736438985)
              ·
                refine ⟨127470456666177689802329239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169960608888236919736438985 127470456666177689802329239)
                ·
                  refine ⟨191205684999266534703493859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127470456666177689802329239 191205684999266534703493859)
                  ·
                    refine ⟨286808527498899802055240789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191205684999266534703493859 286808527498899802055240789)
                    ·
                      refine ⟨3361037431627732055334853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286808527498899802055240789 3361037431627732055334853)
                      ·
                        rfl

theorem cell23_6545597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6545597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545597 prefixEnd_6545597 := by exact prefixLift 6545597
  have htrace : WordTrace (prefixWord ++ tailWord_6545597) baseStart_6545597 baseEnd_6545597 := by
    simpa [prefixWord, tailWord_6545597, baseEnd_6545597] using wordTrace_append hprefix tailTrace_6545597
  have hstable : (prefixWord ++ tailWord_6545597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545597).length < 2 ^ (prefixWord ++ tailWord_6545597).sum := by decide
  have hdescent : baseEnd_6545597 < baseStart_6545597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545624 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_6545624 : Nat := 118140960795 + 6545624 * 2 ^ 59
def prefixEnd_6545624 : Nat := 4983230072969 + 3 ^ 40 * 6545624 * 2
def baseEnd_6545624 : Nat := 1120350431868467816565743

theorem tailTrace_6545624 : CollatzResearch.WordTrace tailWord_6545624 prefixEnd_6545624 1120350431868467816565743 := by
  unfold tailWord_6545624
  simp only [CollatzResearch.WordTrace]
  refine ⟨119369260219164813211729963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159159013625553084282306617 119369260219164813211729963)
  ·
    refine ⟨179053890328747219817594945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119369260219164813211729963 179053890328747219817594945)
    ·
      refine ⟨134290417746560414863196209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179053890328747219817594945 134290417746560414863196209)
      ·
        refine ⟨100717813309920311147397157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134290417746560414863196209 100717813309920311147397157)
        ·
          refine ⟨18884589995610058340136967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100717813309920311147397157 18884589995610058340136967)
          ·
            refine ⟨28326884993415087510205451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884589995610058340136967 28326884993415087510205451)
            ·
              refine ⟨42490327490122631265308177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28326884993415087510205451 42490327490122631265308177)
              ·
                refine ⟨31867745617591973448981133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42490327490122631265308177 31867745617591973448981133)
                ·
                  refine ⟨11950404606596990043367925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31867745617591973448981133 11950404606596990043367925)
                  ·
                    refine ⟨1120350431868467816565743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11950404606596990043367925 1120350431868467816565743)
                    ·
                      rfl

theorem cell23_6545624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_6545624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545624 prefixEnd_6545624 := by exact prefixLift 6545624
  have htrace : WordTrace (prefixWord ++ tailWord_6545624) baseStart_6545624 baseEnd_6545624 := by
    simpa [prefixWord, tailWord_6545624, baseEnd_6545624] using wordTrace_append hprefix tailTrace_6545624
  have hstable : (prefixWord ++ tailWord_6545624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545624).length < 2 ^ (prefixWord ++ tailWord_6545624).sum := by decide
  have hdescent : baseEnd_6545624 < baseStart_6545624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_6545627 : Nat := 118140960795 + 6545627 * 2 ^ 59
def prefixEnd_6545627 : Nat := 4983230072969 + 3 ^ 40 * 6545627 * 2
def baseEnd_6545627 : Nat := 3361052836047366937959715

theorem tailTrace_6545627 : CollatzResearch.WordTrace tailWord_6545627 prefixEnd_6545627 3361052836047366937959715 := by
  unfold tailWord_6545627
  simp only [CollatzResearch.WordTrace]
  refine ⟨238738629857318757935819135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159159086571545838623879423 238738629857318757935819135)
  ·
    refine ⟨358107944785978136903728703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238738629857318757935819135 358107944785978136903728703)
    ·
      refine ⟨537161917178967205355593055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358107944785978136903728703 537161917178967205355593055)
      ·
        refine ⟨805742875768450808033389583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537161917178967205355593055 805742875768450808033389583)
        ·
          refine ⟨1208614313652676212050084375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805742875768450808033389583 1208614313652676212050084375)
          ·
            refine ⟨1812921470479014318075126563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208614313652676212050084375 1812921470479014318075126563)
            ·
              refine ⟨2719382205718521477112689845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812921470479014318075126563 2719382205718521477112689845)
              ·
                refine ⟨254942081786111388479314673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2719382205718521477112689845 254942081786111388479314673)
                ·
                  refine ⟨191206561339583541359486005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254942081786111388479314673 191206561339583541359486005)
                  ·
                    refine ⟨17925615125585957002451813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 191206561339583541359486005 17925615125585957002451813)
                    ·
                      refine ⟨3361052836047366937959715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17925615125585957002451813 3361052836047366937959715)
                      ·
                        rfl

theorem cell23_6545627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_6545627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545627 prefixEnd_6545627 := by exact prefixLift 6545627
  have htrace : WordTrace (prefixWord ++ tailWord_6545627) baseStart_6545627 baseEnd_6545627 := by
    simpa [prefixWord, tailWord_6545627, baseEnd_6545627] using wordTrace_append hprefix tailTrace_6545627
  have hstable : (prefixWord ++ tailWord_6545627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545627).length < 2 ^ (prefixWord ++ tailWord_6545627).sum := by decide
  have hdescent : baseEnd_6545627 < baseStart_6545627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545644 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_6545644 : Nat := 118140960795 + 6545644 * 2 ^ 59
def prefixEnd_6545644 : Nat := 4983230072969 + 3 ^ 40 * 6545644 * 2
def baseEnd_6545644 : Nat := 3361061565218493371447137

theorem tailTrace_6545644 : CollatzResearch.WordTrace tailWord_6545644 prefixEnd_6545644 3361061565218493371447137 := by
  unfold tailWord_6545644
  simp only [CollatzResearch.WordTrace]
  refine ⟨119369624949128584919593993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159159499932171446559458657 119369624949128584919593993)
  ·
    refine ⟨89527218711846438689695495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119369624949128584919593993 89527218711846438689695495)
    ·
      refine ⟨134290828067769658034543243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89527218711846438689695495 134290828067769658034543243)
      ·
        refine ⟨201436242101654487051814865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134290828067769658034543243 201436242101654487051814865)
        ·
          refine ⟨151077181576240865288861149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201436242101654487051814865 151077181576240865288861149)
          ·
            refine ⟨56653943091090324483322931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151077181576240865288861149 56653943091090324483322931)
            ·
              refine ⟨84980914636635486724984397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56653943091090324483322931 84980914636635486724984397)
              ·
                refine ⟨31867842988738307521869149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84980914636635486724984397 31867842988738307521869149)
                ·
                  refine ⟨11950441120776865320700931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31867842988738307521869149 11950441120776865320700931)
                  ·
                    refine ⟨17925661681165297981051397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11950441120776865320700931 17925661681165297981051397)
                    ·
                      refine ⟨3361061565218493371447137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17925661681165297981051397 3361061565218493371447137)
                      ·
                        rfl

theorem cell23_6545644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_6545644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545644 prefixEnd_6545644 := by exact prefixLift 6545644
  have htrace : WordTrace (prefixWord ++ tailWord_6545644) baseStart_6545644 baseEnd_6545644 := by
    simpa [prefixWord, tailWord_6545644, baseEnd_6545644] using wordTrace_append hprefix tailTrace_6545644
  have hstable : (prefixWord ++ tailWord_6545644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545644).length < 2 ^ (prefixWord ++ tailWord_6545644).sum := by decide
  have hdescent : baseEnd_6545644 < baseStart_6545644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545658 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_6545658 : Nat := 118140960795 + 6545658 * 2 ^ 59
def prefixEnd_6545658 : Nat := 4983230072969 + 3 ^ 40 * 6545658 * 2
def baseEnd_6545658 : Nat := 1120356251315885438890691

theorem tailTrace_6545658 : CollatzResearch.WordTrace tailWord_6545658 prefixEnd_6545658 1120356251315885438890691 := by
  unfold tailWord_6545658
  simp only [CollatzResearch.WordTrace]
  refine ⟨59684940130051612557549407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159159840346804300153465085 59684940130051612557549407)
  ·
    refine ⟨89527410195077418836324111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59684940130051612557549407 89527410195077418836324111)
    ·
      refine ⟨134291115292616128254486167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89527410195077418836324111 134291115292616128254486167)
      ·
        refine ⟨201436672938924192381729251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134291115292616128254486167 201436672938924192381729251)
        ·
          refine ⟨302155009408386288572593877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201436672938924192381729251 302155009408386288572593877)
          ·
            refine ⟨7081758033009053638420169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 302155009408386288572593877 7081758033009053638420169)
            ·
              refine ⟨5311318524756790228815127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7081758033009053638420169 5311318524756790228815127)
              ·
                refine ⟨7966977787135185343222691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311318524756790228815127 7966977787135185343222691)
                ·
                  refine ⟨11950466680702778014834037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7966977787135185343222691 11950466680702778014834037)
                  ·
                    refine ⟨1120356251315885438890691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11950466680702778014834037 1120356251315885438890691)
                    ·
                      rfl

theorem cell23_6545658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_6545658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545658 prefixEnd_6545658 := by exact prefixLift 6545658
  have htrace : WordTrace (prefixWord ++ tailWord_6545658) baseStart_6545658 baseEnd_6545658 := by
    simpa [prefixWord, tailWord_6545658, baseEnd_6545658] using wordTrace_append hprefix tailTrace_6545658
  have hstable : (prefixWord ++ tailWord_6545658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545658).length < 2 ^ (prefixWord ++ tailWord_6545658).sum := by decide
  have hdescent : baseEnd_6545658 < baseStart_6545658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545667 : List Nat := [1, 1, 1, 3, 2, 3, 12]
def baseStart_6545667 : Nat := 118140960795 + 6545667 * 2 ^ 59
def prefixEnd_6545667 : Nat := 4983230072969 + 3 ^ 40 * 6545667 * 2
def baseEnd_6545667 : Nat := 41494733028068478783451

theorem tailTrace_6545667 : CollatzResearch.WordTrace tailWord_6545667 prefixEnd_6545667 41494733028068478783451 := by
  unfold tailWord_6545667
  simp only [CollatzResearch.WordTrace]
  refine ⟨238740088777173844767275255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159160059184782563178183503 238740088777173844767275255)
  ·
    refine ⟨358110133165760767150912883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238740088777173844767275255 358110133165760767150912883)
    ·
      refine ⟨537165199748641150726369325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358110133165760767150912883 537165199748641150726369325)
      ·
        refine ⟨201436949905740431522388497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537165199748641150726369325 201436949905740431522388497)
        ·
          refine ⟨151077712429305323641791373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201436949905740431522388497 151077712429305323641791373)
          ·
            refine ⟨56654142160989496365671765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151077712429305323641791373 56654142160989496365671765)
            ·
              refine ⟨41494733028068478783451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56654142160989496365671765 41494733028068478783451)
              ·
                rfl

theorem cell23_6545667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 12].length) (baseStart_6545667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545667 prefixEnd_6545667 := by exact prefixLift 6545667
  have htrace : WordTrace (prefixWord ++ tailWord_6545667) baseStart_6545667 baseEnd_6545667 := by
    simpa [prefixWord, tailWord_6545667, baseEnd_6545667] using wordTrace_append hprefix tailTrace_6545667
  have hstable : (prefixWord ++ tailWord_6545667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545667).length < 2 ^ (prefixWord ++ tailWord_6545667).sum := by decide
  have hdescent : baseEnd_6545667 < baseStart_6545667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545674 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_6545674 : Nat := 118140960795 + 6545674 * 2 ^ 59
def prefixEnd_6545674 : Nat := 4983230072969 + 3 ^ 40 * 6545674 * 2
def baseEnd_6545674 : Nat := 3361076969638128254071999

theorem tailTrace_6545674 : CollatzResearch.WordTrace tailWord_6545674 prefixEnd_6545674 3361076969638128254071999 := by
  unfold tailWord_6545674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59685086022037121240695019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159160229392098989975186717 59685086022037121240695019)
  ·
    refine ⟨89527629033055681861042529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59685086022037121240695019 89527629033055681861042529)
    ·
      refine ⟨67145721774791761395781897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89527629033055681861042529 67145721774791761395781897)
      ·
        refine ⟨50359291331093821046836423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67145721774791761395781897 50359291331093821046836423)
        ·
          refine ⟨75538936996640731570254635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50359291331093821046836423 75538936996640731570254635)
          ·
            refine ⟨113308405494961097355381953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75538936996640731570254635 113308405494961097355381953)
            ·
              refine ⟨84981304121220823016536465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113308405494961097355381953 84981304121220823016536465)
              ·
                refine ⟨63735978090915617262402349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84981304121220823016536465 63735978090915617262402349)
                ·
                  refine ⟨23900991784093356473400881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63735978090915617262402349 23900991784093356473400881)
                  ·
                    refine ⟨17925743838070017355050661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23900991784093356473400881 17925743838070017355050661)
                    ·
                      refine ⟨3361076969638128254071999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17925743838070017355050661 3361076969638128254071999)
                      ·
                        rfl

theorem cell23_6545674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_6545674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545674 prefixEnd_6545674 := by exact prefixLift 6545674
  have htrace : WordTrace (prefixWord ++ tailWord_6545674) baseStart_6545674 baseEnd_6545674 := by
    simpa [prefixWord, tailWord_6545674, baseEnd_6545674] using wordTrace_append hprefix tailTrace_6545674
  have hstable : (prefixWord ++ tailWord_6545674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545674).length < 2 ^ (prefixWord ++ tailWord_6545674).sum := by decide
  have hdescent : baseEnd_6545674 < baseStart_6545674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545688 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_6545688 : Nat := 118140960795 + 6545688 * 2 ^ 59
def prefixEnd_6545688 : Nat := 4983230072969 + 3 ^ 40 * 6545688 * 2
def baseEnd_6545688 : Nat := 1120361386122430399765645

theorem tailTrace_6545688 : CollatzResearch.WordTrace tailWord_6545688 prefixEnd_6545688 1120361386122430399765645 := by
  unfold tailWord_6545688
  simp only [CollatzResearch.WordTrace]
  refine ⟨119370427355048882676894859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159160569806731843569193145 119370427355048882676894859)
  ·
    refine ⟨179055641032573324015342289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119370427355048882676894859 179055641032573324015342289)
    ·
      refine ⟨134291730774429993011506717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179055641032573324015342289 134291730774429993011506717)
      ·
        refine ⟨50359399040411247379315019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134291730774429993011506717 50359399040411247379315019)
        ·
          refine ⟨75539098560616871068972529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50359399040411247379315019 75539098560616871068972529)
          ·
            refine ⟨56654323920462653301729397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75539098560616871068972529 56654323920462653301729397)
            ·
              refine ⟨5311342867543373747037131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56654323920462653301729397 5311342867543373747037131)
              ·
                refine ⟨7967014301315060620555697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311342867543373747037131 7967014301315060620555697)
                ·
                  refine ⟨5975260725986295465416773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7967014301315060620555697 5975260725986295465416773)
                  ·
                    refine ⟨1120361386122430399765645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975260725986295465416773 1120361386122430399765645)
                    ·
                      rfl

theorem cell23_6545688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_6545688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545688 prefixEnd_6545688 := by exact prefixLift 6545688
  have htrace : WordTrace (prefixWord ++ tailWord_6545688) baseStart_6545688 baseEnd_6545688 := by
    simpa [prefixWord, tailWord_6545688, baseEnd_6545688] using wordTrace_append hprefix tailTrace_6545688
  have hstable : (prefixWord ++ tailWord_6545688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545688).length < 2 ^ (prefixWord ++ tailWord_6545688).sum := by decide
  have hdescent : baseEnd_6545688 < baseStart_6545688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545698 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_6545698 : Nat := 118140960795 + 6545698 * 2 ^ 59
def prefixEnd_6545698 : Nat := 4983230072969 + 3 ^ 40 * 6545698 * 2
def baseEnd_6545698 : Nat := 3361089293173836160171889

theorem tailTrace_6545698 : CollatzResearch.WordTrace tailWord_6545698 prefixEnd_6545698 3361089293173836160171889 := by
  unfold tailWord_6545698
  simp only [CollatzResearch.WordTrace]
  refine ⟨59685304860015384265413437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159160812960041024707769165 59685304860015384265413437)
  ·
    refine ⟨22381989322505769099530039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59685304860015384265413437 22381989322505769099530039)
    ·
      refine ⟨33572983983758653649295059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22381989322505769099530039 33572983983758653649295059)
      ·
        refine ⟨50359475975637980473942589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33572983983758653649295059 50359475975637980473942589)
        ·
          refine ⟨18884803490864242677728471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50359475975637980473942589 18884803490864242677728471)
          ·
            refine ⟨28327205236296364016592707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884803490864242677728471 28327205236296364016592707)
            ·
              refine ⟨42490807854444546024889061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28327205236296364016592707 42490807854444546024889061)
              ·
                refine ⟨7967026472708352379666699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42490807854444546024889061 7967026472708352379666699)
                ·
                  refine ⟨11950539709062528569500049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7967026472708352379666699 11950539709062528569500049)
                  ·
                    refine ⟨8962904781796896427125037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11950539709062528569500049 8962904781796896427125037)
                    ·
                      refine ⟨3361089293173836160171889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962904781796896427125037 3361089293173836160171889)
                      ·
                        rfl

theorem cell23_6545698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_6545698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545698 prefixEnd_6545698 := by exact prefixLift 6545698
  have htrace : WordTrace (prefixWord ++ tailWord_6545698) baseStart_6545698 baseEnd_6545698 := by
    simpa [prefixWord, tailWord_6545698, baseEnd_6545698] using wordTrace_append hprefix tailTrace_6545698
  have hstable : (prefixWord ++ tailWord_6545698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545698).length < 2 ^ (prefixWord ++ tailWord_6545698).sum := by decide
  have hdescent : baseEnd_6545698 < baseStart_6545698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545711 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_6545711 : Nat := 118140960795 + 6545711 * 2 ^ 59
def prefixEnd_6545711 : Nat := 4983230072969 + 3 ^ 40 * 6545711 * 2
def baseEnd_6545711 : Nat := 3361095968422344609309329

theorem tailTrace_6545711 : CollatzResearch.WordTrace tailWord_6545711 prefixEnd_6545711 3361095968422344609309329 := by
  unfold tailWord_6545711
  simp only [CollatzResearch.WordTrace]
  refine ⟨238741693589014440281876987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159161129059342960187917991 238741693589014440281876987)
  ·
    refine ⟨358112540383521660422815481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238741693589014440281876987 358112540383521660422815481)
    ·
      refine ⟨268584405287641245317111611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358112540383521660422815481 268584405287641245317111611)
      ·
        refine ⟨402876607931461867975667417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268584405287641245317111611 402876607931461867975667417)
        ·
          refine ⟨302157455948596400981750563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402876607931461867975667417 302157455948596400981750563)
          ·
            refine ⟨453236183922894601472625845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302157455948596400981750563 453236183922894601472625845)
            ·
              refine ⟨42490892242771368888058673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 453236183922894601472625845 42490892242771368888058673)
              ·
                refine ⟨31868169182078526666044005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42490892242771368888058673 31868169182078526666044005)
                ·
                  refine ⟨5975281721639723749883251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31868169182078526666044005 5975281721639723749883251)
                  ·
                    refine ⟨8962922582459585624824877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5975281721639723749883251 8962922582459585624824877)
                    ·
                      refine ⟨3361095968422344609309329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962922582459585624824877 3361095968422344609309329)
                      ·
                        rfl

theorem cell23_6545711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_6545711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545711 prefixEnd_6545711 := by exact prefixLift 6545711
  have htrace : WordTrace (prefixWord ++ tailWord_6545711) baseStart_6545711 baseEnd_6545711 := by
    simpa [prefixWord, tailWord_6545711, baseEnd_6545711] using wordTrace_append hprefix tailTrace_6545711
  have hstable : (prefixWord ++ tailWord_6545711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545711).length < 2 ^ (prefixWord ++ tailWord_6545711).sum := by decide
  have hdescent : baseEnd_6545711 < baseStart_6545711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545724 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6545724 : Nat := 118140960795 + 6545724 * 2 ^ 59
def prefixEnd_6545724 : Nat := 4983230072969 + 3 ^ 40 * 6545724 * 2
def baseEnd_6545724 : Nat := 3361102643670853058446769

theorem tailTrace_6545724 : CollatzResearch.WordTrace tailWord_6545724 prefixEnd_6545724 3361102643670853058446769 := by
  unfold tailWord_6545724
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371083868983671751050113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159161445158644895668066817 119371083868983671751050113)
  ·
    refine ⟨89528312901737753813287585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119371083868983671751050113 89528312901737753813287585)
    ·
      refine ⟨67146234676303315359965689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89528312901737753813287585 67146234676303315359965689)
      ·
        refine ⟨50359676007227486519974267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67146234676303315359965689 50359676007227486519974267)
        ·
          refine ⟨75539514010841229779961401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50359676007227486519974267 75539514010841229779961401)
          ·
            refine ⟨56654635508130922334971051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75539514010841229779961401 56654635508130922334971051)
            ·
              refine ⟨84981953262196383502456577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56654635508130922334971051 84981953262196383502456577)
              ·
                refine ⟨63736464946647287626842433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84981953262196383502456577 63736464946647287626842433)
                ·
                  refine ⟨47802348709985465720131825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63736464946647287626842433 47802348709985465720131825)
                  ·
                    refine ⟨35851761532489099290098869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47802348709985465720131825 35851761532489099290098869)
                    ·
                      refine ⟨3361102643670853058446769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35851761532489099290098869 3361102643670853058446769)
                      ·
                        rfl

theorem cell23_6545724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6545724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545724 prefixEnd_6545724 := by exact prefixLift 6545724
  have htrace : WordTrace (prefixWord ++ tailWord_6545724) baseStart_6545724 baseEnd_6545724 := by
    simpa [prefixWord, tailWord_6545724, baseEnd_6545724] using wordTrace_append hprefix tailTrace_6545724
  have hstable : (prefixWord ++ tailWord_6545724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545724).length < 2 ^ (prefixWord ++ tailWord_6545724).sum := by decide
  have hdescent : baseEnd_6545724 < baseStart_6545724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545729 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6545729 : Nat := 118140960795 + 6545729 * 2 ^ 59
def prefixEnd_6545729 : Nat := 4983230072969 + 3 ^ 40 * 6545729 * 2
def baseEnd_6545729 : Nat := 3361105211074125538884247

theorem tailTrace_6545729 : CollatzResearch.WordTrace tailWord_6545729 prefixEnd_6545729 3361105211074125538884247 := by
  unfold tailWord_6545729
  simp only [CollatzResearch.WordTrace]
  refine ⟨238742350102949229356032241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159161566735299486237354827 238742350102949229356032241)
  ·
    refine ⟨179056762577211922017024181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238742350102949229356032241 179056762577211922017024181)
    ·
      refine ⟨16786571491613617689096017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179056762577211922017024181 16786571491613617689096017)
      ·
        refine ⟨12589928618710213266822013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16786571491613617689096017 12589928618710213266822013)
        ·
          refine ⟨4721223232016329975058255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12589928618710213266822013 4721223232016329975058255)
          ·
            refine ⟨7081834848024494962587383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721223232016329975058255 7081834848024494962587383)
            ·
              refine ⟨10622752272036742443881075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081834848024494962587383 10622752272036742443881075)
              ·
                refine ⟨15934128408055113665821613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10622752272036742443881075 15934128408055113665821613)
                ·
                  refine ⟨5975298153020667624683105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15934128408055113665821613 5975298153020667624683105)
                  ·
                    refine ⟨4481473614765500718512329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5975298153020667624683105 4481473614765500718512329)
                    ·
                      refine ⟨3361105211074125538884247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481473614765500718512329 3361105211074125538884247)
                      ·
                        rfl

theorem cell23_6545729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6545729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545729 prefixEnd_6545729 := by exact prefixLift 6545729
  have htrace : WordTrace (prefixWord ++ tailWord_6545729) baseStart_6545729 baseEnd_6545729 := by
    simpa [prefixWord, tailWord_6545729, baseEnd_6545729] using wordTrace_append hprefix tailTrace_6545729
  have hstable : (prefixWord ++ tailWord_6545729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545729).length < 2 ^ (prefixWord ++ tailWord_6545729).sum := by decide
  have hdescent : baseEnd_6545729 < baseStart_6545729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545745 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_6545745 : Nat := 118140960795 + 6545745 * 2 ^ 59
def prefixEnd_6545745 : Nat := 4983230072969 + 3 ^ 40 * 6545745 * 2
def baseEnd_6545745 : Nat := 3361113426764597476284173

theorem tailTrace_6545745 : CollatzResearch.WordTrace tailWord_6545745 prefixEnd_6545745 3361113426764597476284173 := by
  unfold tailWord_6545745
  simp only [CollatzResearch.WordTrace]
  refine ⟨238742933670891264088614689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159161955780594176059076459 238742933670891264088614689)
  ·
    refine ⟨179057200253168448066461017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238742933670891264088614689 179057200253168448066461017)
    ·
      refine ⟨134292900189876336049845763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179057200253168448066461017 134292900189876336049845763)
      ·
        refine ⟨201439350284814504074768645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134292900189876336049845763 201439350284814504074768645)
        ·
          refine ⟨37769878178402719514019121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201439350284814504074768645 37769878178402719514019121)
          ·
            refine ⟨28327408633802039635514341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37769878178402719514019121 28327408633802039635514341)
            ·
              refine ⟨5311389118837882431658939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28327408633802039635514341 5311389118837882431658939)
              ·
                refine ⟨7967083678256823647488409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311389118837882431658939 7967083678256823647488409)
                ·
                  refine ⟨5975312758692617735616307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7967083678256823647488409 5975312758692617735616307)
                  ·
                    refine ⟨8962969138038926603424461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5975312758692617735616307 8962969138038926603424461)
                    ·
                      refine ⟨3361113426764597476284173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8962969138038926603424461 3361113426764597476284173)
                      ·
                        rfl

theorem cell23_6545745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_6545745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545745 prefixEnd_6545745 := by exact prefixLift 6545745
  have htrace : WordTrace (prefixWord ++ tailWord_6545745) baseStart_6545745 baseEnd_6545745 := by
    simpa [prefixWord, tailWord_6545745, baseEnd_6545745] using wordTrace_append hprefix tailTrace_6545745
  have hstable : (prefixWord ++ tailWord_6545745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545745).length < 2 ^ (prefixWord ++ tailWord_6545745).sum := by decide
  have hdescent : baseEnd_6545745 < baseStart_6545745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545768 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6545768 : Nat := 118140960795 + 6545768 * 2 ^ 59
def prefixEnd_6545768 : Nat := 4983230072969 + 3 ^ 40 * 6545768 * 2
def baseEnd_6545768 : Nat := 3361125236819650886296567

theorem tailTrace_6545768 : CollatzResearch.WordTrace tailWord_6545768 prefixEnd_6545768 3361125236819650886296567 := by
  unfold tailWord_6545768
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371886274903969508350979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159162515033205292677801305 119371886274903969508350979)
  ·
    refine ⟨179057829412355954262526469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119371886274903969508350979 179057829412355954262526469)
    ·
      refine ⟨33573343014816741424223713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179057829412355954262526469 33573343014816741424223713)
      ·
        refine ⟨25180007261112556068167785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33573343014816741424223713 25180007261112556068167785)
        ·
          refine ⟨18885005445834417051125839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25180007261112556068167785 18885005445834417051125839)
          ·
            refine ⟨28327508168751625576688759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18885005445834417051125839 28327508168751625576688759)
            ·
              refine ⟨42491262253127438365033139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28327508168751625576688759 42491262253127438365033139)
              ·
                refine ⟨63736893379691157547549709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42491262253127438365033139 63736893379691157547549709)
                ·
                  refine ⟨23901335017384184080331141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63736893379691157547549709 23901335017384184080331141)
                  ·
                    refine ⟨4481500315759534515062089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23901335017384184080331141 4481500315759534515062089)
                    ·
                      refine ⟨3361125236819650886296567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481500315759534515062089 3361125236819650886296567)
                      ·
                        rfl

theorem cell23_6545768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6545768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545768 prefixEnd_6545768 := by exact prefixLift 6545768
  have htrace : WordTrace (prefixWord ++ tailWord_6545768) baseStart_6545768 baseEnd_6545768 := by
    simpa [prefixWord, tailWord_6545768, baseEnd_6545768] using wordTrace_append hprefix tailTrace_6545768
  have hstable : (prefixWord ++ tailWord_6545768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545768).length < 2 ^ (prefixWord ++ tailWord_6545768).sum := by decide
  have hdescent : baseEnd_6545768 < baseStart_6545768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545772 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_6545772 : Nat := 118140960795 + 6545772 * 2 ^ 59
def prefixEnd_6545772 : Nat := 4983230072969 + 3 ^ 40 * 6545772 * 2
def baseEnd_6545772 : Nat := 3361127290742268870646549

theorem tailTrace_6545772 : CollatzResearch.WordTrace tailWord_6545772 prefixEnd_6545772 3361127290742268870646549 := by
  unfold tailWord_6545772
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371959220896723849923785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159162612294528965133231713 119371959220896723849923785)
  ·
    refine ⟨89528969415672542887442839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119371959220896723849923785 89528969415672542887442839)
    ·
      refine ⟨134293454123508814331164259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89528969415672542887442839 134293454123508814331164259)
      ·
        refine ⟨201440181185263221496746389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134293454123508814331164259 201440181185263221496746389)
        ·
          refine ⟨9442508493059213507659987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201440181185263221496746389 9442508493059213507659987)
          ·
            refine ⟨14163762739588820261489981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442508493059213507659987 14163762739588820261489981)
            ·
              refine ⟨5311411027345807598058743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14163762739588820261489981 5311411027345807598058743)
              ·
                refine ⟨7967116541018711397088115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311411027345807598058743 7967116541018711397088115)
                ·
                  refine ⟨11950674811528067095632173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7967116541018711397088115 11950674811528067095632173)
                  ·
                    refine ⟨4481503054323025160862065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11950674811528067095632173 4481503054323025160862065)
                    ·
                      refine ⟨3361127290742268870646549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481503054323025160862065 3361127290742268870646549)
                      ·
                        rfl

theorem cell23_6545772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_6545772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545772 prefixEnd_6545772 := by exact prefixLift 6545772
  have htrace : WordTrace (prefixWord ++ tailWord_6545772) baseStart_6545772 baseEnd_6545772 := by
    simpa [prefixWord, tailWord_6545772, baseEnd_6545772] using wordTrace_append hprefix tailTrace_6545772
  have hstable : (prefixWord ++ tailWord_6545772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545772).length < 2 ^ (prefixWord ++ tailWord_6545772).sum := by decide
  have hdescent : baseEnd_6545772 < baseStart_6545772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545791 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 5]
def baseStart_6545791 : Nat := 118140960795 + 6545791 * 2 ^ 59
def prefixEnd_6545791 : Nat := 4983230072969 + 3 ^ 40 * 6545791 * 2
def baseEnd_6545791 : Nat := 373459671874967144034329

theorem tailTrace_6545791 : CollatzResearch.WordTrace tailWord_6545791 prefixEnd_6545791 373459671874967144034329 := by
  unfold tailWord_6545791
  simp only [CollatzResearch.WordTrace]
  refine ⟨238744611428724613944789227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159163074285816409296526151 238744611428724613944789227)
  ·
    refine ⟨358116917143086920917183841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238744611428724613944789227 358116917143086920917183841)
    ·
      refine ⟨268587687857315190687887881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358116917143086920917183841 268587687857315190687887881)
      ·
        refine ⟨201440765892986393015915911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268587687857315190687887881 201440765892986393015915911)
        ·
          refine ⟨302161148839479589523873867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201440765892986393015915911 302161148839479589523873867)
          ·
            refine ⟨453241723259219384285810801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302161148839479589523873867 453241723259219384285810801)
            ·
              refine ⟨339931292444414538214358101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453241723259219384285810801 339931292444414538214358101)
              ·
                refine ⟨3983569833332982869699509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 339931292444414538214358101 3983569833332982869699509)
                ·
                  refine ⟨373459671874967144034329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983569833332982869699509 373459671874967144034329)
                  ·
                    rfl

theorem cell23_6545791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 5].length) (baseStart_6545791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545791 prefixEnd_6545791 := by exact prefixLift 6545791
  have htrace : WordTrace (prefixWord ++ tailWord_6545791) baseStart_6545791 baseEnd_6545791 := by
    simpa [prefixWord, tailWord_6545791, baseEnd_6545791] using wordTrace_append hprefix tailTrace_6545791
  have hstable : (prefixWord ++ tailWord_6545791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545791).length < 2 ^ (prefixWord ++ tailWord_6545791).sum := by decide
  have hdescent : baseEnd_6545791 < baseStart_6545791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545801 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_6545801 : Nat := 118140960795 + 6545801 * 2 ^ 59
def prefixEnd_6545801 : Nat := 4983230072969 + 3 ^ 40 * 6545801 * 2
def baseEnd_6545801 : Nat := 3361142181681249257183915

theorem tailTrace_6545801 : CollatzResearch.WordTrace tailWord_6545801 prefixEnd_6545801 3361142181681249257183915 := by
  unfold tailWord_6545801
  simp only [CollatzResearch.WordTrace]
  refine ⟨238744976158688385652653257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159163317439125590435102171 238744976158688385652653257)
  ·
    refine ⟨179058732119016289239489943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238744976158688385652653257 179058732119016289239489943)
    ·
      refine ⟨268588098178524433859234915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179058732119016289239489943 268588098178524433859234915)
      ·
        refine ⟨402882147267786650788852373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268588098178524433859234915 402882147267786650788852373)
        ·
          refine ⟨18885100653177499255727455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 402882147267786650788852373 18885100653177499255727455)
          ·
            refine ⟨28327650979766248883591183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18885100653177499255727455 28327650979766248883591183)
            ·
              refine ⟨42491476469649373325386775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28327650979766248883591183 42491476469649373325386775)
              ·
                refine ⟨63737214704474059988080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42491476469649373325386775 63737214704474059988080163)
                ·
                  refine ⟨95605822056711089982120245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63737214704474059988080163 95605822056711089982120245)
                  ·
                    refine ⟨8963045817816664685823773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95605822056711089982120245 8963045817816664685823773)
                    ·
                      refine ⟨3361142181681249257183915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963045817816664685823773 3361142181681249257183915)
                      ·
                        rfl

theorem cell23_6545801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_6545801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545801 prefixEnd_6545801 := by exact prefixLift 6545801
  have htrace : WordTrace (prefixWord ++ tailWord_6545801) baseStart_6545801 baseEnd_6545801 := by
    simpa [prefixWord, tailWord_6545801, baseEnd_6545801] using wordTrace_append hprefix tailTrace_6545801
  have hstable : (prefixWord ++ tailWord_6545801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545801).length < 2 ^ (prefixWord ++ tailWord_6545801).sum := by decide
  have hdescent : baseEnd_6545801 < baseStart_6545801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545802 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6545802 : Nat := 118140960795 + 6545802 * 2 ^ 59
def prefixEnd_6545802 : Nat := 4983230072969 + 3 ^ 40 * 6545802 * 2
def baseEnd_6545802 : Nat := 3361142695161903753271411

theorem tailTrace_6545802 : CollatzResearch.WordTrace tailWord_6545802 prefixEnd_6545802 3361142695161903753271411 := by
  unfold tailWord_6545802
  simp only [CollatzResearch.WordTrace]
  refine ⟨59686253157921190705859915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159163341754456508548959773 59686253157921190705859915)
  ·
    refine ⟨89529379736881786058789873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59686253157921190705859915 89529379736881786058789873)
    ·
      refine ⟨67147034802661339544092405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89529379736881786058789873 67147034802661339544092405)
      ·
        refine ⟨6295034512749500582258663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67147034802661339544092405 6295034512749500582258663)
        ·
          refine ⟨9442551769124250873387995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295034512749500582258663 9442551769124250873387995)
          ·
            refine ⟨14163827653686376310081993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442551769124250873387995 14163827653686376310081993)
            ·
              refine ⟨10622870740264782232561495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14163827653686376310081993 10622870740264782232561495)
              ·
                refine ⟨15934306110397173348842243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10622870740264782232561495 15934306110397173348842243)
                ·
                  refine ⟨23901459165595760023263365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15934306110397173348842243 23901459165595760023263365)
                  ·
                    refine ⟨4481523593549205004361881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23901459165595760023263365 4481523593549205004361881)
                    ·
                      refine ⟨3361142695161903753271411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481523593549205004361881 3361142695161903753271411)
                      ·
                        rfl

theorem cell23_6545802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6545802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545802 prefixEnd_6545802 := by exact prefixLift 6545802
  have htrace : WordTrace (prefixWord ++ tailWord_6545802) baseStart_6545802 baseEnd_6545802 := by
    simpa [prefixWord, tailWord_6545802, baseEnd_6545802] using wordTrace_append hprefix tailTrace_6545802
  have hstable : (prefixWord ++ tailWord_6545802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545802).length < 2 ^ (prefixWord ++ tailWord_6545802).sum := by decide
  have hdescent : baseEnd_6545802 < baseStart_6545802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545968 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_6545968 : Nat := 118140960795 + 6545968 * 2 ^ 59
def prefixEnd_6545968 : Nat := 4983230072969 + 3 ^ 40 * 6545968 * 2
def baseEnd_6545968 : Nat := 3361227932950550103795647

theorem tailTrace_6545968 : CollatzResearch.WordTrace tailWord_6545968 prefixEnd_6545968 3361227932950550103795647 := by
  unfold tailWord_6545968
  simp only [CollatzResearch.WordTrace]
  refine ⟨119375533574541686586991279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159167378099388915449321705 119375533574541686586991279)
  ·
    refine ⟨179063300361812529880486919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119375533574541686586991279 179063300361812529880486919)
    ·
      refine ⟨268594950542718794820730379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179063300361812529880486919 268594950542718794820730379)
      ·
        refine ⟨402892425814078192231095569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268594950542718794820730379 402892425814078192231095569)
        ·
          refine ⟨302169319360558644173321677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402892425814078192231095569 302169319360558644173321677)
          ·
            refine ⟨113313494760209491564995629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302169319360558644173321677 113313494760209491564995629)
            ·
              refine ⟨42492560535078559336873361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113313494760209491564995629 42492560535078559336873361)
              ·
                refine ⟨31869420401308919502655021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42492560535078559336873361 31869420401308919502655021)
                ·
                  refine ⟨11951032650490844813495633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31869420401308919502655021 11951032650490844813495633)
                  ·
                    refine ⟨8963274487868133610121725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11951032650490844813495633 8963274487868133610121725)
                    ·
                      refine ⟨3361227932950550103795647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963274487868133610121725 3361227932950550103795647)
                      ·
                        rfl

theorem cell23_6545968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_6545968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545968 prefixEnd_6545968 := by exact prefixLift 6545968
  have htrace : WordTrace (prefixWord ++ tailWord_6545968) baseStart_6545968 baseEnd_6545968 := by
    simpa [prefixWord, tailWord_6545968, baseEnd_6545968] using wordTrace_append hprefix tailTrace_6545968
  have hstable : (prefixWord ++ tailWord_6545968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545968).length < 2 ^ (prefixWord ++ tailWord_6545968).sum := by decide
  have hdescent : baseEnd_6545968 < baseStart_6545968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545978 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_6545978 : Nat := 118140960795 + 6545978 * 2 ^ 59
def prefixEnd_6545978 : Nat := 4983230072969 + 3 ^ 40 * 6545978 * 2
def baseEnd_6545978 : Nat := 3361233067757095064670601

theorem tailTrace_6545978 : CollatzResearch.WordTrace tailWord_6545978 prefixEnd_6545978 3361233067757095064670601 := by
  unfold tailWord_6545978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59687857969761786220461647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159167621252698096587897725 59687857969761786220461647)
  ·
    refine ⟨89531786954642679330692471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59687857969761786220461647 89531786954642679330692471)
    ·
      refine ⟨134297680431964018996038707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89531786954642679330692471 134297680431964018996038707)
      ·
        refine ⟨201446520647946028494058061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134297680431964018996038707 201446520647946028494058061)
        ·
          refine ⟨75542445242979760685271773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201446520647946028494058061 75542445242979760685271773)
          ·
            refine ⟨28328416966117410256976915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75542445242979760685271773 28328416966117410256976915)
            ·
              refine ⟨42492625449176115385465373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28328416966117410256976915 42492625449176115385465373)
              ·
                refine ⟨15934734543441043269549515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42492625449176115385465373 15934734543441043269549515)
                ·
                  refine ⟨23902101815161564904324273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15934734543441043269549515 23902101815161564904324273)
                  ·
                    refine ⟨17926576361371173678243205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23902101815161564904324273 17926576361371173678243205)
                    ·
                      refine ⟨3361233067757095064670601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17926576361371173678243205 3361233067757095064670601)
                      ·
                        rfl

theorem cell23_6545978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_6545978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545978 prefixEnd_6545978 := by exact prefixLift 6545978
  have htrace : WordTrace (prefixWord ++ tailWord_6545978) baseStart_6545978 baseEnd_6545978 := by
    simpa [prefixWord, tailWord_6545978, baseEnd_6545978] using wordTrace_append hprefix tailTrace_6545978
  have hstable : (prefixWord ++ tailWord_6545978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545978).length < 2 ^ (prefixWord ++ tailWord_6545978).sum := by decide
  have hdescent : baseEnd_6545978 < baseStart_6545978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6545985 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6545985 : Nat := 118140960795 + 6545985 * 2 ^ 59
def prefixEnd_6545985 : Nat := 4983230072969 + 3 ^ 40 * 6545985 * 2
def baseEnd_6545985 : Nat := 3361236662121676537283069

theorem tailTrace_6545985 : CollatzResearch.WordTrace tailWord_6545985 prefixEnd_6545985 3361236662121676537283069 := by
  unfold tailWord_6545985
  simp only [CollatzResearch.WordTrace]
  refine ⟨238751687190021785077351409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159167791460014523384900939 238751687190021785077351409)
  ·
    refine ⟨179063765392516338808013557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238751687190021785077351409 179063765392516338808013557)
    ·
      refine ⟨16787228005548406763251271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179063765392516338808013557 16787228005548406763251271)
      ·
        refine ⟨25180842008322610144876907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16787228005548406763251271 25180842008322610144876907)
        ·
          refine ⟨37771263012483915217315361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25180842008322610144876907 37771263012483915217315361)
          ·
            refine ⟨28328447259362936412986521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37771263012483915217315361 28328447259362936412986521)
            ·
              refine ⟨21246335444522202309739891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28328447259362936412986521 21246335444522202309739891)
              ·
                refine ⟨31869503166783303464609837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21246335444522202309739891 31869503166783303464609837)
                ·
                  refine ⟨11951063687543738799228689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31869503166783303464609837 11951063687543738799228689)
                  ·
                    refine ⟨8963297765657804099421517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11951063687543738799228689 8963297765657804099421517)
                    ·
                      refine ⟨3361236662121676537283069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963297765657804099421517 3361236662121676537283069)
                      ·
                        rfl

theorem cell23_6545985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6545985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6545985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6545985 prefixEnd_6545985 := by exact prefixLift 6545985
  have htrace : WordTrace (prefixWord ++ tailWord_6545985) baseStart_6545985 baseEnd_6545985 := by
    simpa [prefixWord, tailWord_6545985, baseEnd_6545985] using wordTrace_append hprefix tailTrace_6545985
  have hstable : (prefixWord ++ tailWord_6545985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6545985).length < 2 ^ (prefixWord ++ tailWord_6545985).sum := by decide
  have hdescent : baseEnd_6545985 < baseStart_6545985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6545985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546032 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_6546032 : Nat := 118140960795 + 6546032 * 2 ^ 59
def prefixEnd_6546032 : Nat := 4983230072969 + 3 ^ 40 * 6546032 * 2
def baseEnd_6546032 : Nat := 3361260795712437853395353

theorem tailTrace_6546032 : CollatzResearch.WordTrace tailWord_6546032 prefixEnd_6546032 3361260795712437853395353 := by
  unfold tailWord_6546032
  simp only [CollatzResearch.WordTrace]
  refine ⟨119376700710425756052156175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159168934280567674736208233 119376700710425756052156175)
  ·
    refine ⟨179065051065638634078234263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119376700710425756052156175 179065051065638634078234263)
    ·
      refine ⟨268597576598457951117351395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179065051065638634078234263 268597576598457951117351395)
      ·
        refine ⟨402896364897686926676027093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268597576598457951117351395 402896364897686926676027093)
        ·
          refine ⟨9442883552289537343969385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 402896364897686926676027093 9442883552289537343969385)
          ·
            refine ⟨7082162664217153007977039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9442883552289537343969385 7082162664217153007977039)
            ·
              refine ⟨10623243996325729511965559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082162664217153007977039 10623243996325729511965559)
              ·
                refine ⟨15934865994488594267948339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10623243996325729511965559 15934865994488594267948339)
                ·
                  refine ⟨23902298991732891401922509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15934865994488594267948339 23902298991732891401922509)
                  ·
                    refine ⟨8963362121899834275720941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23902298991732891401922509 8963362121899834275720941)
                    ·
                      refine ⟨3361260795712437853395353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963362121899834275720941 3361260795712437853395353)
                      ·
                        rfl

theorem cell23_6546032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_6546032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546032 prefixEnd_6546032 := by exact prefixLift 6546032
  have htrace : WordTrace (prefixWord ++ tailWord_6546032) baseStart_6546032 baseEnd_6546032 := by
    simpa [prefixWord, tailWord_6546032, baseEnd_6546032] using wordTrace_append hprefix tailTrace_6546032
  have hstable : (prefixWord ++ tailWord_6546032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546032).length < 2 ^ (prefixWord ++ tailWord_6546032).sum := by decide
  have hdescent : baseEnd_6546032 < baseStart_6546032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546055 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_6546055 : Nat := 118140960795 + 6546055 * 2 ^ 59
def prefixEnd_6546055 : Nat := 4983230072969 + 3 ^ 40 * 6546055 * 2
def baseEnd_6546055 : Nat := 3361272605767491263407747

theorem tailTrace_6546055 : CollatzResearch.WordTrace tailWord_6546055 prefixEnd_6546055 3361272605767491263407747 := by
  unfold tailWord_6546055
  simp only [CollatzResearch.WordTrace]
  refine ⟨238754240299768187032399619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159169493533178791354933079 238754240299768187032399619)
  ·
    refine ⟨358131360449652280548599429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238754240299768187032399619 358131360449652280548599429)
    ·
      refine ⟨67149630084309802602862393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358131360449652280548599429 67149630084309802602862393)
      ·
        refine ⟨50362222563232351952146795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67149630084309802602862393 50362222563232351952146795)
        ·
          refine ⟨75543333844848527928220193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50362222563232351952146795 75543333844848527928220193)
          ·
            refine ⟨56657500383636395946165145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75543333844848527928220193 56657500383636395946165145)
            ·
              refine ⟨42493125287727296959623859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56657500383636395946165145 42493125287727296959623859)
              ·
                refine ⟨63739687931590945439435789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42493125287727296959623859 63739687931590945439435789)
                ·
                  refine ⟨23902382974346604539788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63739687931590945439435789 23902382974346604539788421)
                  ·
                    refine ⟨4481696807689988351210329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23902382974346604539788421 4481696807689988351210329)
                    ·
                      refine ⟨3361272605767491263407747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481696807689988351210329 3361272605767491263407747)
                      ·
                        rfl

theorem cell23_6546055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_6546055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546055 prefixEnd_6546055 := by exact prefixLift 6546055
  have htrace : WordTrace (prefixWord ++ tailWord_6546055) baseStart_6546055 baseEnd_6546055 := by
    simpa [prefixWord, tailWord_6546055, baseEnd_6546055] using wordTrace_append hprefix tailTrace_6546055
  have hstable : (prefixWord ++ tailWord_6546055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546055).length < 2 ^ (prefixWord ++ tailWord_6546055).sum := by decide
  have hdescent : baseEnd_6546055 < baseStart_6546055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546072 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6546072 : Nat := 118140960795 + 6546072 * 2 ^ 59
def prefixEnd_6546072 : Nat := 4983230072969 + 3 ^ 40 * 6546072 * 2
def baseEnd_6546072 : Nat := 3361281334938617696895169

theorem tailTrace_6546072 : CollatzResearch.WordTrace tailWord_6546072 prefixEnd_6546072 3361281334938617696895169 := by
  unfold tailWord_6546072
  simp only [CollatzResearch.WordTrace]
  refine ⟨119377430170353299467884235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159169906893804399290512313 119377430170353299467884235)
  ·
    refine ⟨179066145255529949201826353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119377430170353299467884235 179066145255529949201826353)
    ·
      refine ⟨134299608941647461901369765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179066145255529949201826353 134299608941647461901369765)
      ·
        refine ⟨25181176676558899106506831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134299608941647461901369765 25181176676558899106506831)
        ·
          refine ⟨37771765014838348659760247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25181176676558899106506831 37771765014838348659760247)
          ·
            refine ⟨56657647522257522989640371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37771765014838348659760247 56657647522257522989640371)
            ·
              refine ⟨84986471283386284484460557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56657647522257522989640371 84986471283386284484460557)
              ·
                refine ⟨31869926731269856681672709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84986471283386284484460557 31869926731269856681672709)
                ·
                  refine ⟨5975611262113098127813633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31869926731269856681672709 5975611262113098127813633)
                  ·
                    refine ⟨4481708446584823595860225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5975611262113098127813633 4481708446584823595860225)
                    ·
                      refine ⟨3361281334938617696895169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481708446584823595860225 3361281334938617696895169)
                      ·
                        rfl

theorem cell23_6546072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6546072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546072 prefixEnd_6546072 := by exact prefixLift 6546072
  have htrace : WordTrace (prefixWord ++ tailWord_6546072) baseStart_6546072 baseEnd_6546072 := by
    simpa [prefixWord, tailWord_6546072, baseEnd_6546072] using wordTrace_append hprefix tailTrace_6546072
  have hstable : (prefixWord ++ tailWord_6546072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546072).length < 2 ^ (prefixWord ++ tailWord_6546072).sum := by decide
  have hdescent : baseEnd_6546072 < baseStart_6546072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546162 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6546162 : Nat := 118140960795 + 6546162 * 2 ^ 59
def prefixEnd_6546162 : Nat := 4983230072969 + 3 ^ 40 * 6546162 * 2
def baseEnd_6546162 : Nat := 3361327548197522344769755

theorem tailTrace_6546162 : CollatzResearch.WordTrace tailWord_6546162 prefixEnd_6546162 3361327548197522344769755 := by
  unfold tailWord_6546162
  simp only [CollatzResearch.WordTrace]
  refine ⟨59689535727595136076636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159172095273587029537696493 59689535727595136076636185)
  ·
    refine ⟨44767151795696352057477139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59689535727595136076636185 44767151795696352057477139)
    ·
      refine ⟨67150727693544528086215709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44767151795696352057477139 67150727693544528086215709)
      ·
        refine ⟨25181522885079198032330891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67150727693544528086215709 25181522885079198032330891)
        ·
          refine ⟨37772284327618797048496337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25181522885079198032330891 37772284327618797048496337)
          ·
            refine ⟨28329213245714097786372253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37772284327618797048496337 28329213245714097786372253)
            ·
              refine ⟨10623454967142786669889595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28329213245714097786372253 10623454967142786669889595)
              ·
                refine ⟨15935182450714180004834393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10623454967142786669889595 15935182450714180004834393)
                ·
                  refine ⟨11951386838035635003625795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15935182450714180004834393 11951386838035635003625795)
                  ·
                    refine ⟨17927080257053452505438693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11951386838035635003625795 17927080257053452505438693)
                    ·
                      refine ⟨3361327548197522344769755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17927080257053452505438693 3361327548197522344769755)
                      ·
                        rfl

theorem cell23_6546162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6546162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546162 prefixEnd_6546162 := by exact prefixLift 6546162
  have htrace : WordTrace (prefixWord ++ tailWord_6546162) baseStart_6546162 baseEnd_6546162 := by
    simpa [prefixWord, tailWord_6546162, baseEnd_6546162] using wordTrace_append hprefix tailTrace_6546162
  have hstable : (prefixWord ++ tailWord_6546162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546162).length < 2 ^ (prefixWord ++ tailWord_6546162).sum := by decide
  have hdescent : baseEnd_6546162 < baseStart_6546162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546168 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 8]
def baseStart_6546168 : Nat := 118140960795 + 6546168 * 2 ^ 59
def prefixEnd_6546168 : Nat := 4983230072969 + 3 ^ 40 * 6546168 * 2
def baseEnd_6546168 : Nat := 373481181009049924588303

theorem tailTrace_6546168 : CollatzResearch.WordTrace tailWord_6546168 prefixEnd_6546168 373481181009049924588303 := by
  unfold tailWord_6546168
  simp only [CollatzResearch.WordTrace]
  refine ⟨119379180874179403665631579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159172241165572538220842105 119379180874179403665631579)
  ·
    refine ⟨179068771311269105498447369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119379180874179403665631579 179068771311269105498447369)
    ·
      refine ⟨134301578483451829123835527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179068771311269105498447369 134301578483451829123835527)
      ·
        refine ⟨201452367725177743685753291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134301578483451829123835527 201452367725177743685753291)
        ·
          refine ⟨302178551587766615528629937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201452367725177743685753291 302178551587766615528629937)
          ·
            refine ⟨226633913690824961646472453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302178551587766615528629937 226633913690824961646472453)
            ·
              refine ⟨42493858817029680308713585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226633913690824961646472453 42493858817029680308713585)
              ·
                refine ⟨31870394112772260231535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42493858817029680308713585 31870394112772260231535189)
                ·
                  refine ⟨373481181009049924588303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31870394112772260231535189 373481181009049924588303)
                  ·
                    rfl

theorem cell23_6546168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_6546168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546168 prefixEnd_6546168 := by exact prefixLift 6546168
  have htrace : WordTrace (prefixWord ++ tailWord_6546168) baseStart_6546168 baseEnd_6546168 := by
    simpa [prefixWord, tailWord_6546168, baseEnd_6546168] using wordTrace_append hprefix tailTrace_6546168
  have hstable : (prefixWord ++ tailWord_6546168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546168).length < 2 ^ (prefixWord ++ tailWord_6546168).sum := by decide
  have hdescent : baseEnd_6546168 < baseStart_6546168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546185 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 6]
def baseStart_6546185 : Nat := 118140960795 + 6546185 * 2 ^ 59
def prefixEnd_6546185 : Nat := 4983230072969 + 3 ^ 40 * 6546185 * 2
def baseEnd_6546185 : Nat := 373482150916952861642461

theorem tailTrace_6546185 : CollatzResearch.WordTrace tailWord_6546185 prefixEnd_6546185 373482150916952861642461 := by
  unfold tailWord_6546185
  simp only [CollatzResearch.WordTrace]
  refine ⟨238758981789297219234632009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159172654526198146156421339 238758981789297219234632009)
  ·
    refine ⟨179069236341972914425974007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238758981789297219234632009 179069236341972914425974007)
    ·
      refine ⟨268603854512959371638961011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179069236341972914425974007 268603854512959371638961011)
      ·
        refine ⟨402905781769439057458441517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268603854512959371638961011 402905781769439057458441517)
        ·
          refine ⟨151089668163539646546915569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402905781769439057458441517 151089668163539646546915569)
          ·
            refine ⟨113317251122654734910186677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151089668163539646546915569 113317251122654734910186677)
            ·
              refine ⟨10623492292748881397830001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113317251122654734910186677 10623492292748881397830001)
              ·
                refine ⟨7967619219561661048372501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10623492292748881397830001 7967619219561661048372501)
                ·
                  refine ⟨373482150916952861642461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7967619219561661048372501 373482150916952861642461)
                  ·
                    rfl

theorem cell23_6546185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_6546185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546185 prefixEnd_6546185 := by exact prefixLift 6546185
  have htrace : WordTrace (prefixWord ++ tailWord_6546185) baseStart_6546185 baseEnd_6546185 := by
    simpa [prefixWord, tailWord_6546185, baseEnd_6546185] using wordTrace_append hprefix tailTrace_6546185
  have hstable : (prefixWord ++ tailWord_6546185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546185).length < 2 ^ (prefixWord ++ tailWord_6546185).sum := by decide
  have hdescent : baseEnd_6546185 < baseStart_6546185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546202 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_6546202 : Nat := 118140960795 + 6546202 * 2 ^ 59
def prefixEnd_6546202 : Nat := 4983230072969 + 3 ^ 40 * 6546202 * 2
def baseEnd_6546202 : Nat := 373483120824855798696619

theorem tailTrace_6546202 : CollatzResearch.WordTrace tailWord_6546202 prefixEnd_6546202 373483120824855798696619 := by
  unfold tailWord_6546202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59689900457558907784500215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159173067886823754092000573 59689900457558907784500215)
  ·
    refine ⟨89534850686338361676750323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59689900457558907784500215 89534850686338361676750323)
    ·
      refine ⟨134302276029507542515125485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89534850686338361676750323 134302276029507542515125485)
      ·
        refine ⟨50363353511065328443172057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134302276029507542515125485 50363353511065328443172057)
        ·
          refine ⟨37772515133298996332379043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50363353511065328443172057 37772515133298996332379043)
          ·
            refine ⟨56658772699948494498568565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37772515133298996332379043 56658772699948494498568565)
            ·
              refine ⟨5311759940620171359240803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56658772699948494498568565 5311759940620171359240803)
              ·
                refine ⟨7967639910930257038861205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311759940620171359240803 7967639910930257038861205)
                ·
                  refine ⟨373483120824855798696619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7967639910930257038861205 373483120824855798696619)
                  ·
                    rfl

theorem cell23_6546202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_6546202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546202 prefixEnd_6546202 := by exact prefixLift 6546202
  have htrace : WordTrace (prefixWord ++ tailWord_6546202) baseStart_6546202 baseEnd_6546202 := by
    simpa [prefixWord, tailWord_6546202, baseEnd_6546202] using wordTrace_append hprefix tailTrace_6546202
  have hstable : (prefixWord ++ tailWord_6546202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546202).length < 2 ^ (prefixWord ++ tailWord_6546202).sum := by decide
  have hdescent : baseEnd_6546202 < baseStart_6546202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546239 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 2, 3, 2]
def baseStart_6546239 : Nat := 118140960795 + 6546239 * 2 ^ 59
def prefixEnd_6546239 : Nat := 4983230072969 + 3 ^ 40 * 6546239 * 2
def baseEnd_6546239 : Nat := 3361367086207918543506901

theorem tailTrace_6546239 : CollatzResearch.WordTrace tailWord_6546239 prefixEnd_6546239 3361367086207918543506901 := by
  unfold tailWord_6546239
  simp only [CollatzResearch.WordTrace]
  refine ⟨238760951331101586457097771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159173967554067724304731847 238760951331101586457097771)
  ·
    refine ⟨358141426996652379685646657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238760951331101586457097771 358141426996652379685646657)
    ·
      refine ⟨268606070247489284764234993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358141426996652379685646657 268606070247489284764234993)
      ·
        refine ⟨201454552685616963573176245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268606070247489284764234993 201454552685616963573176245)
        ·
          refine ⟨18886364314276590334985273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201454552685616963573176245 18886364314276590334985273)
          ·
            refine ⟨14164773235707442751238955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18886364314276590334985273 14164773235707442751238955)
            ·
              refine ⟨21247159853561164126858433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14164773235707442751238955 21247159853561164126858433)
              ·
                refine ⟨15935369890170873095143825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21247159853561164126858433 15935369890170873095143825)
                ·
                  refine ⟨11951527417628154821357869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15935369890170873095143825 11951527417628154821357869)
                  ·
                    refine ⟨4481822781610558058009201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11951527417628154821357869 4481822781610558058009201)
                    ·
                      refine ⟨3361367086207918543506901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481822781610558058009201 3361367086207918543506901)
                      ·
                        rfl

theorem cell23_6546239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_6546239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546239 prefixEnd_6546239 := by exact prefixLift 6546239
  have htrace : WordTrace (prefixWord ++ tailWord_6546239) baseStart_6546239 baseEnd_6546239 := by
    simpa [prefixWord, tailWord_6546239, baseEnd_6546239] using wordTrace_append hprefix tailTrace_6546239
  have hstable : (prefixWord ++ tailWord_6546239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546239).length < 2 ^ (prefixWord ++ tailWord_6546239).sum := by decide
  have hdescent : baseEnd_6546239 < baseStart_6546239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546253 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6546253 : Nat := 118140960795 + 6546253 * 2 ^ 59
def prefixEnd_6546253 : Nat := 4983230072969 + 3 ^ 40 * 6546253 * 2
def baseEnd_6546253 : Nat := 373486030548564609859093

theorem tailTrace_6546253 : CollatzResearch.WordTrace tailWord_6546253 prefixEnd_6546253 373486030548564609859093 := by
  unfold tailWord_6546253
  simp only [CollatzResearch.WordTrace]
  refine ⟨238761461953050866848107413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159174307968700577898738275 238761461953050866848107413)
  ·
    refine ⟨11191943529049259383505035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238761461953050866848107413 11191943529049259383505035)
    ·
      refine ⟨16787915293573889075257553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191943529049259383505035 16787915293573889075257553)
      ·
        refine ⟨12590936470180416806443165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16787915293573889075257553 12590936470180416806443165)
        ·
          refine ⟨4721601176317656302416187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12590936470180416806443165 4721601176317656302416187)
          ·
            refine ⟨7082401764476484453624281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721601176317656302416187 7082401764476484453624281)
            ·
              refine ⟨5311801323357363340218211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7082401764476484453624281 5311801323357363340218211)
              ·
                refine ⟨7967701985036045010327317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311801323357363340218211 7967701985036045010327317)
                ·
                  refine ⟨373486030548564609859093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7967701985036045010327317 373486030548564609859093)
                  ·
                    rfl

theorem cell23_6546253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6546253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546253 prefixEnd_6546253 := by exact prefixLift 6546253
  have htrace : WordTrace (prefixWord ++ tailWord_6546253) baseStart_6546253 baseEnd_6546253 := by
    simpa [prefixWord, tailWord_6546253, baseEnd_6546253] using wordTrace_append hprefix tailTrace_6546253
  have hstable : (prefixWord ++ tailWord_6546253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546253).length < 2 ^ (prefixWord ++ tailWord_6546253).sum := by decide
  have hdescent : baseEnd_6546253 < baseStart_6546253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546265 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_6546265 : Nat := 118140960795 + 6546265 * 2 ^ 59
def prefixEnd_6546265 : Nat := 4983230072969 + 3 ^ 40 * 6546265 * 2
def baseEnd_6546265 : Nat := 3361380436704935441781781

theorem tailTrace_6546265 : CollatzResearch.WordTrace tailWord_6546265 prefixEnd_6546265 3361380436704935441781781 := by
  unfold tailWord_6546265
  simp only [CollatzResearch.WordTrace]
  refine ⟨238761899629007392897544249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159174599752671595265029499 238761899629007392897544249)
  ·
    refine ⟨179071424721755544673158187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238761899629007392897544249 179071424721755544673158187)
    ·
      refine ⟨268607137082633317009737281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179071424721755544673158187 268607137082633317009737281)
      ·
        refine ⟨201455352811974987757302961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268607137082633317009737281 201455352811974987757302961)
        ·
          refine ⟨151091514608981240817977221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201455352811974987757302961 151091514608981240817977221)
          ·
            refine ⟨28329658989183982653370729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151091514608981240817977221 28329658989183982653370729)
            ·
              refine ⟨21247244241887986990028047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28329658989183982653370729 21247244241887986990028047)
              ·
                refine ⟨31870866362831980485042071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21247244241887986990028047 31870866362831980485042071)
                ·
                  refine ⟨47806299544247970727563107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31870866362831980485042071 47806299544247970727563107)
                  ·
                    refine ⟨71709449316371956091344661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47806299544247970727563107 71709449316371956091344661)
                    ·
                      refine ⟨3361380436704935441781781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71709449316371956091344661 3361380436704935441781781)
                      ·
                        rfl

theorem cell23_6546265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_6546265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546265 prefixEnd_6546265 := by exact prefixLift 6546265
  have htrace : WordTrace (prefixWord ++ tailWord_6546265) baseStart_6546265 baseEnd_6546265 := by
    simpa [prefixWord, tailWord_6546265, baseEnd_6546265] using wordTrace_append hprefix tailTrace_6546265
  have hstable : (prefixWord ++ tailWord_6546265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546265).length < 2 ^ (prefixWord ++ tailWord_6546265).sum := by decide
  have hdescent : baseEnd_6546265 < baseStart_6546265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546272 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_6546272 : Nat := 118140960795 + 6546272 * 2 ^ 59
def prefixEnd_6546272 : Nat := 4983230072969 + 3 ^ 40 * 6546272 * 2
def baseEnd_6546272 : Nat := 3361384031069516914394249

theorem tailTrace_6546272 : CollatzResearch.WordTrace tailWord_6546272 prefixEnd_6546272 3361384031069516914394249 := by
  unfold tailWord_6546272
  simp only [CollatzResearch.WordTrace]
  refine ⟨119381077469991016546524535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159174769959988022062032713 119381077469991016546524535)
  ·
    refine ⟨179071616204986524819786803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119381077469991016546524535 179071616204986524819786803)
    ·
      refine ⟨268607424307479787229680205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179071616204986524819786803 268607424307479787229680205)
      ·
        refine ⟨100727784115304920211130077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268607424307479787229680205 100727784115304920211130077)
        ·
          refine ⟨37772919043239345079173779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100727784115304920211130077 37772919043239345079173779)
          ·
            refine ⟨56659378564859017618760669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37772919043239345079173779 56659378564859017618760669)
            ·
              refine ⟨21247266961822131607035251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56659378564859017618760669 21247266961822131607035251)
              ·
                refine ⟨31870900442733197410552877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21247266961822131607035251 31870900442733197410552877)
                ·
                  refine ⟨11951587666024949028957329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31870900442733197410552877 11951587666024949028957329)
                  ·
                    refine ⟨8963690749518711771717997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11951587666024949028957329 8963690749518711771717997)
                    ·
                      refine ⟨3361384031069516914394249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963690749518711771717997 3361384031069516914394249)
                      ·
                        rfl

theorem cell23_6546272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_6546272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546272 prefixEnd_6546272 := by exact prefixLift 6546272
  have htrace : WordTrace (prefixWord ++ tailWord_6546272) baseStart_6546272 baseEnd_6546272 := by
    simpa [prefixWord, tailWord_6546272, baseEnd_6546272] using wordTrace_append hprefix tailTrace_6546272
  have hstable : (prefixWord ++ tailWord_6546272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546272).length < 2 ^ (prefixWord ++ tailWord_6546272).sum := by decide
  have hdescent : baseEnd_6546272 < baseStart_6546272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546275 : List Nat := [1, 1, 1, 5, 3, 1, 2, 9]
def baseStart_6546275 : Nat := 118140960795 + 6546275 * 2 ^ 59
def prefixEnd_6546275 : Nat := 4983230072969 + 3 ^ 40 * 6546275 * 2
def baseEnd_6546275 : Nat := 124495761907832607505805

theorem tailTrace_6546275 : CollatzResearch.WordTrace tailWord_6546275 prefixEnd_6546275 124495761907832607505805 := by
  unfold tailWord_6546275
  simp only [CollatzResearch.WordTrace]
  refine ⟨238762264358971164605408279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159174842905980776403605519 238762264358971164605408279)
  ·
    refine ⟨358143396538456746908112419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238762264358971164605408279 358143396538456746908112419)
    ·
      refine ⟨537215094807685120362168629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358143396538456746908112419 537215094807685120362168629)
      ·
        refine ⟨50363915138220480033953309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 537215094807685120362168629 50363915138220480033953309)
        ·
          refine ⟨18886468176832680012732491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50363915138220480033953309 18886468176832680012732491)
          ·
            refine ⟨28329702265249020019098737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18886468176832680012732491 28329702265249020019098737)
            ·
              refine ⟨21247276698936765014324053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28329702265249020019098737 21247276698936765014324053)
              ·
                refine ⟨124495761907832607505805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21247276698936765014324053 124495761907832607505805)
                ·
                  rfl

theorem cell23_6546275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 9].length) (baseStart_6546275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546275 prefixEnd_6546275 := by exact prefixLift 6546275
  have htrace : WordTrace (prefixWord ++ tailWord_6546275) baseStart_6546275 baseEnd_6546275 := by
    simpa [prefixWord, tailWord_6546275, baseEnd_6546275] using wordTrace_append hprefix tailTrace_6546275
  have hstable : (prefixWord ++ tailWord_6546275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546275).length < 2 ^ (prefixWord ++ tailWord_6546275).sum := by decide
  have hdescent : baseEnd_6546275 < baseStart_6546275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546303 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 1, 2, 2]
def baseStart_6546303 : Nat := 118140960795 + 6546303 * 2 ^ 59
def prefixEnd_6546303 : Nat := 4983230072969 + 3 ^ 40 * 6546303 * 2
def baseEnd_6546303 : Nat := 3361399948969806293106607

theorem tailTrace_6546303 : CollatzResearch.WordTrace tailWord_6546303 prefixEnd_6546303 3361399948969806293106607 := by
  unfold tailWord_6546303
  simp only [CollatzResearch.WordTrace]
  refine ⟨238763285602869725387427563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159175523735246483591618375 238763285602869725387427563)
  ·
    refine ⟨358144928404304588081141345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238763285602869725387427563 358144928404304588081141345)
    ·
      refine ⟨268608696303228441060856009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358144928404304588081141345 268608696303228441060856009)
      ·
        refine ⟨201456522227421330795642007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268608696303228441060856009 201456522227421330795642007)
        ·
          refine ⟨302184783341131996193463011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201456522227421330795642007 302184783341131996193463011)
          ·
            refine ⟨453277175011697994290194517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302184783341131996193463011 453277175011697994290194517)
            ·
              refine ⟨5311841894668335870588217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 453277175011697994290194517 5311841894668335870588217)
              ·
                refine ⟨3983881421001251902941163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311841894668335870588217 3983881421001251902941163)
                ·
                  refine ⟨5975822131501877854411745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983881421001251902941163 5975822131501877854411745)
                  ·
                    refine ⟨4481866598626408390808809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5975822131501877854411745 4481866598626408390808809)
                    ·
                      refine ⟨3361399948969806293106607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481866598626408390808809 3361399948969806293106607)
                      ·
                        rfl

theorem cell23_6546303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_6546303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546303 prefixEnd_6546303 := by exact prefixLift 6546303
  have htrace : WordTrace (prefixWord ++ tailWord_6546303) baseStart_6546303 baseEnd_6546303 := by
    simpa [prefixWord, tailWord_6546303, baseEnd_6546303] using wordTrace_append hprefix tailTrace_6546303
  have hstable : (prefixWord ++ tailWord_6546303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546303).length < 2 ^ (prefixWord ++ tailWord_6546303).sum := by decide
  have hdescent : baseEnd_6546303 < baseStart_6546303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546329 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 1, 3, 2]
def baseStart_6546329 : Nat := 118140960795 + 6546329 * 2 ^ 59
def prefixEnd_6546329 : Nat := 4983230072969 + 3 ^ 40 * 6546329 * 2
def baseEnd_6546329 : Nat := 3361413299466823191381487

theorem tailTrace_6546329 : CollatzResearch.WordTrace tailWord_6546329 prefixEnd_6546329 3361413299466823191381487 := by
  unfold tailWord_6546329
  simp only [CollatzResearch.WordTrace]
  refine ⟨238764233900775531827874041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159176155933850354551916027 238764233900775531827874041)
  ·
    refine ⟨179073175425581648870905531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238764233900775531827874041 179073175425581648870905531)
    ·
      refine ⟨268609763138372473306358297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179073175425581648870905531 268609763138372473306358297)
      ·
        refine ⟨201457322353779354979768723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268609763138372473306358297 201457322353779354979768723)
        ·
          refine ⟨302185983530669032469653085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201457322353779354979768723 302185983530669032469653085)
          ·
            refine ⟨113319743824000887176119907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302185983530669032469653085 113319743824000887176119907)
            ·
              refine ⟨169979615736001330764179861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113319743824000887176119907 169979615736001330764179861)
              ·
                refine ⟨7967794487625062379570931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169979615736001330764179861 7967794487625062379570931)
                ·
                  refine ⟨11951691731437593569356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7967794487625062379570931 11951691731437593569356397)
                  ·
                    refine ⟨4481884399289097588508649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11951691731437593569356397 4481884399289097588508649)
                    ·
                      refine ⟨3361413299466823191381487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4481884399289097588508649 3361413299466823191381487)
                      ·
                        rfl

theorem cell23_6546329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_6546329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546329 prefixEnd_6546329 := by exact prefixLift 6546329
  have htrace : WordTrace (prefixWord ++ tailWord_6546329) baseStart_6546329 baseEnd_6546329 := by
    simpa [prefixWord, tailWord_6546329, baseEnd_6546329] using wordTrace_append hprefix tailTrace_6546329
  have hstable : (prefixWord ++ tailWord_6546329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546329).length < 2 ^ (prefixWord ++ tailWord_6546329).sum := by decide
  have hdescent : baseEnd_6546329 < baseStart_6546329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546345 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_6546345 : Nat := 118140960795 + 6546345 * 2 ^ 59
def prefixEnd_6546345 : Nat := 4983230072969 + 3 ^ 40 * 6546345 * 2
def baseEnd_6546345 : Nat := 3361421515157295128781413

theorem tailTrace_6546345 : CollatzResearch.WordTrace tailWord_6546345 prefixEnd_6546345 3361421515157295128781413 := by
  unfold tailWord_6546345
  simp only [CollatzResearch.WordTrace]
  refine ⟨238764817468717566560456489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159176544979145044373637659 238764817468717566560456489)
  ·
    refine ⟨179073613101538174920342367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238764817468717566560456489 179073613101538174920342367)
    ·
      refine ⟨268610419652307262380513551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179073613101538174920342367 268610419652307262380513551)
      ·
        refine ⟨402915629478460893570770327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268610419652307262380513551 402915629478460893570770327)
        ·
          refine ⟨604373444217691340356155491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402915629478460893570770327 604373444217691340356155491)
          ·
            refine ⟨906560166326537010534233237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604373444217691340356155491 906560166326537010534233237)
            ·
              refine ⟨42495007796556422368792183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 906560166326537010534233237 42495007796556422368792183)
              ·
                refine ⟨63742511694834633553188275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42495007796556422368792183 63742511694834633553188275)
                ·
                  refine ⟨95613767542251950329782413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63742511694834633553188275 95613767542251950329782413)
                  ·
                    refine ⟨35855162828344481373668405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95613767542251950329782413 35855162828344481373668405)
                    ·
                      refine ⟨3361421515157295128781413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35855162828344481373668405 3361421515157295128781413)
                      ·
                        rfl

theorem cell23_6546345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_6546345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546345 prefixEnd_6546345 := by exact prefixLift 6546345
  have htrace : WordTrace (prefixWord ++ tailWord_6546345) baseStart_6546345 baseEnd_6546345 := by
    simpa [prefixWord, tailWord_6546345, baseEnd_6546345] using wordTrace_append hprefix tailTrace_6546345
  have hstable : (prefixWord ++ tailWord_6546345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546345).length < 2 ^ (prefixWord ++ tailWord_6546345).sum := by decide
  have hdescent : baseEnd_6546345 < baseStart_6546345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546353 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6546353 : Nat := 118140960795 + 6546353 * 2 ^ 59
def prefixEnd_6546353 : Nat := 4983230072969 + 3 ^ 40 * 6546353 * 2
def baseEnd_6546353 : Nat := 3361425623002531097481377

theorem tailTrace_6546353 : CollatzResearch.WordTrace tailWord_6546353 prefixEnd_6546353 3361425623002531097481377 := by
  unfold tailWord_6546353
  simp only [CollatzResearch.WordTrace]
  refine ⟨238765109252688583926747713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159176739501792389284498475 238765109252688583926747713)
  ·
    refine ⟨179073831939516437945060785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238765109252688583926747713 179073831939516437945060785)
    ·
      refine ⟨134305373954637328458795589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179073831939516437945060785 134305373954637328458795589)
      ·
        refine ⟨25182257616494499086024173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134305373954637328458795589 25182257616494499086024173)
        ·
          refine ⟨9443346606185437157259065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25182257616494499086024173 9443346606185437157259065)
          ·
            refine ⟨7082509954639077867944299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9443346606185437157259065 7082509954639077867944299)
            ·
              refine ⟨10623764931958616801916449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082509954639077867944299 10623764931958616801916449)
              ·
                refine ⟨7967823698968962601437337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10623764931958616801916449 7967823698968962601437337)
                ·
                  refine ⟨5975867774226721951078003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7967823698968962601437337 5975867774226721951078003)
                  ·
                    refine ⟨8963801661340082926617005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5975867774226721951078003 8963801661340082926617005)
                    ·
                      refine ⟨3361425623002531097481377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963801661340082926617005 3361425623002531097481377)
                      ·
                        rfl

theorem cell23_6546353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6546353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546353 prefixEnd_6546353 := by exact prefixLift 6546353
  have htrace : WordTrace (prefixWord ++ tailWord_6546353) baseStart_6546353 baseEnd_6546353 := by
    simpa [prefixWord, tailWord_6546353, baseEnd_6546353] using wordTrace_append hprefix tailTrace_6546353
  have hstable : (prefixWord ++ tailWord_6546353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546353).length < 2 ^ (prefixWord ++ tailWord_6546353).sum := by decide
  have hdescent : baseEnd_6546353 < baseStart_6546353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546382 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_6546382 : Nat := 118140960795 + 6546382 * 2 ^ 59
def prefixEnd_6546382 : Nat := 4983230072969 + 3 ^ 40 * 6546382 * 2
def baseEnd_6546382 : Nat := 373493390437945720446527

theorem tailTrace_6546382 : CollatzResearch.WordTrace tailWord_6546382 prefixEnd_6546382 373493390437945720446527 := by
  unfold tailWord_6546382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29845770871197940234944175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159177444646389014586368933 29845770871197940234944175)
  ·
    refine ⟨44768656306796910352416263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29845770871197940234944175 44768656306796910352416263)
    ·
      refine ⟨67152984460195365528624395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44768656306796910352416263 67152984460195365528624395)
      ·
        refine ⟨100729476690293048292936593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67152984460195365528624395 100729476690293048292936593)
        ·
          refine ⟨75547107517719786219702445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100729476690293048292936593 75547107517719786219702445)
          ·
            refine ⟨28330165319144919832388417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75547107517719786219702445 28330165319144919832388417)
            ·
              refine ⟨21247623989358689874291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28330165319144919832388417 21247623989358689874291313)
              ·
                refine ⟨15935717992019017405718485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21247623989358689874291313 15935717992019017405718485)
                ·
                  refine ⟨373493390437945720446527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15935717992019017405718485 373493390437945720446527)
                  ·
                    rfl

theorem cell23_6546382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_6546382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546382 prefixEnd_6546382 := by exact prefixLift 6546382
  have htrace : WordTrace (prefixWord ++ tailWord_6546382) baseStart_6546382 baseEnd_6546382 := by
    simpa [prefixWord, tailWord_6546382, baseEnd_6546382] using wordTrace_append hprefix tailTrace_6546382
  have hstable : (prefixWord ++ tailWord_6546382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546382).length < 2 ^ (prefixWord ++ tailWord_6546382).sum := by decide
  have hdescent : baseEnd_6546382 < baseStart_6546382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546469 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_6546469 : Nat := 118140960795 + 6546469 * 2 ^ 59
def prefixEnd_6546469 : Nat := 4983230072969 + 3 ^ 40 * 6546469 * 2
def baseEnd_6546469 : Nat := 3361485186758452643630843

theorem tailTrace_6546469 : CollatzResearch.WordTrace tailWord_6546469 prefixEnd_6546469 3361485186758452643630843 := by
  unfold tailWord_6546469
  simp only [CollatzResearch.WordTrace]
  refine ⟨238769340120268335737970461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159179560080178890491980307 238769340120268335737970461)
  ·
    refine ⟨89538502545100625901738923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238769340120268335737970461 89538502545100625901738923)
    ·
      refine ⟨134307753817650938852608385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89538502545100625901738923 134307753817650938852608385)
      ·
        refine ⟨100730815363238204139456289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134307753817650938852608385 100730815363238204139456289)
        ·
          refine ⟨75548111522428653104592217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100730815363238204139456289 75548111522428653104592217)
          ·
            refine ⟨56661083641821489828444163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75548111522428653104592217 56661083641821489828444163)
            ·
              refine ⟨84991625462732234742666245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56661083641821489828444163 84991625462732234742666245)
              ·
                refine ⟨15935929774262294014249921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84991625462732234742666245 15935929774262294014249921)
                ·
                  refine ⟨11951947330696720510687441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15935929774262294014249921 11951947330696720510687441)
                  ·
                    refine ⟨8963960498022540383015581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11951947330696720510687441 8963960498022540383015581)
                    ·
                      refine ⟨3361485186758452643630843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8963960498022540383015581 3361485186758452643630843)
                      ·
                        rfl

theorem cell23_6546469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_6546469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546469 prefixEnd_6546469 := by exact prefixLift 6546469
  have htrace : WordTrace (prefixWord ++ tailWord_6546469) baseStart_6546469 baseEnd_6546469 := by
    simpa [prefixWord, tailWord_6546469, baseEnd_6546469] using wordTrace_append hprefix tailTrace_6546469
  have hstable : (prefixWord ++ tailWord_6546469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546469).length < 2 ^ (prefixWord ++ tailWord_6546469).sum := by decide
  have hdescent : baseEnd_6546469 < baseStart_6546469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546476 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_6546476 : Nat := 118140960795 + 6546476 * 2 ^ 59
def prefixEnd_6546476 : Nat := 4983230072969 + 3 ^ 40 * 6546476 * 2
def baseEnd_6546476 : Nat := 1120496260374344705414437

theorem tailTrace_6546476 : CollatzResearch.WordTrace tailWord_6546476 prefixEnd_6546476 1120496260374344705414437 := by
  unfold tailWord_6546476
  simp only [CollatzResearch.WordTrace]
  refine ⟨119384797715621487966737641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159179730287495317288983521 119384797715621487966737641)
  ·
    refine ⟨89538598286716115975053231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119384797715621487966737641 89538598286716115975053231)
    ·
      refine ⟨134307897430074173962579847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89538598286716115975053231 134307897430074173962579847)
      ·
        refine ⟨201461846145111260943869771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134307897430074173962579847 201461846145111260943869771)
        ·
          refine ⟨302192769217666891415804657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201461846145111260943869771 302192769217666891415804657)
          ·
            refine ⟨226644576913250168561853493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302192769217666891415804657 226644576913250168561853493)
            ·
              refine ⟨21247929085617203302673765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226644576913250168561853493 21247929085617203302673765)
              ·
                refine ⟨3983986703553225619251331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21247929085617203302673765 3983986703553225619251331)
                ·
                  refine ⟨5975980055329838428876997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983986703553225619251331 5975980055329838428876997)
                  ·
                    refine ⟨1120496260374344705414437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975980055329838428876997 1120496260374344705414437)
                    ·
                      rfl

theorem cell23_6546476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_6546476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546476 prefixEnd_6546476 := by exact prefixLift 6546476
  have htrace : WordTrace (prefixWord ++ tailWord_6546476) baseStart_6546476 baseEnd_6546476 := by
    simpa [prefixWord, tailWord_6546476, baseEnd_6546476] using wordTrace_append hprefix tailTrace_6546476
  have hstable : (prefixWord ++ tailWord_6546476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546476).length < 2 ^ (prefixWord ++ tailWord_6546476).sum := by decide
  have hdescent : baseEnd_6546476 < baseStart_6546476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546489 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 6]
def baseStart_6546489 : Nat := 118140960795 + 6546489 * 2 ^ 59
def prefixEnd_6546489 : Nat := 4983230072969 + 3 ^ 40 * 6546489 * 2
def baseEnd_6546489 : Nat := 373499495152393618375639

theorem tailTrace_6546489 : CollatzResearch.WordTrace tailWord_6546489 prefixEnd_6546489 373499495152393618375639 := by
  unfold tailWord_6546489
  simp only [CollatzResearch.WordTrace]
  refine ⟨238770069580195879153698521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159180046386797252769132347 238770069580195879153698521)
  ·
    refine ⟨179077552185146909365273891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238770069580195879153698521 179077552185146909365273891)
    ·
      refine ⟨268616328277720364047910837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179077552185146909365273891 268616328277720364047910837)
      ·
        refine ⟨25182780776036284129491641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268616328277720364047910837 25182780776036284129491641)
        ·
          refine ⟨18887085582027213097118731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25182780776036284129491641 18887085582027213097118731)
          ·
            refine ⟨28330628373040819645678097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887085582027213097118731 28330628373040819645678097)
            ·
              refine ⟨21247971279780614734258573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28330628373040819645678097 21247971279780614734258573)
              ·
                refine ⟨7967989229917730525346965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21247971279780614734258573 7967989229917730525346965)
                ·
                  refine ⟨373499495152393618375639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7967989229917730525346965 373499495152393618375639)
                  ·
                    rfl

theorem cell23_6546489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_6546489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546489 prefixEnd_6546489 := by exact prefixLift 6546489
  have htrace : WordTrace (prefixWord ++ tailWord_6546489) baseStart_6546489 baseEnd_6546489 := by
    simpa [prefixWord, tailWord_6546489, baseEnd_6546489] using wordTrace_append hprefix tailTrace_6546489
  have hstable : (prefixWord ++ tailWord_6546489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546489).length < 2 ^ (prefixWord ++ tailWord_6546489).sum := by decide
  have hdescent : baseEnd_6546489 < baseStart_6546489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546533 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_6546533 : Nat := 118140960795 + 6546533 * 2 ^ 59
def prefixEnd_6546533 : Nat := 4983230072969 + 3 ^ 40 * 6546533 * 2
def baseEnd_6546533 : Nat := 3361518049520340393230549

theorem tailTrace_6546533 : CollatzResearch.WordTrace tailWord_6546533 prefixEnd_6546533 3361518049520340393230549 := by
  unfold tailWord_6546533
  simp only [CollatzResearch.WordTrace]
  refine ⟨238771674392036474668300253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159181116261357649778866835 238771674392036474668300253)
  ·
    refine ⟨89539377897013678000612595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238771674392036474668300253 89539377897013678000612595)
    ·
      refine ⟨134309066845520517000918893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89539377897013678000612595 134309066845520517000918893)
      ·
        refine ⟨50365900067070193875344585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134309066845520517000918893 50365900067070193875344585)
        ·
          refine ⟨37774425050302645406508439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50365900067070193875344585 37774425050302645406508439)
          ·
            refine ⟨56661637575453968109762659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37774425050302645406508439 56661637575453968109762659)
            ·
              refine ⟨84992456363180952164643989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56661637575453968109762659 84992456363180952164643989)
              ·
                refine ⟨3984021392024107132717687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84992456363180952164643989 3984021392024107132717687)
                ·
                  refine ⟨5976032088036160699076531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984021392024107132717687 5976032088036160699076531)
                  ·
                    refine ⟨8964048132054241048614797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5976032088036160699076531 8964048132054241048614797)
                    ·
                      refine ⟨3361518049520340393230549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8964048132054241048614797 3361518049520340393230549)
                      ·
                        rfl

theorem cell23_6546533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_6546533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546533 prefixEnd_6546533 := by exact prefixLift 6546533
  have htrace : WordTrace (prefixWord ++ tailWord_6546533) baseStart_6546533 baseEnd_6546533 := by
    simpa [prefixWord, tailWord_6546533, baseEnd_6546533] using wordTrace_append hprefix tailTrace_6546533
  have hstable : (prefixWord ++ tailWord_6546533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546533).length < 2 ^ (prefixWord ++ tailWord_6546533).sum := by decide
  have hdescent : baseEnd_6546533 < baseStart_6546533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546556 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_6546556 : Nat := 118140960795 + 6546556 * 2 ^ 59
def prefixEnd_6546556 : Nat := 4983230072969 + 3 ^ 40 * 6546556 * 2
def baseEnd_6546556 : Nat := 3361529859575393803242943

theorem tailTrace_6546556 : CollatzResearch.WordTrace tailWord_6546556 prefixEnd_6546556 3361529859575393803242943 := by
  unfold tailWord_6546556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119386256635476574798193761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159181675513968766397591681 119386256635476574798193761)
  ·
    refine ⟨89539692476607431098645321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119386256635476574798193761 89539692476607431098645321)
    ·
      refine ⟨67154769357455573323983991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89539692476607431098645321 67154769357455573323983991)
      ·
        refine ⟨100732154036183359985975987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67154769357455573323983991 100732154036183359985975987)
        ·
          refine ⟨151098231054275039978963981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100732154036183359985975987 151098231054275039978963981)
          ·
            refine ⟨56661836645353139992111493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151098231054275039978963981 56661836645353139992111493)
            ·
              refine ⟨10624094371003713748520905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56661836645353139992111493 10624094371003713748520905)
              ·
                refine ⟨7968070778252785311390679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624094371003713748520905 7968070778252785311390679)
                ·
                  refine ⟨11952106167379177967086019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968070778252785311390679 11952106167379177967086019)
                  ·
                    refine ⟨17928159251068766950629029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11952106167379177967086019 17928159251068766950629029)
                    ·
                      refine ⟨3361529859575393803242943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17928159251068766950629029 3361529859575393803242943)
                      ·
                        rfl

theorem cell23_6546556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_6546556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546556 prefixEnd_6546556 := by exact prefixLift 6546556
  have htrace : WordTrace (prefixWord ++ tailWord_6546556) baseStart_6546556 baseEnd_6546556 := by
    simpa [prefixWord, tailWord_6546556, baseEnd_6546556] using wordTrace_append hprefix tailTrace_6546556
  have hstable : (prefixWord ++ tailWord_6546556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546556).length < 2 ^ (prefixWord ++ tailWord_6546556).sum := by decide
  have hdescent : baseEnd_6546556 < baseStart_6546556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546630 : List Nat := [6, 1, 2, 2, 2, 10]
def baseStart_6546630 : Nat := 118140960795 + 6546630 * 2 ^ 59
def prefixEnd_6546630 : Nat := 4983230072969 + 3 ^ 40 * 6546630 * 2
def baseEnd_6546630 : Nat := 13833612580838792237521

theorem tailTrace_6546630 : CollatzResearch.WordTrace tailWord_6546630 prefixEnd_6546630 13833612580838792237521 := by
  unfold tailWord_6546630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461725383521408132330667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159183474848456706823054229 7461725383521408132330667)
  ·
    refine ⟨11192588075282112198496001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461725383521408132330667 11192588075282112198496001)
    ·
      refine ⟨8394441056461584148872001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11192588075282112198496001 8394441056461584148872001)
      ·
        refine ⟨6295830792346188111654001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8394441056461584148872001 6295830792346188111654001)
        ·
          refine ⟨4721873094259641083740501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6295830792346188111654001 4721873094259641083740501)
          ·
            refine ⟨13833612580838792237521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4721873094259641083740501 13833612580838792237521)
            ·
              rfl

theorem cell23_6546630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 10].length) (baseStart_6546630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546630 prefixEnd_6546630 := by exact prefixLift 6546630
  have htrace : WordTrace (prefixWord ++ tailWord_6546630) baseStart_6546630 baseEnd_6546630 := by
    simpa [prefixWord, tailWord_6546630, baseEnd_6546630] using wordTrace_append hprefix tailTrace_6546630
  have hstable : (prefixWord ++ tailWord_6546630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546630).length < 2 ^ (prefixWord ++ tailWord_6546630).sum := by decide
  have hdescent : baseEnd_6546630 < baseStart_6546630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546684 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_6546684 : Nat := 118140960795 + 6546684 * 2 ^ 59
def prefixEnd_6546684 : Nat := 4983230072969 + 3 ^ 40 * 6546684 * 2
def baseEnd_6546684 : Nat := 3361595585099169302442355

theorem tailTrace_6546684 : CollatzResearch.WordTrace tailWord_6546684 prefixEnd_6546684 3361595585099169302442355 := by
  unfold tailWord_6546684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119388590907244713728523553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159184787876326284971364737 119388590907244713728523553)
  ·
    refine ⟨89541443180433535296392665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119388590907244713728523553 89541443180433535296392665)
    ·
      refine ⟨67156082385325151472294499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89541443180433535296392665 67156082385325151472294499)
      ·
        refine ⟨100734123577987727208441749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67156082385325151472294499 100734123577987727208441749)
        ·
          refine ⟨4721912042718174712895707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100734123577987727208441749 4721912042718174712895707)
          ·
            refine ⟨7082868064077262069343561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721912042718174712895707 7082868064077262069343561)
            ·
              refine ⟨5312151048057946552007671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7082868064077262069343561 5312151048057946552007671)
              ·
                refine ⟨7968226572086919828011507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312151048057946552007671 7968226572086919828011507)
                ·
                  refine ⟨11952339858130379742017261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968226572086919828011507 11952339858130379742017261)
                  ·
                    refine ⟨4482127446798892403256473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11952339858130379742017261 4482127446798892403256473)
                    ·
                      refine ⟨3361595585099169302442355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482127446798892403256473 3361595585099169302442355)
                      ·
                        rfl

theorem cell23_6546684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_6546684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546684 prefixEnd_6546684 := by exact prefixLift 6546684
  have htrace : WordTrace (prefixWord ++ tailWord_6546684) baseStart_6546684 baseEnd_6546684 := by
    simpa [prefixWord, tailWord_6546684, baseEnd_6546684] using wordTrace_append hprefix tailTrace_6546684
  have hstable : (prefixWord ++ tailWord_6546684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546684).length < 2 ^ (prefixWord ++ tailWord_6546684).sum := by decide
  have hdescent : baseEnd_6546684 < baseStart_6546684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546709 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6546709 : Nat := 118140960795 + 6546709 * 2 ^ 59
def prefixEnd_6546709 : Nat := 4983230072969 + 3 ^ 40 * 6546709 * 2
def baseEnd_6546709 : Nat := 3361608422115531704629739

theorem tailTrace_6546709 : CollatzResearch.WordTrace tailWord_6546709 prefixEnd_6546709 3361608422115531704629739 := by
  unfold tailWord_6546709
  simp only [CollatzResearch.WordTrace]
  refine ⟨238778093639398856726707181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159185395759599237817804787 238778093639398856726707181)
  ·
    refine ⟨89541785114774571272515193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238778093639398856726707181 89541785114774571272515193)
    ·
      refine ⟨67156338836080928454386395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89541785114774571272515193 67156338836080928454386395)
      ·
        refine ⟨100734508254121392681579593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67156338836080928454386395 100734508254121392681579593)
        ·
          refine ⟨75550881190591044511184695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100734508254121392681579593 75550881190591044511184695)
          ·
            refine ⟨113326321785886566766777043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75550881190591044511184695 113326321785886566766777043)
            ·
              refine ⟨169989482678829850150165565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113326321785886566766777043 169989482678829850150165565)
              ·
                refine ⟨63746056004561193806312087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169989482678829850150165565 63746056004561193806312087)
                ·
                  refine ⟨95619084006841790709468131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63746056004561193806312087 95619084006841790709468131)
                  ·
                    refine ⟨143428626010262686064202197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95619084006841790709468131 143428626010262686064202197)
                    ·
                      refine ⟨3361608422115531704629739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143428626010262686064202197 3361608422115531704629739)
                      ·
                        rfl

theorem cell23_6546709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6546709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546709 prefixEnd_6546709 := by exact prefixLift 6546709
  have htrace : WordTrace (prefixWord ++ tailWord_6546709) baseStart_6546709 baseEnd_6546709 := by
    simpa [prefixWord, tailWord_6546709, baseEnd_6546709] using wordTrace_append hprefix tailTrace_6546709
  have hstable : (prefixWord ++ tailWord_6546709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546709).length < 2 ^ (prefixWord ++ tailWord_6546709).sum := by decide
  have hdescent : baseEnd_6546709 < baseStart_6546709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546733 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6546733 : Nat := 118140960795 + 6546733 * 2 ^ 59
def prefixEnd_6546733 : Nat := 4983230072969 + 3 ^ 40 * 6546733 * 2
def baseEnd_6546733 : Nat := 1120540248550413203576543

theorem tailTrace_6546733 : CollatzResearch.WordTrace tailWord_6546733 prefixEnd_6546733 1120540248550413203576543 := by
  unfold tailWord_6546733
  simp only [CollatzResearch.WordTrace]
  refine ⟨238778968991311908825580853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159185979327541272550387235 238778968991311908825580853)
  ·
    refine ⟨22385528342935491452398205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238778968991311908825580853 22385528342935491452398205)
    ·
      refine ⟨8394573128600809294649327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22385528342935491452398205 8394573128600809294649327)
      ·
        refine ⟨12591859692901213941973991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394573128600809294649327 12591859692901213941973991)
        ·
          refine ⟨18887789539351820912960987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591859692901213941973991 18887789539351820912960987)
          ·
            refine ⟨28331684309027731369441481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887789539351820912960987 28331684309027731369441481)
            ·
              refine ⟨21248763231770798527081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28331684309027731369441481 21248763231770798527081111)
              ·
                refine ⟨31873144847656197790621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21248763231770798527081111 31873144847656197790621667)
                ·
                  refine ⟨47809717271484296685932501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31873144847656197790621667 47809717271484296685932501)
                  ·
                    refine ⟨1120540248550413203576543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47809717271484296685932501 1120540248550413203576543)
                    ·
                      rfl

theorem cell23_6546733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6546733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546733 prefixEnd_6546733 := by exact prefixLift 6546733
  have htrace : WordTrace (prefixWord ++ tailWord_6546733) baseStart_6546733 baseEnd_6546733 := by
    simpa [prefixWord, tailWord_6546733, baseEnd_6546733] using wordTrace_append hprefix tailTrace_6546733
  have hstable : (prefixWord ++ tailWord_6546733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546733).length < 2 ^ (prefixWord ++ tailWord_6546733).sum := by decide
  have hdescent : baseEnd_6546733 < baseStart_6546733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546736 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_6546736 : Nat := 118140960795 + 6546736 * 2 ^ 59
def prefixEnd_6546736 : Nat := 4983230072969 + 3 ^ 40 * 6546736 * 2
def baseEnd_6546736 : Nat := 3361622286093203098992115

theorem tailTrace_6546736 : CollatzResearch.WordTrace tailWord_6546736 prefixEnd_6546736 3361622286093203098992115 := by
  unfold tailWord_6546736
  simp only [CollatzResearch.WordTrace]
  refine ⟨119389539205150520168970031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159186052273534026891960041 119389539205150520168970031)
  ·
    refine ⟨179084308807725780253455047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119389539205150520168970031 179084308807725780253455047)
    ·
      refine ⟨268626463211588670380182571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179084308807725780253455047 268626463211588670380182571)
      ·
        refine ⟨402939694817383005570273857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268626463211588670380182571 402939694817383005570273857)
        ·
          refine ⟨302204771113037254177705393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402939694817383005570273857 302204771113037254177705393)
          ·
            refine ⟨226653578334777940633279045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302204771113037254177705393 226653578334777940633279045)
            ·
              refine ⟨42497545937770863868739821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226653578334777940633279045 42497545937770863868739821)
              ·
                refine ⟨15936579726664073950777433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42497545937770863868739821 15936579726664073950777433)
                ·
                  refine ⟨11952434794998055463083075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15936579726664073950777433 11952434794998055463083075)
                  ·
                    refine ⟨17928652192497083194624613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11952434794998055463083075 17928652192497083194624613)
                    ·
                      refine ⟨3361622286093203098992115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17928652192497083194624613 3361622286093203098992115)
                      ·
                        rfl

theorem cell23_6546736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_6546736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546736 prefixEnd_6546736 := by exact prefixLift 6546736
  have htrace : WordTrace (prefixWord ++ tailWord_6546736) baseStart_6546736 baseEnd_6546736 := by
    simpa [prefixWord, tailWord_6546736, baseEnd_6546736] using wordTrace_append hprefix tailTrace_6546736
  have hstable : (prefixWord ++ tailWord_6546736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546736).length < 2 ^ (prefixWord ++ tailWord_6546736).sum := by decide
  have hdescent : baseEnd_6546736 < baseStart_6546736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546753 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6546753 : Nat := 118140960795 + 6546753 * 2 ^ 59
def prefixEnd_6546753 : Nat := 4983230072969 + 3 ^ 40 * 6546753 * 2
def baseEnd_6546753 : Nat := 3361631015264329532479537

theorem tailTrace_6546753 : CollatzResearch.WordTrace tailWord_6546753 prefixEnd_6546753 3361631015264329532479537 := by
  unfold tailWord_6546753
  simp only [CollatzResearch.WordTrace]
  refine ⟨238779698451239452241308913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159186465634159634827539275 238779698451239452241308913)
  ·
    refine ⟨179084773838429589180981685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238779698451239452241308913 179084773838429589180981685)
    ·
      refine ⟨16789197547352773985717033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179084773838429589180981685 16789197547352773985717033)
      ·
        refine ⟨12591898160514580489287775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16789197547352773985717033 12591898160514580489287775)
        ·
          refine ⟨18887847240771870733931663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591898160514580489287775 18887847240771870733931663)
          ·
            refine ⟨28331770861157806100897495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887847240771870733931663 28331770861157806100897495)
            ·
              refine ⟨42497656291736709151346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28331770861157806100897495 42497656291736709151346243)
              ·
                refine ⟨63746484437605063727019365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42497656291736709151346243 63746484437605063727019365)
                ·
                  refine ⟨11952465832050949448816131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63746484437605063727019365 11952465832050949448816131)
                  ·
                    refine ⟨17928698748076424173224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11952465832050949448816131 17928698748076424173224197)
                    ·
                      refine ⟨3361631015264329532479537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17928698748076424173224197 3361631015264329532479537)
                      ·
                        rfl

theorem cell23_6546753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6546753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546753 prefixEnd_6546753 := by exact prefixLift 6546753
  have htrace : WordTrace (prefixWord ++ tailWord_6546753) baseStart_6546753 baseEnd_6546753 := by
    simpa [prefixWord, tailWord_6546753, baseEnd_6546753] using wordTrace_append hprefix tailTrace_6546753
  have hstable : (prefixWord ++ tailWord_6546753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546753).length < 2 ^ (prefixWord ++ tailWord_6546753).sum := by decide
  have hdescent : baseEnd_6546753 < baseStart_6546753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546776 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 6]
def baseStart_6546776 : Nat := 118140960795 + 6546776 * 2 ^ 59
def prefixEnd_6546776 : Nat := 4983230072969 + 3 ^ 40 * 6546776 * 2
def baseEnd_6546776 : Nat := 373515869479931438054659

theorem tailTrace_6546776 : CollatzResearch.WordTrace tailWord_6546776 prefixEnd_6546776 373515869479931438054659 := by
  unfold tailWord_6546776
  simp only [CollatzResearch.WordTrace]
  refine ⟨119390268665078063584698091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159187024886770751446264121 119390268665078063584698091)
  ·
    refine ⟨179085402997617095377047137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119390268665078063584698091 179085402997617095377047137)
    ·
      refine ⟨134314052248212821532785353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179085402997617095377047137 134314052248212821532785353)
      ·
        refine ⟨100735539186159616149589015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134314052248212821532785353 100735539186159616149589015)
        ·
          refine ⟨151103308779239424224383523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100735539186159616149589015 151103308779239424224383523)
          ·
            refine ⟨226654963168859136336575285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151103308779239424224383523 226654963168859136336575285)
            ·
              refine ⟨21248902797080544031553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226654963168859136336575285 21248902797080544031553933)
              ·
                refine ⟨7968338548905204011832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21248902797080544031553933 7968338548905204011832725)
                ·
                  refine ⟨373515869479931438054659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7968338548905204011832725 373515869479931438054659)
                  ·
                    rfl

theorem cell23_6546776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_6546776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546776 prefixEnd_6546776 := by exact prefixLift 6546776
  have htrace : WordTrace (prefixWord ++ tailWord_6546776) baseStart_6546776 baseEnd_6546776 := by
    simpa [prefixWord, tailWord_6546776, baseEnd_6546776] using wordTrace_append hprefix tailTrace_6546776
  have hstable : (prefixWord ++ tailWord_6546776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546776).length < 2 ^ (prefixWord ++ tailWord_6546776).sum := by decide
  have hdescent : baseEnd_6546776 < baseStart_6546776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546847 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6546847 : Nat := 118140960795 + 6546847 * 2 ^ 59
def prefixEnd_6546847 : Nat := 4983230072969 + 3 ^ 40 * 6546847 * 2
def baseEnd_6546847 : Nat := 3361679282445852164704105

theorem tailTrace_6546847 : CollatzResearch.WordTrace tailWord_6546847 prefixEnd_6546847 3361679282445852164704105 := by
  unfold tailWord_6546847
  simp only [CollatzResearch.WordTrace]
  refine ⟨238783126912898906295230795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159188751275265937530153863 238783126912898906295230795)
  ·
    refine ⟨358174690369348359442846193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238783126912898906295230795 358174690369348359442846193)
    ·
      refine ⟨268631017777011269582134645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358174690369348359442846193 268631017777011269582134645)
      ·
        refine ⟨25184157916594806523325123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268631017777011269582134645 25184157916594806523325123)
        ·
          refine ⟨37776236874892209784987685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25184157916594806523325123 37776236874892209784987685)
          ·
            refine ⟨7083044414042289334685191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37776236874892209784987685 7083044414042289334685191)
            ·
              refine ⟨10624566621063434002027787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083044414042289334685191 10624566621063434002027787)
              ·
                refine ⟨15936849931595151003041681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624566621063434002027787 15936849931595151003041681)
                ·
                  refine ⟨11952637448696363252281261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15936849931595151003041681 11952637448696363252281261)
                  ·
                    refine ⟨4482239043261136219605473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11952637448696363252281261 4482239043261136219605473)
                    ·
                      refine ⟨3361679282445852164704105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482239043261136219605473 3361679282445852164704105)
                      ·
                        rfl

theorem cell23_6546847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6546847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546847 prefixEnd_6546847 := by exact prefixLift 6546847
  have htrace : WordTrace (prefixWord ++ tailWord_6546847) baseStart_6546847 baseEnd_6546847 := by
    simpa [prefixWord, tailWord_6546847, baseEnd_6546847] using wordTrace_append hprefix tailTrace_6546847
  have hstable : (prefixWord ++ tailWord_6546847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546847).length < 2 ^ (prefixWord ++ tailWord_6546847).sum := by decide
  have hdescent : baseEnd_6546847 < baseStart_6546847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546860 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_6546860 : Nat := 118140960795 + 6546860 * 2 ^ 59
def prefixEnd_6546860 : Nat := 4983230072969 + 3 ^ 40 * 6546860 * 2
def baseEnd_6546860 : Nat := 3361685957694360613841545

theorem tailTrace_6546860 : CollatzResearch.WordTrace tailWord_6546860 prefixEnd_6546860 3361685957694360613841545 := by
  unfold tailWord_6546860
  simp only [CollatzResearch.WordTrace]
  refine ⟨119391800530925904757727017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159189067374567873010302689 119391800530925904757727017)
  ·
    refine ⟨89543850398194428568295263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119391800530925904757727017 89543850398194428568295263)
    ·
      refine ⟨134315775597291642852442895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89543850398194428568295263 134315775597291642852442895)
      ·
        refine ⟨201473663395937464278664343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134315775597291642852442895 201473663395937464278664343)
        ·
          refine ⟨302210495093906196417996515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201473663395937464278664343 302210495093906196417996515)
          ·
            refine ⟨453315742640859294626994773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302210495093906196417996515 453315742640859294626994773)
            ·
              refine ⟨5312293859072569858910095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 453315742640859294626994773 5312293859072569858910095)
              ·
                refine ⟨7968440788608854788365143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312293859072569858910095 7968440788608854788365143)
                ·
                  refine ⟨11952661182913282182547715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968440788608854788365143 11952661182913282182547715)
                  ·
                    refine ⟨17928991774369923273821573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11952661182913282182547715 17928991774369923273821573)
                    ·
                      refine ⟨3361685957694360613841545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17928991774369923273821573 3361685957694360613841545)
                      ·
                        rfl

theorem cell23_6546860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_6546860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546860 prefixEnd_6546860 := by exact prefixLift 6546860
  have htrace : WordTrace (prefixWord ++ tailWord_6546860) baseStart_6546860 baseEnd_6546860 := by
    simpa [prefixWord, tailWord_6546860, baseEnd_6546860] using wordTrace_append hprefix tailTrace_6546860
  have hstable : (prefixWord ++ tailWord_6546860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546860).length < 2 ^ (prefixWord ++ tailWord_6546860).sum := by decide
  have hdescent : baseEnd_6546860 < baseStart_6546860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546877 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6546877 : Nat := 118140960795 + 6546877 * 2 ^ 59
def prefixEnd_6546877 : Nat := 4983230072969 + 3 ^ 40 * 6546877 * 2
def baseEnd_6546877 : Nat := 3361694686865487047328967

theorem tailTrace_6546877 : CollatzResearch.WordTrace tailWord_6546877 prefixEnd_6546877 3361694686865487047328967 := by
  unfold tailWord_6546877
  simp only [CollatzResearch.WordTrace]
  refine ⟨238784221102790221418822885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159189480735193480945881923 238784221102790221418822885)
  ·
    refine ⟨44772041456773166516029291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238784221102790221418822885 44772041456773166516029291)
    ·
      refine ⟨67158062185159749774043937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44772041456773166516029291 67158062185159749774043937)
      ·
        refine ⟨50368546638869812330532953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67158062185159749774043937 50368546638869812330532953)
        ·
          refine ⟨37776409979152359247899715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50368546638869812330532953 37776409979152359247899715)
          ·
            refine ⟨56664614968728538871849573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37776409979152359247899715 56664614968728538871849573)
            ·
              refine ⟨10624615306636601038471795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56664614968728538871849573 10624615306636601038471795)
              ·
                refine ⟨15936922959954901557707693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624615306636601038471795 15936922959954901557707693)
                ·
                  refine ⟨5976346109983088084140385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15936922959954901557707693 5976346109983088084140385)
                  ·
                    refine ⟨4482259582487316063105289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976346109983088084140385 4482259582487316063105289)
                    ·
                      refine ⟨3361694686865487047328967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482259582487316063105289 3361694686865487047328967)
                      ·
                        rfl

theorem cell23_6546877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6546877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546877 prefixEnd_6546877 := by exact prefixLift 6546877
  have htrace : WordTrace (prefixWord ++ tailWord_6546877) baseStart_6546877 baseEnd_6546877 := by
    simpa [prefixWord, tailWord_6546877, baseEnd_6546877] using wordTrace_append hprefix tailTrace_6546877
  have hstable : (prefixWord ++ tailWord_6546877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546877).length < 2 ^ (prefixWord ++ tailWord_6546877).sum := by decide
  have hdescent : baseEnd_6546877 < baseStart_6546877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546890 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_6546890 : Nat := 118140960795 + 6546890 * 2 ^ 59
def prefixEnd_6546890 : Nat := 4983230072969 + 3 ^ 40 * 6546890 * 2
def baseEnd_6546890 : Nat := 3361701362113995496466407

theorem tailTrace_6546890 : CollatzResearch.WordTrace tailWord_6546890 prefixEnd_6546890 3361701362113995496466407 := by
  unfold tailWord_6546890
  simp only [CollatzResearch.WordTrace]
  refine ⟨59696173812935781159761531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159189796834495416426030749 59696173812935781159761531)
  ·
    refine ⟨89544260719403671739642297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59696173812935781159761531 89544260719403671739642297)
    ·
      refine ⟨67158195539552753804731723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89544260719403671739642297 67158195539552753804731723)
      ·
        refine ⟨100737293309329130707097585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67158195539552753804731723 100737293309329130707097585)
        ·
          refine ⟨75552969981996848030323189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100737293309329130707097585 75552969981996848030323189)
          ·
            refine ⟨7083090935812204502842799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75552969981996848030323189 7083090935812204502842799)
            ·
              refine ⟨10624636403718306754264199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083090935812204502842799 10624636403718306754264199)
              ·
                refine ⟨15936954605577460131396299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624636403718306754264199 15936954605577460131396299)
                ·
                  refine ⟨23905431908366190197094449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15936954605577460131396299 23905431908366190197094449)
                  ·
                    refine ⟨17929073931274642647820837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23905431908366190197094449 17929073931274642647820837)
                    ·
                      refine ⟨3361701362113995496466407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17929073931274642647820837 3361701362113995496466407)
                      ·
                        rfl

theorem cell23_6546890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_6546890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546890 prefixEnd_6546890 := by exact prefixLift 6546890
  have htrace : WordTrace (prefixWord ++ tailWord_6546890) baseStart_6546890 baseEnd_6546890 := by
    simpa [prefixWord, tailWord_6546890, baseEnd_6546890] using wordTrace_append hprefix tailTrace_6546890
  have hstable : (prefixWord ++ tailWord_6546890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546890).length < 2 ^ (prefixWord ++ tailWord_6546890).sum := by decide
  have hdescent : baseEnd_6546890 < baseStart_6546890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546903 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_6546903 : Nat := 118140960795 + 6546903 * 2 ^ 59
def prefixEnd_6546903 : Nat := 4983230072969 + 3 ^ 40 * 6546903 * 2
def baseEnd_6546903 : Nat := 3361708037362503945603847

theorem tailTrace_6546903 : CollatzResearch.WordTrace tailWord_6546903 prefixEnd_6546903 3361708037362503945603847 := by
  unfold tailWord_6546903
  simp only [CollatzResearch.WordTrace]
  refine ⟨238785169400696027859269363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159190112933797351906179575 238785169400696027859269363)
  ·
    refine ⟨358177754101044041788904045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238785169400696027859269363 358177754101044041788904045)
    ·
      refine ⟨134316657787891515670839017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358177754101044041788904045 134316657787891515670839017)
      ·
        refine ⟨100737493340918636753129263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134316657787891515670839017 100737493340918636753129263)
        ·
          refine ⟨151106240011377955129693895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100737493340918636753129263 151106240011377955129693895)
          ·
            refine ⟨226659360017066932694540843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151106240011377955129693895 226659360017066932694540843)
            ·
              refine ⟨339989040025600399041811265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226659360017066932694540843 339989040025600399041811265)
              ·
                refine ⟨254991780019200299281358449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339989040025600399041811265 254991780019200299281358449)
                ·
                  refine ⟨191243835014400224461018837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254991780019200299281358449 191243835014400224461018837)
                  ·
                    refine ⟨4482277383150005260805129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191243835014400224461018837 4482277383150005260805129)
                    ·
                      refine ⟨3361708037362503945603847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482277383150005260805129 3361708037362503945603847)
                      ·
                        rfl

theorem cell23_6546903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_6546903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546903 prefixEnd_6546903 := by exact prefixLift 6546903
  have htrace : WordTrace (prefixWord ++ tailWord_6546903) baseStart_6546903 baseEnd_6546903 := by
    simpa [prefixWord, tailWord_6546903, baseEnd_6546903] using wordTrace_append hprefix tailTrace_6546903
  have hstable : (prefixWord ++ tailWord_6546903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546903).length < 2 ^ (prefixWord ++ tailWord_6546903).sum := by decide
  have hdescent : baseEnd_6546903 < baseStart_6546903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546916 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_6546916 : Nat := 118140960795 + 6546916 * 2 ^ 59
def prefixEnd_6546916 : Nat := 4983230072969 + 3 ^ 40 * 6546916 * 2
def baseEnd_6546916 : Nat := 3361714712611012394741287

theorem tailTrace_6546916 : CollatzResearch.WordTrace tailWord_6546916 prefixEnd_6546916 3361714712611012394741287 := by
  unfold tailWord_6546916
  simp only [CollatzResearch.WordTrace]
  refine ⟨119392821774824465539746301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159190429033099287386328401 119392821774824465539746301)
  ·
    refine ⟨44772308165559174577404863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119392821774824465539746301 44772308165559174577404863)
    ·
      refine ⟨67158462248338761866107295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44772308165559174577404863 67158462248338761866107295)
      ·
        refine ⟨100737693372508142799160943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67158462248338761866107295 100737693372508142799160943)
        ·
          refine ⟨151106540058762214198741415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100737693372508142799160943 151106540058762214198741415)
          ·
            refine ⟨226659810088143321298112123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151106540058762214198741415 226659810088143321298112123)
            ·
              refine ⟨339989715132214981947168185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226659810088143321298112123 339989715132214981947168185)
              ·
                refine ⟨254992286349161236460376139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339989715132214981947168185 254992286349161236460376139)
                ·
                  refine ⟨382488429523741854690564209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254992286349161236460376139 382488429523741854690564209)
                  ·
                    refine ⟨286866322142806391017923157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382488429523741854690564209 286866322142806391017923157)
                    ·
                      refine ⟨3361714712611012394741287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286866322142806391017923157 3361714712611012394741287)
                      ·
                        rfl

theorem cell23_6546916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_6546916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546916 prefixEnd_6546916 := by exact prefixLift 6546916
  have htrace : WordTrace (prefixWord ++ tailWord_6546916) baseStart_6546916 baseEnd_6546916 := by
    simpa [prefixWord, tailWord_6546916, baseEnd_6546916] using wordTrace_append hprefix tailTrace_6546916
  have hstable : (prefixWord ++ tailWord_6546916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546916).length < 2 ^ (prefixWord ++ tailWord_6546916).sum := by decide
  have hdescent : baseEnd_6546916 < baseStart_6546916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6546954 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_6546954 : Nat := 118140960795 + 6546954 * 2 ^ 59
def prefixEnd_6546954 : Nat := 4983230072969 + 3 ^ 40 * 6546954 * 2
def baseEnd_6546954 : Nat := 3361734224875883246066113

theorem tailTrace_6546954 : CollatzResearch.WordTrace tailWord_6546954 prefixEnd_6546954 3361734224875883246066113 := by
  unfold tailWord_6546954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59696757380877815892343979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159191353015674175712917277 59696757380877815892343979)
  ·
    refine ⟨89545136071316723838515969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59696757380877815892343979 89545136071316723838515969)
    ·
      refine ⟨67158852053487542878886977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89545136071316723838515969 67158852053487542878886977)
      ·
        refine ⟨50369139040115657159165233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67158852053487542878886977 50369139040115657159165233)
        ·
          refine ⟨37776854280086742869373925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50369139040115657159165233 37776854280086742869373925)
          ·
            refine ⟨7083160177516264288007611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37776854280086742869373925 7083160177516264288007611)
            ·
              refine ⟨10624740266274396432011417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083160177516264288007611 10624740266274396432011417)
              ·
                refine ⟨7968555199705797324008563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624740266274396432011417 7968555199705797324008563)
                ·
                  refine ⟨11952832799558695986012845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968555199705797324008563 11952832799558695986012845)
                  ·
                    refine ⟨4482312299834510994754817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11952832799558695986012845 4482312299834510994754817)
                    ·
                      refine ⟨3361734224875883246066113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482312299834510994754817 3361734224875883246066113)
                      ·
                        rfl

theorem cell23_6546954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_6546954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6546954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6546954 prefixEnd_6546954 := by exact prefixLift 6546954
  have htrace : WordTrace (prefixWord ++ tailWord_6546954) baseStart_6546954 baseEnd_6546954 := by
    simpa [prefixWord, tailWord_6546954, baseEnd_6546954] using wordTrace_append hprefix tailTrace_6546954
  have hstable : (prefixWord ++ tailWord_6546954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6546954).length < 2 ^ (prefixWord ++ tailWord_6546954).sum := by decide
  have hdescent : baseEnd_6546954 < baseStart_6546954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6546954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547000 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_6547000 : Nat := 118140960795 + 6547000 * 2 ^ 59
def prefixEnd_6547000 : Nat := 4983230072969 + 3 ^ 40 * 6547000 * 2
def baseEnd_6547000 : Nat := 3361757844985990066090901

theorem tailTrace_6547000 : CollatzResearch.WordTrace tailWord_6547000 prefixEnd_6547000 3361757844985990066090901 := by
  unfold tailWord_6547000
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394353640672306712775227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159192471520896408950366969 119394353640672306712775227)
  ·
    refine ⟨179091530461008460069162841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119394353640672306712775227 179091530461008460069162841)
    ·
      refine ⟨134318647845756345051872131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179091530461008460069162841 134318647845756345051872131)
      ·
        refine ⟨201477971768634517577808197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134318647845756345051872131 201477971768634517577808197)
        ·
          refine ⟨37777119706618972045839037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201477971768634517577808197 37777119706618972045839037)
          ·
            refine ⟨14166419889982114517189639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37777119706618972045839037 14166419889982114517189639)
            ·
              refine ⟨21249629834973171775784459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166419889982114517189639 21249629834973171775784459)
              ·
                refine ⟨31874444752459757663676689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21249629834973171775784459 31874444752459757663676689)
                ·
                  refine ⟨23905833564344818247757517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31874444752459757663676689 23905833564344818247757517)
                  ·
                    refine ⟨8964687586629306842909069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23905833564344818247757517 8964687586629306842909069)
                    ·
                      refine ⟨3361757844985990066090901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8964687586629306842909069 3361757844985990066090901)
                      ·
                        rfl

theorem cell23_6547000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_6547000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547000 prefixEnd_6547000 := by exact prefixLift 6547000
  have htrace : WordTrace (prefixWord ++ tailWord_6547000) baseStart_6547000 baseEnd_6547000 := by
    simpa [prefixWord, tailWord_6547000, baseEnd_6547000] using wordTrace_append hprefix tailTrace_6547000
  have hstable : (prefixWord ++ tailWord_6547000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547000).length < 2 ^ (prefixWord ++ tailWord_6547000).sum := by decide
  have hdescent : baseEnd_6547000 < baseStart_6547000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547020 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_6547020 : Nat := 118140960795 + 6547020 * 2 ^ 59
def prefixEnd_6547020 : Nat := 4983230072969 + 3 ^ 40 * 6547020 * 2
def baseEnd_6547020 : Nat := 1120589371533026662613603

theorem tailTrace_6547020 : CollatzResearch.WordTrace tailWord_6547020 prefixEnd_6547020 1120589371533026662613603 := by
  unfold tailWord_6547020
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394718370636078420639257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159192957827514771227519009 119394718370636078420639257)
  ·
    refine ⟨89546038777977058815479443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119394718370636078420639257 89546038777977058815479443)
    ·
      refine ⟨134319058166965588223219165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89546038777977058815479443 134319058166965588223219165)
      ·
        refine ⟨50369646812612095583707187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134319058166965588223219165 50369646812612095583707187)
        ·
          refine ⟨75554470218918143375560781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50369646812612095583707187 75554470218918143375560781)
          ·
            refine ⟨28332926332094303765835293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75554470218918143375560781 28332926332094303765835293)
            ·
              refine ⟨10624847374535363912188235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28332926332094303765835293 10624847374535363912188235)
              ·
                refine ⟨15937271061803045868282353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624847374535363912188235 15937271061803045868282353)
                ·
                  refine ⟨11952953296352284401211765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15937271061803045868282353 11952953296352284401211765)
                  ·
                    refine ⟨1120589371533026662613603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11952953296352284401211765 1120589371533026662613603)
                    ·
                      rfl

theorem cell23_6547020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_6547020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547020 prefixEnd_6547020 := by exact prefixLift 6547020
  have htrace : WordTrace (prefixWord ++ tailWord_6547020) baseStart_6547020 baseEnd_6547020 := by
    simpa [prefixWord, tailWord_6547020, baseEnd_6547020] using wordTrace_append hprefix tailTrace_6547020
  have hstable : (prefixWord ++ tailWord_6547020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547020).length < 2 ^ (prefixWord ++ tailWord_6547020).sum := by decide
  have hdescent : baseEnd_6547020 < baseStart_6547020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547127 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 1, 5]
def baseStart_6547127 : Nat := 118140960795 + 6547127 * 2 ^ 59
def prefixEnd_6547127 : Nat := 4983230072969 + 3 ^ 40 * 6547127 * 2
def baseEnd_6547127 : Nat := 1120607685676370356400939

theorem tailTrace_6547127 : CollatzResearch.WordTrace tailWord_6547127 prefixEnd_6547127 1120607685676370356400939 := by
  unfold tailWord_6547127
  simp only [CollatzResearch.WordTrace]
  refine ⟨238793339351884514115423635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159195559567923009410282423 238793339351884514115423635)
  ·
    refine ⟨358190009027826771173135453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238793339351884514115423635 358190009027826771173135453)
    ·
      refine ⟨134321253385435039189925795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358190009027826771173135453 134321253385435039189925795)
      ·
        refine ⟨201481880078152558784888693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134321253385435039189925795 201481880078152558784888693)
        ·
          refine ⟨18888926257326802386083315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201481880078152558784888693 18888926257326802386083315)
          ·
            refine ⟨28333389385990203579124973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18888926257326802386083315 28333389385990203579124973)
            ·
              refine ⟨10625021019746326342171865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28333389385990203579124973 10625021019746326342171865)
              ·
                refine ⟨7968765764809744756628899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10625021019746326342171865 7968765764809744756628899)
                ·
                  refine ⟨11953148647214617134943349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968765764809744756628899 11953148647214617134943349)
                  ·
                    refine ⟨1120607685676370356400939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11953148647214617134943349 1120607685676370356400939)
                    ·
                      rfl

theorem cell23_6547127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_6547127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547127 prefixEnd_6547127 := by exact prefixLift 6547127
  have htrace : WordTrace (prefixWord ++ tailWord_6547127) baseStart_6547127 baseEnd_6547127 := by
    simpa [prefixWord, tailWord_6547127, baseEnd_6547127] using wordTrace_append hprefix tailTrace_6547127
  have hstable : (prefixWord ++ tailWord_6547127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547127).length < 2 ^ (prefixWord ++ tailWord_6547127).sum := by decide
  have hdescent : baseEnd_6547127 < baseStart_6547127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547134 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_6547134 : Nat := 118140960795 + 6547134 * 2 ^ 59
def prefixEnd_6547134 : Nat := 4983230072969 + 3 ^ 40 * 6547134 * 2
def baseEnd_6547134 : Nat := 3361826651393692541815285

theorem tailTrace_6547134 : CollatzResearch.WordTrace tailWord_6547134 prefixEnd_6547134 3361826651393692541815285 := by
  unfold tailWord_6547134
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849199332857394288866057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159195729775239436207285637 29849199332857394288866057)
  ·
    refine ⟨22386899499643045716649543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29849199332857394288866057 22386899499643045716649543)
    ·
      refine ⟨33580349249464568574974315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22386899499643045716649543 33580349249464568574974315)
      ·
        refine ⟨50370523874196852862461473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33580349249464568574974315 50370523874196852862461473)
        ·
          refine ⟨37777892905647639646846105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50370523874196852862461473 37777892905647639646846105)
          ·
            refine ⟨28333419679235729735134579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37777892905647639646846105 28333419679235729735134579)
            ·
              refine ⟨42500129518853594602701869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28333419679235729735134579 42500129518853594602701869)
              ·
                refine ⟨15937548569570097976013201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42500129518853594602701869 15937548569570097976013201)
                ·
                  refine ⟨11953161427177573482009901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15937548569570097976013201 11953161427177573482009901)
                  ·
                    refine ⟨4482435535191590055753713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11953161427177573482009901 4482435535191590055753713)
                    ·
                      refine ⟨3361826651393692541815285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482435535191590055753713 3361826651393692541815285)
                      ·
                        rfl

theorem cell23_6547134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_6547134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547134 prefixEnd_6547134 := by exact prefixLift 6547134
  have htrace : WordTrace (prefixWord ++ tailWord_6547134) baseStart_6547134 baseEnd_6547134 := by
    simpa [prefixWord, tailWord_6547134, baseEnd_6547134] using wordTrace_append hprefix tailTrace_6547134
  have hstable : (prefixWord ++ tailWord_6547134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547134).length < 2 ^ (prefixWord ++ tailWord_6547134).sum := by decide
  have hdescent : baseEnd_6547134 < baseStart_6547134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547153 : List Nat := [1, 2, 2, 1, 2, 15]
def baseStart_6547153 : Nat := 118140960795 + 6547153 * 2 ^ 59
def prefixEnd_6547153 : Nat := 4983230072969 + 3 ^ 40 * 6547153 * 2
def baseEnd_6547153 : Nat := 13834717726444971059579

theorem tailTrace_6547153 : CollatzResearch.WordTrace tailWord_6547153 prefixEnd_6547153 13834717726444971059579 := by
  unfold tailWord_6547153
  simp only [CollatzResearch.WordTrace]
  refine ⟨238794287649790320555870113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159196191766526880370580075 238794287649790320555870113)
  ·
    refine ⟨179095715737342740416902585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238794287649790320555870113 179095715737342740416902585)
    ·
      refine ⟨134321786803007055312676939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179095715737342740416902585 134321786803007055312676939)
      ·
        refine ⟨201482680204510582969015409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134321786803007055312676939 201482680204510582969015409)
        ·
          refine ⟨151112010153382937226761557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201482680204510582969015409 151112010153382937226761557)
          ·
            refine ⟨13834717726444971059579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 151112010153382937226761557 13834717726444971059579)
            ·
              rfl

theorem cell23_6547153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 15].length) (baseStart_6547153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547153 prefixEnd_6547153 := by exact prefixLift 6547153
  have htrace : WordTrace (prefixWord ++ tailWord_6547153) baseStart_6547153 baseEnd_6547153 := by
    simpa [prefixWord, tailWord_6547153, baseEnd_6547153] using wordTrace_append hprefix tailTrace_6547153
  have hstable : (prefixWord ++ tailWord_6547153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547153).length < 2 ^ (prefixWord ++ tailWord_6547153).sum := by decide
  have hdescent : baseEnd_6547153 < baseStart_6547153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547160 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6547160 : Nat := 118140960795 + 6547160 * 2 ^ 59
def prefixEnd_6547160 : Nat := 4983230072969 + 3 ^ 40 * 6547160 * 2
def baseEnd_6547160 : Nat := 3361840001890709440090165

theorem tailTrace_6547160 : CollatzResearch.WordTrace tailWord_6547160 prefixEnd_6547160 3361840001890709440090165 := by
  unfold tailWord_6547160
  simp only [CollatzResearch.WordTrace]
  refine ⟨119397271480382480375687467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159196361973843307167583289 119397271480382480375687467)
  ·
    refine ⟨179095907220573720563531201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119397271480382480375687467 179095907220573720563531201)
    ·
      refine ⟨134321930415430290422648401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179095907220573720563531201 134321930415430290422648401)
      ·
        refine ⟨100741447811572717816986301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134321930415430290422648401 100741447811572717816986301)
        ·
          refine ⟨37778042929339769181369863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100741447811572717816986301 37778042929339769181369863)
          ·
            refine ⟨56667064394009653772054795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37778042929339769181369863 56667064394009653772054795)
            ·
              refine ⟨85000596591014480658082193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56667064394009653772054795 85000596591014480658082193)
              ·
                refine ⟨63750447443260860493561645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85000596591014480658082193 63750447443260860493561645)
                ·
                  refine ⟨23906417791222822685085617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63750447443260860493561645 23906417791222822685085617)
                  ·
                    refine ⟨17929813343417117013814213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23906417791222822685085617 17929813343417117013814213)
                    ·
                      refine ⟨3361840001890709440090165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17929813343417117013814213 3361840001890709440090165)
                      ·
                        rfl

theorem cell23_6547160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6547160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547160 prefixEnd_6547160 := by exact prefixLift 6547160
  have htrace : WordTrace (prefixWord ++ tailWord_6547160) baseStart_6547160 baseEnd_6547160 := by
    simpa [prefixWord, tailWord_6547160, baseEnd_6547160] using wordTrace_append hprefix tailTrace_6547160
  have hstable : (prefixWord ++ tailWord_6547160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547160).length < 2 ^ (prefixWord ++ tailWord_6547160).sum := by decide
  have hdescent : baseEnd_6547160 < baseStart_6547160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547181 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6547181 : Nat := 118140960795 + 6547181 * 2 ^ 59
def prefixEnd_6547181 : Nat := 4983230072969 + 3 ^ 40 * 6547181 * 2
def baseEnd_6547181 : Nat := 3361850784984453857927569

theorem tailTrace_6547181 : CollatzResearch.WordTrace tailWord_6547181 prefixEnd_6547181 3361850784984453857927569 := by
  unfold tailWord_6547181
  simp only [CollatzResearch.WordTrace]
  refine ⟨238795308893688881337889397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159196872595792587558592931 238795308893688881337889397)
  ·
    refine ⟨22387060208783332625427131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238795308893688881337889397 22387060208783332625427131)
    ·
      refine ⟨33580590313174998938140697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22387060208783332625427131 33580590313174998938140697)
      ·
        refine ⟨25185442734881249203605523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33580590313174998938140697 25185442734881249203605523)
        ·
          refine ⟨37778164102321873805408285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25185442734881249203605523 37778164102321873805408285)
          ·
            refine ⟨14166811538370702677028107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37778164102321873805408285 14166811538370702677028107)
            ·
              refine ⟨21250217307556054015542161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166811538370702677028107 21250217307556054015542161)
              ·
                refine ⟨15937662980667040511656621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21250217307556054015542161 15937662980667040511656621)
                ·
                  refine ⟨5976623617750140191871233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15937662980667040511656621 5976623617750140191871233)
                  ·
                    refine ⟨4482467713312605143903425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976623617750140191871233 4482467713312605143903425)
                    ·
                      refine ⟨3361850784984453857927569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482467713312605143903425 3361850784984453857927569)
                      ·
                        rfl

theorem cell23_6547181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6547181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547181 prefixEnd_6547181 := by exact prefixLift 6547181
  have htrace : WordTrace (prefixWord ++ tailWord_6547181) baseStart_6547181 baseEnd_6547181 := by
    simpa [prefixWord, tailWord_6547181, baseEnd_6547181] using wordTrace_append hprefix tailTrace_6547181
  have hstable : (prefixWord ++ tailWord_6547181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547181).length < 2 ^ (prefixWord ++ tailWord_6547181).sum := by decide
  have hdescent : baseEnd_6547181 < baseStart_6547181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547198 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6547198 : Nat := 118140960795 + 6547198 * 2 ^ 59
def prefixEnd_6547198 : Nat := 4983230072969 + 3 ^ 40 * 6547198 * 2
def baseEnd_6547198 : Nat := 3361859514155580291414991

theorem tailTrace_6547198 : CollatzResearch.WordTrace tailWord_6547198 prefixEnd_6547198 3361859514155580291414991 := by
  unfold tailWord_6547198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849491116828411655157281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159197285956418195494172165 29849491116828411655157281)
  ·
    refine ⟨22387118337621308741367961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29849491116828411655157281 22387118337621308741367961)
    ·
      refine ⟨16790338753215981556025971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22387118337621308741367961 16790338753215981556025971)
      ·
        refine ⟨25185508129823972334038957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16790338753215981556025971 25185508129823972334038957)
        ·
          refine ⟨9444565548683989625264609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25185508129823972334038957 9444565548683989625264609)
          ·
            refine ⟨7083424161512992218948457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9444565548683989625264609 7083424161512992218948457)
            ·
              refine ⟨5312568121134744164211343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083424161512992218948457 5312568121134744164211343)
              ·
                refine ⟨7968852181702116246317015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312568121134744164211343 7968852181702116246317015)
                ·
                  refine ⟨11953278272553174369475523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968852181702116246317015 11953278272553174369475523)
                  ·
                    refine ⟨17929917408829761554213285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11953278272553174369475523 17929917408829761554213285)
                    ·
                      refine ⟨3361859514155580291414991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17929917408829761554213285 3361859514155580291414991)
                      ·
                        rfl

theorem cell23_6547198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6547198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547198 prefixEnd_6547198 := by exact prefixLift 6547198
  have htrace : WordTrace (prefixWord ++ tailWord_6547198) baseStart_6547198 baseEnd_6547198 := by
    simpa [prefixWord, tailWord_6547198, baseEnd_6547198] using wordTrace_append hprefix tailTrace_6547198
  have hstable : (prefixWord ++ tailWord_6547198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547198).length < 2 ^ (prefixWord ++ tailWord_6547198).sum := by decide
  have hdescent : baseEnd_6547198 < baseStart_6547198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547231 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 2, 1, 3]
def baseStart_6547231 : Nat := 118140960795 + 6547231 * 2 ^ 59
def prefixEnd_6547231 : Nat := 4983230072969 + 3 ^ 40 * 6547231 * 2
def baseEnd_6547231 : Nat := 3361876459017178662302339

theorem tailTrace_6547231 : CollatzResearch.WordTrace tailWord_6547231 prefixEnd_6547231 3361876459017178662302339 := by
  unfold tailWord_6547231
  simp only [CollatzResearch.WordTrace]
  refine ⟨238797132543507739877209547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159198088362338493251473031 238797132543507739877209547)
  ·
    refine ⟨358195698815261609815814321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238797132543507739877209547 358195698815261609815814321)
    ·
      refine ⟨268646774111446207361860741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358195698815261609815814321 268646774111446207361860741)
      ·
        refine ⟨50371270145896163880348889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268646774111446207361860741 50371270145896163880348889)
        ·
          refine ⟨37778452609422122910261667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50371270145896163880348889 37778452609422122910261667)
          ·
            refine ⟨56667678914133184365392501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37778452609422122910261667 56667678914133184365392501)
            ·
              refine ⟨5312594898199986034255547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56667678914133184365392501 5312594898199986034255547)
              ·
                refine ⟨7968892347299979051383321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312594898199986034255547 7968892347299979051383321)
                ·
                  refine ⟨5976669260474984288537491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968892347299979051383321 5976669260474984288537491)
                  ·
                    refine ⟨8965003890712476432806237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5976669260474984288537491 8965003890712476432806237)
                    ·
                      refine ⟨3361876459017178662302339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8965003890712476432806237 3361876459017178662302339)
                      ·
                        rfl

theorem cell23_6547231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_6547231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547231 prefixEnd_6547231 := by exact prefixLift 6547231
  have htrace : WordTrace (prefixWord ++ tailWord_6547231) baseStart_6547231 baseEnd_6547231 := by
    simpa [prefixWord, tailWord_6547231, baseEnd_6547231] using wordTrace_append hprefix tailTrace_6547231
  have hstable : (prefixWord ++ tailWord_6547231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547231).length < 2 ^ (prefixWord ++ tailWord_6547231).sum := by decide
  have hdescent : baseEnd_6547231 < baseStart_6547231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547260 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 9]
def baseStart_6547260 : Nat := 118140960795 + 6547260 * 2 ^ 59
def prefixEnd_6547260 : Nat := 4983230072969 + 3 ^ 40 * 6547260 * 2
def baseEnd_6547260 : Nat := 373543483328462116537745

theorem tailTrace_6547260 : CollatzResearch.WordTrace tailWord_6547260 prefixEnd_6547260 373543483328462116537745 := by
  unfold tailWord_6547260
  simp only [CollatzResearch.WordTrace]
  refine ⟨119399095130201338915007617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159198793506935118553343489 119399095130201338915007617)
  ·
    refine ⟨89549321347651004186255713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119399095130201338915007617 89549321347651004186255713)
    ·
      refine ⟨67161991010738253139691785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89549321347651004186255713 67161991010738253139691785)
      ·
        refine ⟨50371493258053689854768839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67161991010738253139691785 50371493258053689854768839)
        ·
          refine ⟨75557239887080534782153259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50371493258053689854768839 75557239887080534782153259)
          ·
            refine ⟨113335859830620802173229889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75557239887080534782153259 113335859830620802173229889)
            ·
              refine ⟨85001894872965601629922417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113335859830620802173229889 85001894872965601629922417)
              ·
                refine ⟨63751421154724201222441813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85001894872965601629922417 63751421154724201222441813)
                ·
                  refine ⟨373543483328462116537745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63751421154724201222441813 373543483328462116537745)
                  ·
                    rfl

theorem cell23_6547260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_6547260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547260 prefixEnd_6547260 := by exact prefixLift 6547260
  have htrace : WordTrace (prefixWord ++ tailWord_6547260) baseStart_6547260 baseEnd_6547260 := by
    simpa [prefixWord, tailWord_6547260, baseEnd_6547260] using wordTrace_append hprefix tailTrace_6547260
  have hstable : (prefixWord ++ tailWord_6547260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547260).length < 2 ^ (prefixWord ++ tailWord_6547260).sum := by decide
  have hdescent : baseEnd_6547260 < baseStart_6547260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547317 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6547317 : Nat := 118140960795 + 6547317 * 2 ^ 59
def prefixEnd_6547317 : Nat := 4983230072969 + 3 ^ 40 * 6547317 * 2
def baseEnd_6547317 : Nat := 3361920618353465325826943

theorem tailTrace_6547317 : CollatzResearch.WordTrace tailWord_6547317 prefixEnd_6547317 3361920618353465325826943 := by
  unfold tailWord_6547317
  simp only [CollatzResearch.WordTrace]
  refine ⟨238800269221196176564840205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159200179480797451043226803 238800269221196176564840205)
  ·
    refine ⟨89550100957948566211815077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238800269221196176564840205 89550100957948566211815077)
    ·
      refine ⟨16790643929615356164715327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89550100957948566211815077 16790643929615356164715327)
      ·
        refine ⟨25185965894423034247072991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16790643929615356164715327 25185965894423034247072991)
        ·
          refine ⟨37778948841634551370609487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25185965894423034247072991 37778948841634551370609487)
          ·
            refine ⟨56668423262451827055914231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37778948841634551370609487 56668423262451827055914231)
            ·
              refine ⟨85002634893677740583871347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56668423262451827055914231 85002634893677740583871347)
              ·
                refine ⟨127503952340516610875807021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85002634893677740583871347 127503952340516610875807021)
                ·
                  refine ⟨47813982127693729078427633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127503952340516610875807021 47813982127693729078427633)
                  ·
                    refine ⟨35860486595770296808820725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47813982127693729078427633 35860486595770296808820725)
                    ·
                      refine ⟨3361920618353465325826943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35860486595770296808820725 3361920618353465325826943)
                      ·
                        rfl

theorem cell23_6547317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6547317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547317 prefixEnd_6547317 := by exact prefixLift 6547317
  have htrace : WordTrace (prefixWord ++ tailWord_6547317) baseStart_6547317 baseEnd_6547317 := by
    simpa [prefixWord, tailWord_6547317, baseEnd_6547317] using wordTrace_append hprefix tailTrace_6547317
  have hstable : (prefixWord ++ tailWord_6547317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547317).length < 2 ^ (prefixWord ++ tailWord_6547317).sum := by decide
  have hdescent : baseEnd_6547317 < baseStart_6547317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547320 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_6547320 : Nat := 118140960795 + 6547320 * 2 ^ 59
def prefixEnd_6547320 : Nat := 4983230072969 + 3 ^ 40 * 6547320 * 2
def baseEnd_6547320 : Nat := 1120640719598476271363143

theorem tailTrace_6547320 : CollatzResearch.WordTrace tailWord_6547320 prefixEnd_6547320 1120640719598476271363143 := by
  unfold tailWord_6547320
  simp only [CollatzResearch.WordTrace]
  refine ⟨119400189320092654038599707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159200252426790205384799609 119400189320092654038599707)
  ·
    refine ⟨179100283980138981057899561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119400189320092654038599707 179100283980138981057899561)
    ·
      refine ⟨134325212985104235793424671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179100283980138981057899561 134325212985104235793424671)
      ·
        refine ⟨201487819477656353690137007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134325212985104235793424671 201487819477656353690137007)
        ·
          refine ⟨302231729216484530535205511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201487819477656353690137007 302231729216484530535205511)
          ·
            refine ⟨453347593824726795802808267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302231729216484530535205511 453347593824726795802808267)
            ·
              refine ⟨680021390737090193704212401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453347593824726795802808267 680021390737090193704212401)
              ·
                refine ⟨510016043052817645278159301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680021390737090193704212401 510016043052817645278159301)
                ·
                  refine ⟨95628008072403308489654869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 510016043052817645278159301 95628008072403308489654869)
                  ·
                    refine ⟨1120640719598476271363143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95628008072403308489654869 1120640719598476271363143)
                    ·
                      rfl

theorem cell23_6547320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_6547320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547320 prefixEnd_6547320 := by exact prefixLift 6547320
  have htrace : WordTrace (prefixWord ++ tailWord_6547320) baseStart_6547320 baseEnd_6547320 := by
    simpa [prefixWord, tailWord_6547320, baseEnd_6547320] using wordTrace_append hprefix tailTrace_6547320
  have hstable : (prefixWord ++ tailWord_6547320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547320).length < 2 ^ (prefixWord ++ tailWord_6547320).sum := by decide
  have hdescent : baseEnd_6547320 < baseStart_6547320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547354 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_6547354 : Nat := 118140960795 + 6547354 * 2 ^ 59
def prefixEnd_6547354 : Nat := 4983230072969 + 3 ^ 40 * 6547354 * 2
def baseEnd_6547354 : Nat := 1120646539045893893688091

theorem tailTrace_6547354 : CollatzResearch.WordTrace tailWord_6547354 prefixEnd_6547354 1120646539045893893688091 := by
  unfold tailWord_6547354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59700404680515532970984279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159201079148041421255958077 59700404680515532970984279)
  ·
    refine ⟨89550607020773299456476419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59700404680515532970984279 89550607020773299456476419)
    ·
      refine ⟨134325910531159949184714629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89550607020773299456476419 134325910531159949184714629)
      ·
        refine ⟨25186108224592490472133993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134325910531159949184714629 25186108224592490472133993)
        ·
          refine ⟨18889581168444367854100495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25186108224592490472133993 18889581168444367854100495)
          ·
            refine ⟨28334371752666551781150743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18889581168444367854100495 28334371752666551781150743)
            ·
              refine ⟨42501557628999827671726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28334371752666551781150743 42501557628999827671726115)
              ·
                refine ⟨63752336443499741507589173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42501557628999827671726115 63752336443499741507589173)
                ·
                  refine ⟨5976781541578100766336485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63752336443499741507589173 5976781541578100766336485)
                  ·
                    refine ⟨1120646539045893893688091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976781541578100766336485 1120646539045893893688091)
                    ·
                      rfl

theorem cell23_6547354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_6547354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547354 prefixEnd_6547354 := by exact prefixLift 6547354
  have htrace : WordTrace (prefixWord ++ tailWord_6547354) baseStart_6547354 baseEnd_6547354 := by
    simpa [prefixWord, tailWord_6547354, baseEnd_6547354] using wordTrace_append hprefix tailTrace_6547354
  have hstable : (prefixWord ++ tailWord_6547354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547354).length < 2 ^ (prefixWord ++ tailWord_6547354).sum := by decide
  have hdescent : baseEnd_6547354 < baseStart_6547354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547364 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_6547364 : Nat := 118140960795 + 6547364 * 2 ^ 59
def prefixEnd_6547364 : Nat := 4983230072969 + 3 ^ 40 * 6547364 * 2
def baseEnd_6547364 : Nat := 3361944751944226641939227

theorem tailTrace_6547364 : CollatzResearch.WordTrace tailWord_6547364 prefixEnd_6547364 3361944751944226641939227 := by
  unfold tailWord_6547364
  simp only [CollatzResearch.WordTrace]
  refine ⟨119400991726012951795900573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159201322301350602394534097 119400991726012951795900573)
  ·
    refine ⟨44775371897254856923462715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119400991726012951795900573 44775371897254856923462715)
    ·
      refine ⟨67163057845882285385194073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44775371897254856923462715 67163057845882285385194073)
      ·
        refine ⟨50372293384411714038895555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67163057845882285385194073 50372293384411714038895555)
        ·
          refine ⟨75558440076617571058343333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50372293384411714038895555 75558440076617571058343333)
          ·
            refine ⟨14167207514365794573439375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75558440076617571058343333 14167207514365794573439375)
            ·
              refine ⟨21250811271548691860159063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167207514365794573439375 21250811271548691860159063)
              ·
                refine ⟨31876216907323037790238595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21250811271548691860159063 31876216907323037790238595)
                ·
                  refine ⟨47814325360984556685357893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31876216907323037790238595 47814325360984556685357893)
                  ·
                    refine ⟨8965186005184604378504605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47814325360984556685357893 8965186005184604378504605)
                    ·
                      refine ⟨3361944751944226641939227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8965186005184604378504605 3361944751944226641939227)
                      ·
                        rfl

theorem cell23_6547364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_6547364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547364 prefixEnd_6547364 := by exact prefixLift 6547364
  have htrace : WordTrace (prefixWord ++ tailWord_6547364) baseStart_6547364 baseEnd_6547364 := by
    simpa [prefixWord, tailWord_6547364, baseEnd_6547364] using wordTrace_append hprefix tailTrace_6547364
  have hstable : (prefixWord ++ tailWord_6547364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547364).length < 2 ^ (prefixWord ++ tailWord_6547364).sum := by decide
  have hdescent : baseEnd_6547364 < baseStart_6547364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547388 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_6547388 : Nat := 118140960795 + 6547388 * 2 ^ 59
def prefixEnd_6547388 : Nat := 4983230072969 + 3 ^ 40 * 6547388 * 2
def baseEnd_6547388 : Nat := 1120652358493311516013039

theorem tailTrace_6547388 : CollatzResearch.WordTrace tailWord_6547388 prefixEnd_6547388 1120652358493311516013039 := by
  unfold tailWord_6547388
  simp only [CollatzResearch.WordTrace]
  refine ⟨119401429401969477845337409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159201905869292637127116545 119401429401969477845337409)
  ·
    refine ⟨89551072051477108384003057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119401429401969477845337409 89551072051477108384003057)
    ·
      refine ⟨67163304038607831288002293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89551072051477108384003057 67163304038607831288002293)
      ·
        refine ⟨6296559753619484183250215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67163304038607831288002293 6296559753619484183250215)
        ·
          refine ⟨9444839630429226274875323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296559753619484183250215 9444839630429226274875323)
          ·
            refine ⟨14167259445643839412312985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444839630429226274875323 14167259445643839412312985)
            ·
              refine ⟨10625444584232879559234739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14167259445643839412312985 10625444584232879559234739)
              ·
                refine ⟨15938166876349319338852109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10625444584232879559234739 15938166876349319338852109)
                ·
                  refine ⟨5976812578630994752069541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15938166876349319338852109 5976812578630994752069541)
                  ·
                    refine ⟨1120652358493311516013039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976812578630994752069541 1120652358493311516013039)
                    ·
                      rfl

theorem cell23_6547388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_6547388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547388 prefixEnd_6547388 := by exact prefixLift 6547388
  have htrace : WordTrace (prefixWord ++ tailWord_6547388) baseStart_6547388 baseEnd_6547388 := by
    simpa [prefixWord, tailWord_6547388, baseEnd_6547388] using wordTrace_append hprefix tailTrace_6547388
  have hstable : (prefixWord ++ tailWord_6547388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547388).length < 2 ^ (prefixWord ++ tailWord_6547388).sum := by decide
  have hdescent : baseEnd_6547388 < baseStart_6547388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547397 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_6547397 : Nat := 118140960795 + 6547397 * 2 ^ 59
def prefixEnd_6547397 : Nat := 4983230072969 + 3 ^ 40 * 6547397 * 2
def baseEnd_6547397 : Nat := 1120653898935275004275525

theorem tailTrace_6547397 : CollatzResearch.WordTrace tailWord_6547397 prefixEnd_6547397 1120653898935275004275525 := by
  unfold tailWord_6547397
  simp only [CollatzResearch.WordTrace]
  refine ⟨238803187060906350227752445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159202124707270900151834963 238803187060906350227752445)
  ·
    refine ⟨89551195147839881335407167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238803187060906350227752445 89551195147839881335407167)
    ·
      refine ⟨134326792721759822003110751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89551195147839881335407167 134326792721759822003110751)
      ·
        refine ⟨201490189082639733004666127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134326792721759822003110751 201490189082639733004666127)
        ·
          refine ⟨302235283623959599506999191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201490189082639733004666127 302235283623959599506999191)
          ·
            refine ⟨453352925435939399260498787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302235283623959599506999191 453352925435939399260498787)
            ·
              refine ⟨680029388153909098890748181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453352925435939399260498787 680029388153909098890748181)
              ·
                refine ⟨31876377569714489010503821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 680029388153909098890748181 31876377569714489010503821)
                ·
                  refine ⟨11953641588642933378938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31876377569714489010503821 11953641588642933378938933)
                  ·
                    refine ⟨1120653898935275004275525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11953641588642933378938933 1120653898935275004275525)
                    ·
                      rfl

theorem cell23_6547397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_6547397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547397 prefixEnd_6547397 := by exact prefixLift 6547397
  have htrace : WordTrace (prefixWord ++ tailWord_6547397) baseStart_6547397 baseEnd_6547397 := by
    simpa [prefixWord, tailWord_6547397, baseEnd_6547397] using wordTrace_append hprefix tailTrace_6547397
  have hstable : (prefixWord ++ tailWord_6547397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547397).length < 2 ^ (prefixWord ++ tailWord_6547397).sum := by decide
  have hdescent : baseEnd_6547397 < baseStart_6547397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547438 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_6547438 : Nat := 118140960795 + 6547438 * 2 ^ 59
def prefixEnd_6547438 : Nat := 4983230072969 + 3 ^ 40 * 6547438 * 2
def baseEnd_6547438 : Nat := 3361982749512659352413887

theorem tailTrace_6547438 : CollatzResearch.WordTrace tailWord_6547438 prefixEnd_6547438 3361982749512659352413887 := by
  unfold tailWord_6547438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850585306719726778749371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159203121635838542819996645 29850585306719726778749371)
  ·
    refine ⟨44775877960079590168124057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850585306719726778749371 44775877960079590168124057)
    ·
      refine ⟨33581908470059692626093043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44775877960079590168124057 33581908470059692626093043)
      ·
        refine ⟨50372862705089538939139565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33581908470059692626093043 50372862705089538939139565)
        ·
          refine ⟨18889823514408577102177337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50372862705089538939139565 18889823514408577102177337)
          ·
            refine ⟨14167367635806432826633003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18889823514408577102177337 14167367635806432826633003)
            ·
              refine ⟨21251051453709649239949505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167367635806432826633003 21251051453709649239949505)
              ·
                refine ⟨15938288590282236929962129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21251051453709649239949505 15938288590282236929962129)
                ·
                  refine ⟨11953716442711677697471597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15938288590282236929962129 11953716442711677697471597)
                  ·
                    refine ⟨4482643666016879136551849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11953716442711677697471597 4482643666016879136551849)
                    ·
                      refine ⟨3361982749512659352413887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482643666016879136551849 3361982749512659352413887)
                      ·
                        rfl

theorem cell23_6547438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_6547438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547438 prefixEnd_6547438 := by exact prefixLift 6547438
  have htrace : WordTrace (prefixWord ++ tailWord_6547438) baseStart_6547438 baseEnd_6547438 := by
    simpa [prefixWord, tailWord_6547438, baseEnd_6547438] using wordTrace_append hprefix tailTrace_6547438
  have hstable : (prefixWord ++ tailWord_6547438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547438).length < 2 ^ (prefixWord ++ tailWord_6547438).sum := by decide
  have hdescent : baseEnd_6547438 < baseStart_6547438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547461 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_6547461 : Nat := 118140960795 + 6547461 * 2 ^ 59
def prefixEnd_6547461 : Nat := 4983230072969 + 3 ^ 40 * 6547461 * 2
def baseEnd_6547461 : Nat := 1120664853189237587475427

theorem tailTrace_6547461 : CollatzResearch.WordTrace tailWord_6547461 prefixEnd_6547461 1120664853189237587475427 := by
  unfold tailWord_6547461
  simp only [CollatzResearch.WordTrace]
  refine ⟨238805521332674489158082237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159203680888449659438721491 238805521332674489158082237)
  ·
    refine ⟨89552070499752933434280839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238805521332674489158082237 89552070499752933434280839)
    ·
      refine ⟨134328105749629400151421259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89552070499752933434280839 134328105749629400151421259)
      ·
        refine ⟨201492158624444100227131889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134328105749629400151421259 201492158624444100227131889)
        ·
          refine ⟨151119118968333075170348917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201492158624444100227131889 151119118968333075170348917)
          ·
            refine ⟨14167417403281225797220211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151119118968333075170348917 14167417403281225797220211)
            ·
              refine ⟨21251126104921838695830317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167417403281225797220211 21251126104921838695830317)
              ·
                refine ⟨7969172289345689510936369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21251126104921838695830317 7969172289345689510936369)
                ·
                  refine ⟨5976879217009267133202277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969172289345689510936369 5976879217009267133202277)
                  ·
                    refine ⟨1120664853189237587475427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976879217009267133202277 1120664853189237587475427)
                    ·
                      rfl

theorem cell23_6547461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_6547461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547461 prefixEnd_6547461 := by exact prefixLift 6547461
  have htrace : WordTrace (prefixWord ++ tailWord_6547461) baseStart_6547461 baseEnd_6547461 := by
    simpa [prefixWord, tailWord_6547461, baseEnd_6547461] using wordTrace_append hprefix tailTrace_6547461
  have hstable : (prefixWord ++ tailWord_6547461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547461).length < 2 ^ (prefixWord ++ tailWord_6547461).sum := by decide
  have hdescent : baseEnd_6547461 < baseStart_6547461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547464 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_6547464 : Nat := 118140960795 + 6547464 * 2 ^ 59
def prefixEnd_6547464 : Nat := 4983230072969 + 3 ^ 40 * 6547464 * 2
def baseEnd_6547464 : Nat := 3361996100009676250688767

theorem tailTrace_6547464 : CollatzResearch.WordTrace tailWord_6547464 prefixEnd_6547464 3361996100009676250688767 := by
  unfold tailWord_6547464
  simp only [CollatzResearch.WordTrace]
  refine ⟨119402815375831810335220723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159203753834442413780294297 119402815375831810335220723)
  ·
    refine ⟨179104223063747715502831085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119402815375831810335220723 179104223063747715502831085)
    ·
      refine ⟨67164083648905393313561657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179104223063747715502831085 67164083648905393313561657)
      ·
        refine ⟨50373062736679044985171243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67164083648905393313561657 50373062736679044985171243)
        ·
          refine ⟨75559594105018567477756865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50373062736679044985171243 75559594105018567477756865)
          ·
            refine ⟨56669695578763925608317649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75559594105018567477756865 56669695578763925608317649)
            ·
              refine ⟨42502271684072944206238237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56669695578763925608317649 42502271684072944206238237)
              ·
                refine ⟨15938351881527354077339339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42502271684072944206238237 15938351881527354077339339)
                ·
                  refine ⟨23907527822291031116009009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15938351881527354077339339 23907527822291031116009009)
                  ·
                    refine ⟨17930645866718273337006757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23907527822291031116009009 17930645866718273337006757)
                    ·
                      refine ⟨3361996100009676250688767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17930645866718273337006757 3361996100009676250688767)
                      ·
                        rfl

theorem cell23_6547464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_6547464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547464 prefixEnd_6547464 := by exact prefixLift 6547464
  have htrace : WordTrace (prefixWord ++ tailWord_6547464) baseStart_6547464 baseEnd_6547464 := by
    simpa [prefixWord, tailWord_6547464, baseEnd_6547464] using wordTrace_append hprefix tailTrace_6547464
  have hstable : (prefixWord ++ tailWord_6547464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547464).length < 2 ^ (prefixWord ++ tailWord_6547464).sum := by decide
  have hdescent : baseEnd_6547464 < baseStart_6547464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547495 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6547495 : Nat := 118140960795 + 6547495 * 2 ^ 59
def prefixEnd_6547495 : Nat := 4983230072969 + 3 ^ 40 * 6547495 * 2
def baseEnd_6547495 : Nat := 1120670672636655209800375

theorem tailTrace_6547495 : CollatzResearch.WordTrace tailWord_6547495 prefixEnd_6547495 1120670672636655209800375 := by
  unfold tailWord_6547495
  simp only [CollatzResearch.WordTrace]
  refine ⟨238806761414551312964819939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159204507609700875309879959 238806761414551312964819939)
  ·
    refine ⟨358210142121826969447229909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238806761414551312964819939 358210142121826969447229909)
    ·
      refine ⟨8395550205980319596419451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 358210142121826969447229909 8395550205980319596419451)
      ·
        refine ⟨12593325308970479394629177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395550205980319596419451 12593325308970479394629177)
        ·
          refine ⟨9444993981727859545971883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593325308970479394629177 9444993981727859545971883)
          ·
            refine ⟨14167490972591789318957825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444993981727859545971883 14167490972591789318957825)
            ·
              refine ⟨10625618229443841989218369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14167490972591789318957825 10625618229443841989218369)
              ·
                refine ⟨7969213672082881491913777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10625618229443841989218369 7969213672082881491913777)
                ·
                  refine ⟨5976910254062161118935333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969213672082881491913777 5976910254062161118935333)
                  ·
                    refine ⟨1120670672636655209800375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5976910254062161118935333 1120670672636655209800375)
                    ·
                      rfl

theorem cell23_6547495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6547495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547495 prefixEnd_6547495 := by exact prefixLift 6547495
  have htrace : WordTrace (prefixWord ++ tailWord_6547495) baseStart_6547495 baseEnd_6547495 := by
    simpa [prefixWord, tailWord_6547495, baseEnd_6547495] using wordTrace_append hprefix tailTrace_6547495
  have hstable : (prefixWord ++ tailWord_6547495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547495).length < 2 ^ (prefixWord ++ tailWord_6547495).sum := by decide
  have hdescent : baseEnd_6547495 < baseStart_6547495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547496 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6547496 : Nat := 118140960795 + 6547496 * 2 ^ 59
def prefixEnd_6547496 : Nat := 4983230072969 + 3 ^ 40 * 6547496 * 2
def baseEnd_6547496 : Nat := 3362012531390620125488621

theorem tailTrace_6547496 : CollatzResearch.WordTrace tailWord_6547496 prefixEnd_6547496 3362012531390620125488621 := by
  unfold tailWord_6547496
  simp only [CollatzResearch.WordTrace]
  refine ⟨119403398943773845067803171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159204531925031793423737561 119403398943773845067803171)
  ·
    refine ⟨179105098415660767601704757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119403398943773845067803171 179105098415660767601704757)
    ·
      refine ⟨16791102976468196962659821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179105098415660767601704757 16791102976468196962659821)
      ·
        refine ⟨6296663616175573860997433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16791102976468196962659821 6296663616175573860997433)
        ·
          refine ⟨4722497712131680395748075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296663616175573860997433 4722497712131680395748075)
          ·
            refine ⟨7083746568197520593622113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722497712131680395748075 7083746568197520593622113)
            ·
              refine ⟨5312809926148140445216585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083746568197520593622113 5312809926148140445216585)
              ·
                refine ⟨3984607444611105333912439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312809926148140445216585 3984607444611105333912439)
                ·
                  refine ⟨5976911166916658000868659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984607444611105333912439 5976911166916658000868659)
                  ·
                    refine ⟨8965366750374987001302989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5976911166916658000868659 8965366750374987001302989)
                    ·
                      refine ⟨3362012531390620125488621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8965366750374987001302989 3362012531390620125488621)
                      ·
                        rfl

theorem cell23_6547496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6547496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547496 prefixEnd_6547496 := by exact prefixLift 6547496
  have htrace : WordTrace (prefixWord ++ tailWord_6547496) baseStart_6547496 baseEnd_6547496 := by
    simpa [prefixWord, tailWord_6547496, baseEnd_6547496] using wordTrace_append hprefix tailTrace_6547496
  have hstable : (prefixWord ++ tailWord_6547496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547496).length < 2 ^ (prefixWord ++ tailWord_6547496).sum := by decide
  have hdescent : baseEnd_6547496 < baseStart_6547496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547497 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_6547497 : Nat := 118140960795 + 6547497 * 2 ^ 59
def prefixEnd_6547497 : Nat := 4983230072969 + 3 ^ 40 * 6547497 * 2
def baseEnd_6547497 : Nat := 3362013044871274621576115

theorem tailTrace_6547497 : CollatzResearch.WordTrace tailWord_6547497 prefixEnd_6547497 3362013044871274621576115 := by
  unfold tailWord_6547497
  simp only [CollatzResearch.WordTrace]
  refine ⟨238806834360544067306392745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159204556240362711537595163 238806834360544067306392745)
  ·
    refine ⟨179105125770408050479794559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238806834360544067306392745 179105125770408050479794559)
    ·
      refine ⟨268657688655612075719691839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179105125770408050479794559 268657688655612075719691839)
      ·
        refine ⟨402986532983418113579537759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268657688655612075719691839 402986532983418113579537759)
        ·
          refine ⟨604479799475127170369306639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402986532983418113579537759 604479799475127170369306639)
          ·
            refine ⟨906719699212690755553959959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604479799475127170369306639 906719699212690755553959959)
            ·
              refine ⟨1360079548819036133330939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906719699212690755553959959 1360079548819036133330939939)
              ·
                refine ⟨2040119323228554199996409909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360079548819036133330939939 2040119323228554199996409909)
                ·
                  refine ⟨191261186552676956249663429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040119323228554199996409909 191261186552676956249663429)
                  ·
                    refine ⟨35861472478626929296811893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191261186552676956249663429 35861472478626929296811893)
                    ·
                      refine ⟨3362013044871274621576115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35861472478626929296811893 3362013044871274621576115)
                      ·
                        rfl

theorem cell23_6547497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_6547497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547497 prefixEnd_6547497 := by exact prefixLift 6547497
  have htrace : WordTrace (prefixWord ++ tailWord_6547497) baseStart_6547497 baseEnd_6547497 := by
    simpa [prefixWord, tailWord_6547497, baseEnd_6547497] using wordTrace_append hprefix tailTrace_6547497
  have hstable : (prefixWord ++ tailWord_6547497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547497).length < 2 ^ (prefixWord ++ tailWord_6547497).sum := by decide
  have hdescent : baseEnd_6547497 < baseStart_6547497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547502 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6547502 : Nat := 118140960795 + 6547502 * 2 ^ 59
def prefixEnd_6547502 : Nat := 4983230072969 + 3 ^ 40 * 6547502 * 2
def baseEnd_6547502 : Nat := 3362015612274547102013593

theorem tailTrace_6547502 : CollatzResearch.WordTrace tailWord_6547502 prefixEnd_6547502 3362015612274547102013593 := by
  unfold tailWord_6547502
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850877090690744145040595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159204677817017302106883173 29850877090690744145040595)
  ·
    refine ⟨44776315636036116217560893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29850877090690744145040595 44776315636036116217560893)
    ·
      refine ⟨16791118363513543581585335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44776315636036116217560893 16791118363513543581585335)
      ·
        refine ⟨25186677545270315372378003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791118363513543581585335 25186677545270315372378003)
        ·
          refine ⟨37780016317905473058567005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25186677545270315372378003 37780016317905473058567005)
          ·
            refine ⟨14167506119214552396962627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37780016317905473058567005 14167506119214552396962627)
            ·
              refine ⟨21251259178821828595443941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167506119214552396962627 21251259178821828595443941)
              ·
                refine ⟨3984611096029092861645739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21251259178821828595443941 3984611096029092861645739)
                ·
                  refine ⟨5976916644043639292468609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984611096029092861645739 5976916644043639292468609)
                  ·
                    refine ⟨4482687483032729469351457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976916644043639292468609 4482687483032729469351457)
                    ·
                      refine ⟨3362015612274547102013593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482687483032729469351457 3362015612274547102013593)
                      ·
                        rfl

theorem cell23_6547502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6547502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547502 prefixEnd_6547502 := by exact prefixLift 6547502
  have htrace : WordTrace (prefixWord ++ tailWord_6547502) baseStart_6547502 baseEnd_6547502 := by
    simpa [prefixWord, tailWord_6547502, baseEnd_6547502] using wordTrace_append hprefix tailTrace_6547502
  have hstable : (prefixWord ++ tailWord_6547502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547502).length < 2 ^ (prefixWord ++ tailWord_6547502).sum := by decide
  have hdescent : baseEnd_6547502 < baseStart_6547502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547508 : List Nat := [2, 5, 1, 2, 2, 2, 1, 8]
def baseStart_6547508 : Nat := 118140960795 + 6547508 * 2 ^ 59
def prefixEnd_6547508 : Nat := 4983230072969 + 3 ^ 40 * 6547508 * 2
def baseEnd_6547508 : Nat := 124519210857721262168095

theorem tailTrace_6547508 : CollatzResearch.WordTrace tailWord_6547508 prefixEnd_6547508 124519210857721262168095 := by
  unfold tailWord_6547508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119403617781752108092521589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159204823709002810790028785 119403617781752108092521589)
  ·
    refine ⟨11194089167039260133673899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119403617781752108092521589 11194089167039260133673899)
    ·
      refine ⟨16791133750558890200510849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194089167039260133673899 16791133750558890200510849)
      ·
        refine ⟨12593350312919167650383137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16791133750558890200510849 12593350312919167650383137)
        ·
          refine ⟨9445012734689375737787353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593350312919167650383137 9445012734689375737787353)
          ·
            refine ⟨7083759551017031803340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9445012734689375737787353 7083759551017031803340515)
            ·
              refine ⟨10625639326525547705010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083759551017031803340515 10625639326525547705010773)
              ·
                refine ⟨124519210857721262168095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10625639326525547705010773 124519210857721262168095)
                ·
                  rfl

theorem cell23_6547508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 8].length) (baseStart_6547508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547508 prefixEnd_6547508 := by exact prefixLift 6547508
  have htrace : WordTrace (prefixWord ++ tailWord_6547508) baseStart_6547508 baseEnd_6547508 := by
    simpa [prefixWord, tailWord_6547508, baseEnd_6547508] using wordTrace_append hprefix tailTrace_6547508
  have hstable : (prefixWord ++ tailWord_6547508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547508).length < 2 ^ (prefixWord ++ tailWord_6547508).sum := by decide
  have hdescent : baseEnd_6547508 < baseStart_6547508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547511 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_6547511 : Nat := 118140960795 + 6547511 * 2 ^ 59
def prefixEnd_6547511 : Nat := 4983230072969 + 3 ^ 40 * 6547511 * 2
def baseEnd_6547511 : Nat := 3362020233600437566801051

theorem tailTrace_6547511 : CollatzResearch.WordTrace tailWord_6547511 prefixEnd_6547511 3362020233600437566801051 := by
  unfold tailWord_6547511
  simp only [CollatzResearch.WordTrace]
  refine ⟨238807344982493347697402387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159204896654995565131601591 238807344982493347697402387)
  ·
    refine ⟨358211017473740021546103581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238807344982493347697402387 358211017473740021546103581)
    ·
      refine ⟨134329131552652508079788843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358211017473740021546103581 134329131552652508079788843)
      ·
        refine ⟨201493697328978762119683265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134329131552652508079788843 201493697328978762119683265)
        ·
          refine ⟨151120272996734071589762449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201493697328978762119683265 151120272996734071589762449)
          ·
            refine ⟨113340204747550553692321837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151120272996734071589762449 113340204747550553692321837)
            ·
              refine ⟨42502576780331457634620689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113340204747550553692321837 42502576780331457634620689)
              ·
                refine ⟨31876932585248593225965517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42502576780331457634620689 31876932585248593225965517)
                ·
                  refine ⟨11953849719468222459737069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31876932585248593225965517 11953849719468222459737069)
                  ·
                    refine ⟨4482693644800583422401401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11953849719468222459737069 4482693644800583422401401)
                    ·
                      refine ⟨3362020233600437566801051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482693644800583422401401 3362020233600437566801051)
                      ·
                        rfl

theorem cell23_6547511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_6547511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547511 prefixEnd_6547511 := by exact prefixLift 6547511
  have htrace : WordTrace (prefixWord ++ tailWord_6547511) baseStart_6547511 baseEnd_6547511 := by
    simpa [prefixWord, tailWord_6547511, baseEnd_6547511] using wordTrace_append hprefix tailTrace_6547511
  have hstable : (prefixWord ++ tailWord_6547511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547511).length < 2 ^ (prefixWord ++ tailWord_6547511).sum := by decide
  have hdescent : baseEnd_6547511 < baseStart_6547511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547564 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 7]
def baseStart_6547564 : Nat := 118140960795 + 6547564 * 2 ^ 59
def prefixEnd_6547564 : Nat := 4983230072969 + 3 ^ 40 * 6547564 * 2
def baseEnd_6547564 : Nat := 373560827563902873270923

theorem tailTrace_6547564 : CollatzResearch.WordTrace tailWord_6547564 prefixEnd_6547564 373560827563902873270923 := by
  unfold tailWord_6547564
  simp only [CollatzResearch.WordTrace]
  refine ⟨119404639025650668874540873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159206185367534225166054497 119404639025650668874540873)
  ·
    refine ⟨89553479269238001655905655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119404639025650668874540873 89553479269238001655905655)
    ·
      refine ⟨134330218903857002483858483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89553479269238001655905655 134330218903857002483858483)
      ·
        refine ⟨201495328355785503725787725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134330218903857002483858483 201495328355785503725787725)
        ·
          refine ⟨75560748133419563897170397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201495328355785503725787725 75560748133419563897170397)
          ·
            refine ⟨28335280550032336461438899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75560748133419563897170397 28335280550032336461438899)
            ·
              refine ⟨42502920825048504692158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28335280550032336461438899 42502920825048504692158349)
              ·
                refine ⟨15938595309393189259559381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42502920825048504692158349 15938595309393189259559381)
                ·
                  refine ⟨373560827563902873270923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15938595309393189259559381 373560827563902873270923)
                  ·
                    rfl

theorem cell23_6547564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_6547564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547564 prefixEnd_6547564 := by exact prefixLift 6547564
  have htrace : WordTrace (prefixWord ++ tailWord_6547564) baseStart_6547564 baseEnd_6547564 := by
    simpa [prefixWord, tailWord_6547564, baseEnd_6547564] using wordTrace_append hprefix tailTrace_6547564
  have hstable : (prefixWord ++ tailWord_6547564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547564).length < 2 ^ (prefixWord ++ tailWord_6547564).sum := by decide
  have hdescent : baseEnd_6547564 < baseStart_6547564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547615 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 5]
def baseStart_6547615 : Nat := 118140960795 + 6547615 * 2 ^ 59
def prefixEnd_6547615 : Nat := 4983230072969 + 3 ^ 40 * 6547615 * 2
def baseEnd_6547615 : Nat := 373563737287611684433397

theorem tailTrace_6547615 : CollatzResearch.WordTrace tailWord_6547615 prefixEnd_6547615 373563737287611684433397 := by
  unfold tailWord_6547615
  simp only [CollatzResearch.WordTrace]
  refine ⟨238811138174116573459188299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159207425449411048972792199 238811138174116573459188299)
  ·
    refine ⟨358216707261174860188782449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238811138174116573459188299 358216707261174860188782449)
    ·
      refine ⟨268662530445881145141586837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358216707261174860188782449 268662530445881145141586837)
      ·
        refine ⟨12593556114650678678511883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 268662530445881145141586837 12593556114650678678511883)
        ·
          refine ⟨18890334171976018017767825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593556114650678678511883 18890334171976018017767825)
          ·
            refine ⟨14167750628982013513325869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18890334171976018017767825 14167750628982013513325869)
            ·
              refine ⟨5312906485868255067497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14167750628982013513325869 5312906485868255067497201)
              ·
                refine ⟨3984679864401191300622901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312906485868255067497201 3984679864401191300622901)
                ·
                  refine ⟨373563737287611684433397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3984679864401191300622901 373563737287611684433397)
                  ·
                    rfl

theorem cell23_6547615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 5].length) (baseStart_6547615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547615 prefixEnd_6547615 := by exact prefixLift 6547615
  have htrace : WordTrace (prefixWord ++ tailWord_6547615) baseStart_6547615 baseEnd_6547615 := by
    simpa [prefixWord, tailWord_6547615, baseEnd_6547615] using wordTrace_append hprefix tailTrace_6547615
  have hstable : (prefixWord ++ tailWord_6547615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547615).length < 2 ^ (prefixWord ++ tailWord_6547615).sum := by decide
  have hdescent : baseEnd_6547615 < baseStart_6547615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547626 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6547626 : Nat := 118140960795 + 6547626 * 2 ^ 59
def prefixEnd_6547626 : Nat := 4983230072969 + 3 ^ 40 * 6547626 * 2
def baseEnd_6547626 : Nat := 3362079283875704616863023

theorem tailTrace_6547626 : CollatzResearch.WordTrace tailWord_6547626 prefixEnd_6547626 3362079283875704616863023 := by
  unfold tailWord_6547626
  simp only [CollatzResearch.WordTrace]
  refine ⟨59702884844269180584459683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159207692918051148225225821 59702884844269180584459683)
  ·
    refine ⟨89554327266403770876689525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59702884844269180584459683 89554327266403770876689525)
    ·
      refine ⟨8395718181225353519689643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89554327266403770876689525 8395718181225353519689643)
      ·
        refine ⟨12593577271838030279534465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395718181225353519689643 12593577271838030279534465)
        ·
          refine ⟨9445182953878522709650849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12593577271838030279534465 9445182953878522709650849)
          ·
            refine ⟨7083887215408892032238137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9445182953878522709650849 7083887215408892032238137)
            ·
              refine ⟨5312915411556669024178603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083887215408892032238137 5312915411556669024178603)
              ·
                refine ⟨7969373117335003536267905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312915411556669024178603 7969373117335003536267905)
                ·
                  refine ⟨5977029838001252652200929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969373117335003536267905 5977029838001252652200929)
                  ·
                    refine ⟨4482772378500939489150697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5977029838001252652200929 4482772378500939489150697)
                    ·
                      refine ⟨3362079283875704616863023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482772378500939489150697 3362079283875704616863023)
                      ·
                        rfl

theorem cell23_6547626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6547626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547626 prefixEnd_6547626 := by exact prefixLift 6547626
  have htrace : WordTrace (prefixWord ++ tailWord_6547626) baseStart_6547626 baseEnd_6547626 := by
    simpa [prefixWord, tailWord_6547626, baseEnd_6547626] using wordTrace_append hprefix tailTrace_6547626
  have hstable : (prefixWord ++ tailWord_6547626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547626).length < 2 ^ (prefixWord ++ tailWord_6547626).sum := by decide
  have hdescent : baseEnd_6547626 < baseStart_6547626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547631 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 6, 2]
def baseStart_6547631 : Nat := 118140960795 + 6547631 * 2 ^ 59
def prefixEnd_6547631 : Nat := 4983230072969 + 3 ^ 40 * 6547631 * 2
def baseEnd_6547631 : Nat := 3362081851278977097300499

theorem tailTrace_6547631 : CollatzResearch.WordTrace tailWord_6547631 prefixEnd_6547631 3362081851278977097300499 := by
  unfold tailWord_6547631
  simp only [CollatzResearch.WordTrace]
  refine ⟨238811721742058608191770747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159207814494705738794513831 238811721742058608191770747)
  ·
    refine ⟨358217582613087912287656121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238811721742058608191770747 358217582613087912287656121)
    ·
      refine ⟨268663186959815934215742091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358217582613087912287656121 268663186959815934215742091)
      ·
        refine ⟨402994780439723901323613137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268663186959815934215742091 402994780439723901323613137)
        ·
          refine ⟨302246085329792925992709853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402994780439723901323613137 302246085329792925992709853)
          ·
            refine ⟨113342281998672347247266195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302246085329792925992709853 113342281998672347247266195)
            ·
              refine ⟨170013422998008520870899293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113342281998672347247266195 170013422998008520870899293)
              ·
                refine ⟨63755033624253195326587235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170013422998008520870899293 63755033624253195326587235)
                ·
                  refine ⟨95632550436379792989880853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63755033624253195326587235 95632550436379792989880853)
                  ·
                    refine ⟨4482775801705302796400665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95632550436379792989880853 4482775801705302796400665)
                    ·
                      refine ⟨3362081851278977097300499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482775801705302796400665 3362081851278977097300499)
                      ·
                        rfl

theorem cell23_6547631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6, 2].length) (baseStart_6547631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547631 prefixEnd_6547631 := by exact prefixLift 6547631
  have htrace : WordTrace (prefixWord ++ tailWord_6547631) baseStart_6547631 baseEnd_6547631 := by
    simpa [prefixWord, tailWord_6547631, baseEnd_6547631] using wordTrace_append hprefix tailTrace_6547631
  have hstable : (prefixWord ++ tailWord_6547631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547631).length < 2 ^ (prefixWord ++ tailWord_6547631).sum := by decide
  have hdescent : baseEnd_6547631 < baseStart_6547631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547641 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_6547641 : Nat := 118140960795 + 6547641 * 2 ^ 59
def prefixEnd_6547641 : Nat := 4983230072969 + 3 ^ 40 * 6547641 * 2
def baseEnd_6547641 : Nat := 1120695662028507352725151

theorem tailTrace_6547641 : CollatzResearch.WordTrace tailWord_6547641 prefixEnd_6547641 1120695662028507352725151 := by
  unfold tailWord_6547641
  simp only [CollatzResearch.WordTrace]
  refine ⟨238812086472022379899634777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159208057648014919933089851 238812086472022379899634777)
  ·
    refine ⟨179109064854016784924726083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238812086472022379899634777 179109064854016784924726083)
    ·
      refine ⟨268663597281025177387089125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179109064854016784924726083 268663597281025177387089125)
      ·
        refine ⟨50374424490192220760079211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268663597281025177387089125 50374424490192220760079211)
        ·
          refine ⟨75561636735288331140118817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50374424490192220760079211 75561636735288331140118817)
          ·
            refine ⟨56671227551466248355089113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75561636735288331140118817 56671227551466248355089113)
            ·
              refine ⟨42503420663599686266316835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56671227551466248355089113 42503420663599686266316835)
              ·
                refine ⟨63755130995399529399475253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42503420663599686266316835 63755130995399529399475253)
                ·
                  refine ⟨5977043530818705881200805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63755130995399529399475253 5977043530818705881200805)
                  ·
                    refine ⟨1120695662028507352725151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5977043530818705881200805 1120695662028507352725151)
                    ·
                      rfl

theorem cell23_6547641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_6547641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547641 prefixEnd_6547641 := by exact prefixLift 6547641
  have htrace : WordTrace (prefixWord ++ tailWord_6547641) baseStart_6547641 baseEnd_6547641 := by
    simpa [prefixWord, tailWord_6547641, baseEnd_6547641] using wordTrace_append hprefix tailTrace_6547641
  have hstable : (prefixWord ++ tailWord_6547641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547641).length < 2 ^ (prefixWord ++ tailWord_6547641).sum := by decide
  have hdescent : baseEnd_6547641 < baseStart_6547641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547648 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_6547648 : Nat := 118140960795 + 6547648 * 2 ^ 59
def prefixEnd_6547648 : Nat := 4983230072969 + 3 ^ 40 * 6547648 * 2
def baseEnd_6547648 : Nat := 3362090580450103530787921

theorem tailTrace_6547648 : CollatzResearch.WordTrace tailWord_6547648 prefixEnd_6547648 3362090580450103530787921 := by
  unfold tailWord_6547648
  simp only [CollatzResearch.WordTrace]
  refine ⟨119406170891498510047569799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159208227855331346730093065 119406170891498510047569799)
  ·
    refine ⟨179109256337247765071354699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119406170891498510047569799 179109256337247765071354699)
    ·
      refine ⟨268663884505871647607032049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179109256337247765071354699 268663884505871647607032049)
      ·
        refine ⟨201497913379403735705274037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268663884505871647607032049 201497913379403735705274037)
        ·
          refine ⟨18890429379319100222369441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201497913379403735705274037 18890429379319100222369441)
          ·
            refine ⟨14167822034489325166777081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18890429379319100222369441 14167822034489325166777081)
            ·
              refine ⟨10625866525866993875082811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14167822034489325166777081 10625866525866993875082811)
              ·
                refine ⟨15938799788800490812624217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10625866525866993875082811 15938799788800490812624217)
                ·
                  refine ⟨11954099841600368109468163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15938799788800490812624217 11954099841600368109468163)
                  ·
                    refine ⟨17931149762400552164202245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11954099841600368109468163 17931149762400552164202245)
                    ·
                      refine ⟨3362090580450103530787921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17931149762400552164202245 3362090580450103530787921)
                      ·
                        rfl

theorem cell23_6547648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_6547648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547648 prefixEnd_6547648 := by exact prefixLift 6547648
  have htrace : WordTrace (prefixWord ++ tailWord_6547648) baseStart_6547648 baseEnd_6547648 := by
    simpa [prefixWord, tailWord_6547648, baseEnd_6547648] using wordTrace_append hprefix tailTrace_6547648
  have hstable : (prefixWord ++ tailWord_6547648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547648).length < 2 ^ (prefixWord ++ tailWord_6547648).sum := by decide
  have hdescent : baseEnd_6547648 < baseStart_6547648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547742 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6547742 : Nat := 118140960795 + 6547742 * 2 ^ 59
def prefixEnd_6547742 : Nat := 4983230072969 + 3 ^ 40 * 6547742 * 2
def baseEnd_6547742 : Nat := 3362138847631626163012489

theorem tailTrace_6547742 : CollatzResearch.WordTrace tailWord_6547742 prefixEnd_6547742 3362138847631626163012489 := by
  unfold tailWord_6547742
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851971280582059268632685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159210513496437649432707653 29851971280582059268632685)
  ·
    refine ⟨11194489230218272225737257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29851971280582059268632685 11194489230218272225737257)
    ·
      refine ⟨8395866922663704169302943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11194489230218272225737257 8395866922663704169302943)
      ·
        refine ⟨12593800383995556253954415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395866922663704169302943 12593800383995556253954415)
        ·
          refine ⟨18890700575993334380931623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593800383995556253954415 18890700575993334380931623)
          ·
            refine ⟨28336050863990001571397435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18890700575993334380931623 28336050863990001571397435)
            ·
              refine ⟨42504076295985002357096153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28336050863990001571397435 42504076295985002357096153)
              ·
                refine ⟨31878057221988751767822115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42504076295985002357096153 31878057221988751767822115)
                ·
                  refine ⟨47817085832983127651733173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31878057221988751767822115 47817085832983127651733173)
                  ·
                    refine ⟨4482851796842168217349985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47817085832983127651733173 4482851796842168217349985)
                    ·
                      refine ⟨3362138847631626163012489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4482851796842168217349985 3362138847631626163012489)
                      ·
                        rfl

theorem cell23_6547742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6547742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547742 prefixEnd_6547742 := by exact prefixLift 6547742
  have htrace : WordTrace (prefixWord ++ tailWord_6547742) baseStart_6547742 baseEnd_6547742 := by
    simpa [prefixWord, tailWord_6547742, baseEnd_6547742] using wordTrace_append hprefix tailTrace_6547742
  have hstable : (prefixWord ++ tailWord_6547742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547742).length < 2 ^ (prefixWord ++ tailWord_6547742).sum := by decide
  have hdescent : baseEnd_6547742 < baseStart_6547742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547748 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_6547748 : Nat := 118140960795 + 6547748 * 2 ^ 59
def prefixEnd_6547748 : Nat := 4983230072969 + 3 ^ 40 * 6547748 * 2
def baseEnd_6547748 : Nat := 1120713976171851046512487

theorem tailTrace_6547748 : CollatzResearch.WordTrace tailWord_6547748 prefixEnd_6547748 1120713976171851046512487 := by
  unfold tailWord_6547748
  simp only [CollatzResearch.WordTrace]
  refine ⟨119407994541317368586889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159210659388423158115853265 119407994541317368586889949)
  ·
    refine ⟨44777997952994013220083731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119407994541317368586889949 44777997952994013220083731)
    ·
      refine ⟨67166996929491019830125597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44777997952994013220083731 67166996929491019830125597)
      ·
        refine ⟨25187623848559132436297099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67166996929491019830125597 25187623848559132436297099)
        ·
          refine ⟨37781435772838698654445649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25187623848559132436297099 37781435772838698654445649)
          ·
            refine ⟨28336076829629023990834237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37781435772838698654445649 28336076829629023990834237)
            ·
              refine ⟨10626028811110883996562839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28336076829629023990834237 10626028811110883996562839)
              ·
                refine ⟨15939043216666325994844259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626028811110883996562839 15939043216666325994844259)
                ·
                  refine ⟨23908564824999488992266389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939043216666325994844259 23908564824999488992266389)
                  ·
                    refine ⟨1120713976171851046512487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23908564824999488992266389 1120713976171851046512487)
                    ·
                      rfl

theorem cell23_6547748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_6547748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547748 prefixEnd_6547748 := by exact prefixLift 6547748
  have htrace : WordTrace (prefixWord ++ tailWord_6547748) baseStart_6547748 baseEnd_6547748 := by
    simpa [prefixWord, tailWord_6547748, baseEnd_6547748] using wordTrace_append hprefix tailTrace_6547748
  have hstable : (prefixWord ++ tailWord_6547748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547748).length < 2 ^ (prefixWord ++ tailWord_6547748).sum := by decide
  have hdescent : baseEnd_6547748 < baseStart_6547748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547806 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6547806 : Nat := 118140960795 + 6547806 * 2 ^ 59
def prefixEnd_6547806 : Nat := 4983230072969 + 3 ^ 40 * 6547806 * 2
def baseEnd_6547806 : Nat := 3362171710393513912612195

theorem tailTrace_6547806 : CollatzResearch.WordTrace tailWord_6547806 prefixEnd_6547806 3362171710393513912612195 := by
  unfold tailWord_6547806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29852263064553076634923909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159212069677616408719594181 29852263064553076634923909)
  ·
    refine ⟨5597299324603701869048233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29852263064553076634923909 5597299324603701869048233)
    ·
      refine ⟨4197974493452776401786175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597299324603701869048233 4197974493452776401786175)
      ·
        refine ⟨6296961740179164602679263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197974493452776401786175 6296961740179164602679263)
        ·
          refine ⟨9445442610268746904018895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296961740179164602679263 9445442610268746904018895)
          ·
            refine ⟨14168163915403120356028343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445442610268746904018895 14168163915403120356028343)
            ·
              refine ⟨21252245873104680534042515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14168163915403120356028343 21252245873104680534042515)
              ·
                refine ⟨31878368809657020801063773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21252245873104680534042515 31878368809657020801063773)
                ·
                  refine ⟨11954388303621382800398915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31878368809657020801063773 11954388303621382800398915)
                  ·
                    refine ⟨17931582455432074200598373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11954388303621382800398915 17931582455432074200598373)
                    ·
                      refine ⟨3362171710393513912612195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17931582455432074200598373 3362171710393513912612195)
                      ·
                        rfl

theorem cell23_6547806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6547806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547806 prefixEnd_6547806 := by exact prefixLift 6547806
  have htrace : WordTrace (prefixWord ++ tailWord_6547806) baseStart_6547806 baseEnd_6547806 := by
    simpa [prefixWord, tailWord_6547806, baseEnd_6547806] using wordTrace_append hprefix tailTrace_6547806
  have hstable : (prefixWord ++ tailWord_6547806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547806).length < 2 ^ (prefixWord ++ tailWord_6547806).sum := by decide
  have hdescent : baseEnd_6547806 < baseStart_6547806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547831 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_6547831 : Nat := 118140960795 + 6547831 * 2 ^ 59
def prefixEnd_6547831 : Nat := 4983230072969 + 3 ^ 40 * 6547831 * 2
def baseEnd_6547831 : Nat := 3362184547409876314799579

theorem tailTrace_6547831 : CollatzResearch.WordTrace tailWord_6547831 prefixEnd_6547831 3362184547409876314799579 := by
  unfold tailWord_6547831
  simp only [CollatzResearch.WordTrace]
  refine ⟨238819016341334042349051347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159212677560889361566034231 238819016341334042349051347)
  ·
    refine ⟨358228524512001063523577021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238819016341334042349051347 358228524512001063523577021)
    ·
      refine ⟨134335696692000398821341383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358228524512001063523577021 134335696692000398821341383)
      ·
        refine ⟨201503545038000598232012075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134335696692000398821341383 201503545038000598232012075)
        ·
          refine ⟨302255317557000897348018113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201503545038000598232012075 302255317557000897348018113)
          ·
            refine ⟨226691488167750673011013585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302255317557000897348018113 226691488167750673011013585)
            ·
              refine ⟨170018616125813004758260189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226691488167750673011013585 170018616125813004758260189)
              ·
                refine ⟨63756981047179876784347571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170018616125813004758260189 63756981047179876784347571)
                ·
                  refine ⟨95635471570769815176521357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63756981047179876784347571 95635471570769815176521357)
                  ·
                    refine ⟨35863301839038680691195509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95635471570769815176521357 35863301839038680691195509)
                    ·
                      refine ⟨3362184547409876314799579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35863301839038680691195509 3362184547409876314799579)
                      ·
                        rfl

theorem cell23_6547831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_6547831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547831 prefixEnd_6547831 := by exact prefixLift 6547831
  have htrace : WordTrace (prefixWord ++ tailWord_6547831) baseStart_6547831 baseEnd_6547831 := by
    simpa [prefixWord, tailWord_6547831, baseEnd_6547831] using wordTrace_append hprefix tailTrace_6547831
  have hstable : (prefixWord ++ tailWord_6547831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547831).length < 2 ^ (prefixWord ++ tailWord_6547831).sum := by decide
  have hdescent : baseEnd_6547831 < baseStart_6547831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547848 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6547848 : Nat := 118140960795 + 6547848 * 2 ^ 59
def prefixEnd_6547848 : Nat := 4983230072969 + 3 ^ 40 * 6547848 * 2
def baseEnd_6547848 : Nat := 3362193276581002748287001

theorem tailTrace_6547848 : CollatzResearch.WordTrace tailWord_6547848 prefixEnd_6547848 3362193276581002748287001 := by
  unfold tailWord_6547848
  simp only [CollatzResearch.WordTrace]
  refine ⟨119409818191136227126210099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159213090921514969501613465 119409818191136227126210099)
  ·
    refine ⟨179114727286704340689315149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119409818191136227126210099 179114727286704340689315149)
    ·
      refine ⟨67168022732514127758493181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179114727286704340689315149 67168022732514127758493181)
      ·
        refine ⟨25188008524692797909434943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67168022732514127758493181 25188008524692797909434943)
        ·
          refine ⟨37782012787039196864152415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25188008524692797909434943 37782012787039196864152415)
          ·
            refine ⟨56673019180558795296228623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37782012787039196864152415 56673019180558795296228623)
            ·
              refine ⟨85009528770838192944342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56673019180558795296228623 85009528770838192944342935)
              ·
                refine ⟨127514293156257289416514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85009528770838192944342935 127514293156257289416514403)
                ·
                  refine ⟨191271439734385934124771605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127514293156257289416514403 191271439734385934124771605)
                  ·
                    refine ⟨8965848737549340662098669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191271439734385934124771605 8965848737549340662098669)
                    ·
                      refine ⟨3362193276581002748287001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8965848737549340662098669 3362193276581002748287001)
                      ·
                        rfl

theorem cell23_6547848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6547848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547848 prefixEnd_6547848 := by exact prefixLift 6547848
  have htrace : WordTrace (prefixWord ++ tailWord_6547848) baseStart_6547848 baseEnd_6547848 := by
    simpa [prefixWord, tailWord_6547848, baseEnd_6547848] using wordTrace_append hprefix tailTrace_6547848
  have hstable : (prefixWord ++ tailWord_6547848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547848).length < 2 ^ (prefixWord ++ tailWord_6547848).sum := by decide
  have hdescent : baseEnd_6547848 < baseStart_6547848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547898 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_6547898 : Nat := 118140960795 + 6547898 * 2 ^ 59
def prefixEnd_6547898 : Nat := 4983230072969 + 3 ^ 40 * 6547898 * 2
def baseEnd_6547898 : Nat := 1120739650204575850887257

theorem tailTrace_6547898 : CollatzResearch.WordTrace tailWord_6547898 prefixEnd_6547898 1120739650204575850887257 := by
  unfold tailWord_6547898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59705365008022828197935087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159214306688060875194493565 59705365008022828197935087)
  ·
    refine ⟨89558047512034242296902631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59705365008022828197935087 89558047512034242296902631)
    ·
      refine ⟨134337071268051363445353947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89558047512034242296902631 134337071268051363445353947)
      ·
        refine ⟨201505606902077045168030921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134337071268051363445353947 201505606902077045168030921)
        ·
          refine ⟨151129205176557783876023191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201505606902077045168030921 151129205176557783876023191)
          ·
            refine ⟨226693807764836675814034787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151129205176557783876023191 226693807764836675814034787)
            ·
              refine ⟨340040711647255013721052181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226693807764836675814034787 340040711647255013721052181)
              ·
                refine ⟨15939408358465078768174321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340040711647255013721052181 15939408358465078768174321)
                ·
                  refine ⟨11954556268848809076130741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15939408358465078768174321 11954556268848809076130741)
                  ·
                    refine ⟨1120739650204575850887257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11954556268848809076130741 1120739650204575850887257)
                    ·
                      rfl

theorem cell23_6547898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_6547898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547898 prefixEnd_6547898 := by exact prefixLift 6547898
  have htrace : WordTrace (prefixWord ++ tailWord_6547898) baseStart_6547898 baseEnd_6547898 := by
    simpa [prefixWord, tailWord_6547898, baseEnd_6547898] using wordTrace_append hprefix tailTrace_6547898
  have hstable : (prefixWord ++ tailWord_6547898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547898).length < 2 ^ (prefixWord ++ tailWord_6547898).sum := by decide
  have hdescent : baseEnd_6547898 < baseStart_6547898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6547955 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3]
def baseStart_6547955 : Nat := 118140960795 + 6547955 * 2 ^ 59
def prefixEnd_6547955 : Nat := 4983230072969 + 3 ^ 40 * 6547955 * 2
def baseEnd_6547955 : Nat := 3362248219011033829649009

theorem tailTrace_6547955 : CollatzResearch.WordTrace tailWord_6547955 prefixEnd_6547955 3362248219011033829649009 := by
  unfold tailWord_6547955
  simp only [CollatzResearch.WordTrace]
  refine ⟨238823538992884811526565319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159215692661923207684376879 238823538992884811526565319)
  ·
    refine ⟨358235308489327217289847979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238823538992884811526565319 358235308489327217289847979)
    ·
      refine ⟨537352962733990825934771969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358235308489327217289847979 537352962733990825934771969)
      ·
        refine ⟨403014722050493119451078977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537352962733990825934771969 403014722050493119451078977)
        ·
          refine ⟨302261041537869839588309233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403014722050493119451078977 302261041537869839588309233)
          ·
            refine ⟨226695781153402379691231925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302261041537869839588309233 226695781153402379691231925)
            ·
              refine ⟨21252729483131473096052993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226695781153402379691231925 21252729483131473096052993)
              ·
                refine ⟨15939547112348604822039745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21252729483131473096052993 15939547112348604822039745)
                ·
                  refine ⟨11954660334261453616529809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15939547112348604822039745 11954660334261453616529809)
                  ·
                    refine ⟨8965995250696090212397357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11954660334261453616529809 8965995250696090212397357)
                    ·
                      refine ⟨3362248219011033829649009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8965995250696090212397357 3362248219011033829649009)
                      ·
                        rfl

theorem cell23_6547955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_6547955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6547955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6547955 prefixEnd_6547955 := by exact prefixLift 6547955
  have htrace : WordTrace (prefixWord ++ tailWord_6547955) baseStart_6547955 baseEnd_6547955 := by
    simpa [prefixWord, tailWord_6547955, baseEnd_6547955] using wordTrace_append hprefix tailTrace_6547955
  have hstable : (prefixWord ++ tailWord_6547955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6547955).length < 2 ^ (prefixWord ++ tailWord_6547955).sum := by decide
  have hdescent : baseEnd_6547955 < baseStart_6547955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6547955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548005 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_6548005 : Nat := 118140960795 + 6548005 * 2 ^ 59
def prefixEnd_6548005 : Nat := 4983230072969 + 3 ^ 40 * 6548005 * 2
def baseEnd_6548005 : Nat := 1120757964347919544674593

theorem tailTrace_6548005 : CollatzResearch.WordTrace tailWord_6548005 prefixEnd_6548005 1120757964347919544674593 := by
  unfold tailWord_6548005
  simp only [CollatzResearch.WordTrace]
  refine ⟨238825362642703670065885469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159216908428469113377256979 238825362642703670065885469)
  ·
    refine ⟨89559510991013876274707051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238825362642703670065885469 89559510991013876274707051)
    ·
      refine ⟨134339266486520814412060577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89559510991013876274707051 134339266486520814412060577)
      ·
        refine ⟨100754449864890610809045433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134339266486520814412060577 100754449864890610809045433)
        ·
          refine ⟨75565837398667958106784075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100754449864890610809045433 75565837398667958106784075)
          ·
            refine ⟨113348756098001937160176113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75565837398667958106784075 113348756098001937160176113)
            ·
              refine ⟨85011567073501452870132085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113348756098001937160176113 85011567073501452870132085)
              ·
                refine ⟨7969834413140761206574883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85011567073501452870132085 7969834413140761206574883)
                ·
                  refine ⟨11954751619711141809862325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7969834413140761206574883 11954751619711141809862325)
                  ·
                    refine ⟨1120757964347919544674593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11954751619711141809862325 1120757964347919544674593)
                    ·
                      rfl

theorem cell23_6548005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_6548005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548005 prefixEnd_6548005 := by exact prefixLift 6548005
  have htrace : WordTrace (prefixWord ++ tailWord_6548005) baseStart_6548005 baseEnd_6548005 := by
    simpa [prefixWord, tailWord_6548005, baseEnd_6548005] using wordTrace_append hprefix tailTrace_6548005
  have hstable : (prefixWord ++ tailWord_6548005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548005).length < 2 ^ (prefixWord ++ tailWord_6548005).sum := by decide
  have hdescent : baseEnd_6548005 < baseStart_6548005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548019 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 1, 1, 3]
def baseStart_6548019 : Nat := 118140960795 + 6548019 * 2 ^ 59
def prefixEnd_6548019 : Nat := 4983230072969 + 3 ^ 40 * 6548019 * 2
def baseEnd_6548019 : Nat := 3362281081772921579248715

theorem tailTrace_6548019 : CollatzResearch.WordTrace tailWord_6548019 prefixEnd_6548019 3362281081772921579248715 := by
  unfold tailWord_6548019
  simp only [CollatzResearch.WordTrace]
  refine ⟨238825873264652950456895111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159217248843101966971263407 238825873264652950456895111)
  ·
    refine ⟨358238809896979425685342667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238825873264652950456895111 358238809896979425685342667)
    ·
      refine ⟨537358214845469138528014001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358238809896979425685342667 537358214845469138528014001)
      ·
        refine ⟨403018661134101853896010501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537358214845469138528014001 403018661134101853896010501)
        ·
          refine ⟨75565998962644097605501969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403018661134101853896010501 75565998962644097605501969)
          ·
            refine ⟨56674499221983073204126477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75565998962644097605501969 56674499221983073204126477)
            ·
              refine ⟨21252937208243652451547429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56674499221983073204126477 21252937208243652451547429)
              ·
                refine ⟨3984925726545684834665143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21252937208243652451547429 3984925726545684834665143)
                ·
                  refine ⟨5977388589818527251997715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984925726545684834665143 5977388589818527251997715)
                  ·
                    refine ⟨8966082884727790877996573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977388589818527251997715 8966082884727790877996573)
                    ·
                      refine ⟨3362281081772921579248715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966082884727790877996573 3362281081772921579248715)
                      ·
                        rfl

theorem cell23_6548019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 1, 3].length) (baseStart_6548019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548019 prefixEnd_6548019 := by exact prefixLift 6548019
  have htrace : WordTrace (prefixWord ++ tailWord_6548019) baseStart_6548019 baseEnd_6548019 := by
    simpa [prefixWord, tailWord_6548019, baseEnd_6548019] using wordTrace_append hprefix tailTrace_6548019
  have hstable : (prefixWord ++ tailWord_6548019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548019).length < 2 ^ (prefixWord ++ tailWord_6548019).sum := by decide
  have hdescent : baseEnd_6548019 < baseStart_6548019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548022 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6548022 : Nat := 118140960795 + 6548022 * 2 ^ 59
def prefixEnd_6548022 : Nat := 4983230072969 + 3 ^ 40 * 6548022 * 2
def baseEnd_6548022 : Nat := 1120760874071628355837067

theorem tailTrace_6548022 : CollatzResearch.WordTrace tailWord_6548022 prefixEnd_6548022 1120760874071628355837067 := by
  unfold tailWord_6548022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14926623917727630123078395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159217321789094721312836213 14926623917727630123078395)
  ·
    refine ⟨22389935876591445184617593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14926623917727630123078395 22389935876591445184617593)
    ·
      refine ⟨16792451907443583888463195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22389935876591445184617593 16792451907443583888463195)
      ·
        refine ⟨25188677861165375832694793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792451907443583888463195 25188677861165375832694793)
        ·
          refine ⟨18891508395874031874521095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25188677861165375832694793 18891508395874031874521095)
          ·
            refine ⟨28337262593811047811781643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18891508395874031874521095 28337262593811047811781643)
            ·
              refine ⟨42505893890716571717672465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28337262593811047811781643 42505893890716571717672465)
              ·
                refine ⟨31879420418037428788254349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42505893890716571717672465 31879420418037428788254349)
                ·
                  refine ⟨11954782656764035795595381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31879420418037428788254349 11954782656764035795595381)
                  ·
                    refine ⟨1120760874071628355837067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11954782656764035795595381 1120760874071628355837067)
                    ·
                      rfl

theorem cell23_6548022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6548022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548022 prefixEnd_6548022 := by exact prefixLift 6548022
  have htrace : WordTrace (prefixWord ++ tailWord_6548022) baseStart_6548022 baseEnd_6548022 := by
    simpa [prefixWord, tailWord_6548022, baseEnd_6548022] using wordTrace_append hprefix tailTrace_6548022
  have hstable : (prefixWord ++ tailWord_6548022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548022).length < 2 ^ (prefixWord ++ tailWord_6548022).sum := by decide
  have hdescent : baseEnd_6548022 < baseStart_6548022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548025 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6548025 : Nat := 118140960795 + 6548025 * 2 ^ 59
def prefixEnd_6548025 : Nat := 4983230072969 + 3 ^ 40 * 6548025 * 2
def baseEnd_6548025 : Nat := 3362284162656848555773687

theorem tailTrace_6548025 : CollatzResearch.WordTrace tailWord_6548025 prefixEnd_6548025 3362284162656848555773687 := by
  unfold tailWord_6548025
  simp only [CollatzResearch.WordTrace]
  refine ⟨238826092102631213481613529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159217394735087475654409019 238826092102631213481613529)
  ·
    refine ⟨179119569076973410111210147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238826092102631213481613529 179119569076973410111210147)
    ·
      refine ⟨268679353615460115166815221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179119569076973410111210147 268679353615460115166815221)
      ·
        refine ⟨25188689401449385796888927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268679353615460115166815221 25188689401449385796888927)
        ·
          refine ⟨37783034102174078695333391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25188689401449385796888927 37783034102174078695333391)
          ·
            refine ⟨56674551153261118043000087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37783034102174078695333391 56674551153261118043000087)
            ·
              refine ⟨85011826729891677064500131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56674551153261118043000087 85011826729891677064500131)
              ·
                refine ⟨127517740094837515596750197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85011826729891677064500131 127517740094837515596750197)
                ·
                  refine ⟨11954788133891017087195331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127517740094837515596750197 11954788133891017087195331)
                  ·
                    refine ⟨17932182200836525630792997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11954788133891017087195331 17932182200836525630792997)
                    ·
                      refine ⟨3362284162656848555773687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17932182200836525630792997 3362284162656848555773687)
                      ·
                        rfl

theorem cell23_6548025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6548025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548025 prefixEnd_6548025 := by exact prefixLift 6548025
  have htrace : WordTrace (prefixWord ++ tailWord_6548025) baseStart_6548025 baseEnd_6548025 := by
    simpa [prefixWord, tailWord_6548025, baseEnd_6548025] using wordTrace_append hprefix tailTrace_6548025
  have hstable : (prefixWord ++ tailWord_6548025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548025).length < 2 ^ (prefixWord ++ tailWord_6548025).sum := by decide
  have hdescent : baseEnd_6548025 < baseStart_6548025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548055 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_6548055 : Nat := 118140960795 + 6548055 * 2 ^ 59
def prefixEnd_6548055 : Nat := 4983230072969 + 3 ^ 40 * 6548055 * 2
def baseEnd_6548055 : Nat := 3362299567076483438398549

theorem tailTrace_6548055 : CollatzResearch.WordTrace tailWord_6548055 prefixEnd_6548055 3362299567076483438398549 := by
  unfold tailWord_6548055
  simp only [CollatzResearch.WordTrace]
  refine ⟨238827186292522528605205619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159218124195015019070137079 238827186292522528605205619)
  ·
    refine ⟨358240779438783792907808429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238827186292522528605205619 358240779438783792907808429)
    ·
      refine ⟨134340292289543922340428161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358240779438783792907808429 134340292289543922340428161)
      ·
        refine ⟨100755219217157941755321121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134340292289543922340428161 100755219217157941755321121)
        ·
          refine ⟨75566414412868456316490841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100755219217157941755321121 75566414412868456316490841)
          ·
            refine ⟨56674810809651342237368131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75566414412868456316490841 56674810809651342237368131)
            ·
              refine ⟨85012216214477013356052197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56674810809651342237368131 85012216214477013356052197)
              ·
                refine ⟨15939790540214440004259787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85012216214477013356052197 15939790540214440004259787)
                ·
                  refine ⟨23909685810321660006389681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939790540214440004259787 23909685810321660006389681)
                  ·
                    refine ⟨17932264357741245004792261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23909685810321660006389681 17932264357741245004792261)
                    ·
                      refine ⟨3362299567076483438398549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17932264357741245004792261 3362299567076483438398549)
                      ·
                        rfl

theorem cell23_6548055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_6548055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548055 prefixEnd_6548055 := by exact prefixLift 6548055
  have htrace : WordTrace (prefixWord ++ tailWord_6548055) baseStart_6548055 baseEnd_6548055 := by
    simpa [prefixWord, tailWord_6548055, baseEnd_6548055] using wordTrace_append hprefix tailTrace_6548055
  have hstable : (prefixWord ++ tailWord_6548055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548055).length < 2 ^ (prefixWord ++ tailWord_6548055).sum := by decide
  have hdescent : baseEnd_6548055 < baseStart_6548055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548076 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 1, 2, 2]
def baseStart_6548076 : Nat := 118140960795 + 6548076 * 2 ^ 59
def prefixEnd_6548076 : Nat := 4983230072969 + 3 ^ 40 * 6548076 * 2
def baseEnd_6548076 : Nat := 3362310350170227856235953

theorem tailTrace_6548076 : CollatzResearch.WordTrace tailWord_6548076 prefixEnd_6548076 3362310350170227856235953 := by
  unfold tailWord_6548076
  simp only [CollatzResearch.WordTrace]
  refine ⟨119413976112723224595860041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159218634816964299461146721 119413976112723224595860041)
  ·
    refine ⟨89560482084542418446895031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119413976112723224595860041 89560482084542418446895031)
    ·
      refine ⟨134340723126813627670342547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89560482084542418446895031 134340723126813627670342547)
      ·
        refine ⟨201511084690220441505513821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134340723126813627670342547 201511084690220441505513821)
        ·
          refine ⟨75566656758832665564567683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201511084690220441505513821 75566656758832665564567683)
          ·
            refine ⟨113349985138248998346851525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75566656758832665564567683 113349985138248998346851525)
            ·
              refine ⟨21253122213421687190034661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113349985138248998346851525 21253122213421687190034661)
              ·
                refine ⟨3984960415016566348131499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21253122213421687190034661 3984960415016566348131499)
                ·
                  refine ⟨5977440622524849522197249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984960415016566348131499 5977440622524849522197249)
                  ·
                    refine ⟨4483080466893637141647937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5977440622524849522197249 4483080466893637141647937)
                    ·
                      refine ⟨3362310350170227856235953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483080466893637141647937 3362310350170227856235953)
                      ·
                        rfl

theorem cell23_6548076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_6548076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548076 prefixEnd_6548076 := by exact prefixLift 6548076
  have htrace : WordTrace (prefixWord ++ tailWord_6548076) baseStart_6548076 baseEnd_6548076 := by
    simpa [prefixWord, tailWord_6548076, baseEnd_6548076] using wordTrace_append hprefix tailTrace_6548076
  have hstable : (prefixWord ++ tailWord_6548076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548076).length < 2 ^ (prefixWord ++ tailWord_6548076).sum := by decide
  have hdescent : baseEnd_6548076 < baseStart_6548076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548086 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6548086 : Nat := 118140960795 + 6548086 * 2 ^ 59
def prefixEnd_6548086 : Nat := 4983230072969 + 3 ^ 40 * 6548086 * 2
def baseEnd_6548086 : Nat := 1120771828325590939036969

theorem tailTrace_6548086 : CollatzResearch.WordTrace tailWord_6548086 prefixEnd_6548086 1120771828325590939036969 := by
  unfold tailWord_6548086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14926769809713138806224007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159218877970273480599722741 14926769809713138806224007)
  ·
    refine ⟨22390154714569708209336011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14926769809713138806224007 22390154714569708209336011)
    ·
      refine ⟨33585232071854562314004017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22390154714569708209336011 33585232071854562314004017)
      ·
        refine ⟨25188924053890921735503013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33585232071854562314004017 25188924053890921735503013)
        ·
          refine ⟨4722923260104547825406815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25188924053890921735503013 4722923260104547825406815)
          ·
            refine ⟨7084384890156821738110223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722923260104547825406815 7084384890156821738110223)
            ·
              refine ⟨10626577335235232607165335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084384890156821738110223 10626577335235232607165335)
              ·
                refine ⟨15939866002852848910748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626577335235232607165335 15939866002852848910748003)
                ·
                  refine ⟨23909799004279273366122005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939866002852848910748003 23909799004279273366122005)
                  ·
                    refine ⟨1120771828325590939036969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23909799004279273366122005 1120771828325590939036969)
                    ·
                      rfl

theorem cell23_6548086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6548086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548086 prefixEnd_6548086 := by exact prefixLift 6548086
  have htrace : WordTrace (prefixWord ++ tailWord_6548086) baseStart_6548086 baseEnd_6548086 := by
    simpa [prefixWord, tailWord_6548086, baseEnd_6548086] using wordTrace_append hprefix tailTrace_6548086
  have hstable : (prefixWord ++ tailWord_6548086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548086).length < 2 ^ (prefixWord ++ tailWord_6548086).sum := by decide
  have hdescent : baseEnd_6548086 < baseStart_6548086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548092 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_6548092 : Nat := 118140960795 + 6548092 * 2 ^ 59
def prefixEnd_6548092 : Nat := 4983230072969 + 3 ^ 40 * 6548092 * 2
def baseEnd_6548092 : Nat := 3362318565860699793635879

theorem tailTrace_6548092 : CollatzResearch.WordTrace tailWord_6548092 prefixEnd_6548092 3362318565860699793635879 := by
  unfold tailWord_6548092
  simp only [CollatzResearch.WordTrace]
  refine ⟨119414267896694241962151265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159219023862258989282868353 119414267896694241962151265)
  ·
    refine ⟨89560700922520681471613449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119414267896694241962151265 89560700922520681471613449)
    ·
      refine ⟨67170525691890511103710087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89560700922520681471613449 67170525691890511103710087)
      ·
        refine ⟨100755788537835766655565131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67170525691890511103710087 100755788537835766655565131)
        ·
          refine ⟨151133682806753649983347697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100755788537835766655565131 151133682806753649983347697)
          ·
            refine ⟨113350262105065237487510773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151133682806753649983347697 113350262105065237487510773)
            ·
              refine ⟨10626587072349866014454135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113350262105065237487510773 10626587072349866014454135)
              ·
                refine ⟨15939880608524799021681203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626587072349866014454135 15939880608524799021681203)
                ·
                  refine ⟨23909820912787198532521805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15939880608524799021681203 23909820912787198532521805)
                  ·
                    refine ⟨8966182842295199449695677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23909820912787198532521805 8966182842295199449695677)
                    ·
                      refine ⟨3362318565860699793635879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966182842295199449695677 3362318565860699793635879)
                      ·
                        rfl

theorem cell23_6548092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_6548092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548092 prefixEnd_6548092 := by exact prefixLift 6548092
  have htrace : WordTrace (prefixWord ++ tailWord_6548092) baseStart_6548092 baseEnd_6548092 := by
    simpa [prefixWord, tailWord_6548092, baseEnd_6548092] using wordTrace_append hprefix tailTrace_6548092
  have hstable : (prefixWord ++ tailWord_6548092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548092).length < 2 ^ (prefixWord ++ tailWord_6548092).sum := by decide
  have hdescent : baseEnd_6548092 < baseStart_6548092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548119 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_6548119 : Nat := 118140960795 + 6548119 * 2 ^ 59
def prefixEnd_6548119 : Nat := 4983230072969 + 3 ^ 40 * 6548119 * 2
def baseEnd_6548119 : Nat := 3362332429838371187998255

theorem tailTrace_6548119 : CollatzResearch.WordTrace tailWord_6548119 prefixEnd_6548119 3362332429838371187998255 := by
  unfold tailWord_6548119
  simp only [CollatzResearch.WordTrace]
  refine ⟨238829520564290667535535411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159219680376193778357023607 238829520564290667535535411)
  ·
    refine ⟨358244280846436001303303117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238829520564290667535535411 358244280846436001303303117)
    ·
      refine ⟨134341605317413500488738669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358244280846436001303303117 134341605317413500488738669)
      ·
        refine ⟨50378101994030062683277001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134341605317413500488738669 50378101994030062683277001)
        ·
          refine ⟨37783576495522547012457751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50378101994030062683277001 37783576495522547012457751)
          ·
            refine ⟨56675364743283820518686627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37783576495522547012457751 56675364743283820518686627)
            ·
              refine ⟨85013047114925730778029941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56675364743283820518686627 85013047114925730778029941)
              ·
                refine ⟨7969973167024287260440307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85013047114925730778029941 7969973167024287260440307)
                ·
                  refine ⟨11954959750536430890660461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7969973167024287260440307 11954959750536430890660461)
                  ·
                    refine ⟨4483109906451161583997673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11954959750536430890660461 4483109906451161583997673)
                    ·
                      refine ⟨3362332429838371187998255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483109906451161583997673 3362332429838371187998255)
                      ·
                        rfl

theorem cell23_6548119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_6548119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548119 prefixEnd_6548119 := by exact prefixLift 6548119
  have htrace : WordTrace (prefixWord ++ tailWord_6548119) baseStart_6548119 baseEnd_6548119 := by
    simpa [prefixWord, tailWord_6548119, baseEnd_6548119] using wordTrace_append hprefix tailTrace_6548119
  have hstable : (prefixWord ++ tailWord_6548119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548119).length < 2 ^ (prefixWord ++ tailWord_6548119).sum := by decide
  have hdescent : baseEnd_6548119 < baseStart_6548119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548125 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_6548125 : Nat := 118140960795 + 6548125 * 2 ^ 59
def prefixEnd_6548125 : Nat := 4983230072969 + 3 ^ 40 * 6548125 * 2
def baseEnd_6548125 : Nat := 1120778503574099388174409

theorem tailTrace_6548125 : CollatzResearch.WordTrace tailWord_6548125 prefixEnd_6548125 1120778503574099388174409 := by
  unfold tailWord_6548125
  simp only [CollatzResearch.WordTrace]
  refine ⟨238829739402268930560253829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159219826268179287040169219 238829739402268930560253829)
  ·
    refine ⟨44780576137925424480047593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238829739402268930560253829 44780576137925424480047593)
    ·
      refine ⟨33585432103444068360035695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44780576137925424480047593 33585432103444068360035695)
      ·
        refine ⟨50378148155166102540053543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33585432103444068360035695 50378148155166102540053543)
        ·
          refine ⟨75567222232749153810080315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50378148155166102540053543 75567222232749153810080315)
          ·
            refine ⟨113350833349123730715120473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75567222232749153810080315 113350833349123730715120473)
            ·
              refine ⟨85013125011842798036340355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113350833349123730715120473 85013125011842798036340355)
              ·
                refine ⟨127519687517764197054510533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85013125011842798036340355 127519687517764197054510533)
                ·
                  refine ⟨23909941409580786947720725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127519687517764197054510533 23909941409580786947720725)
                  ·
                    refine ⟨1120778503574099388174409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23909941409580786947720725 1120778503574099388174409)
                    ·
                      rfl

theorem cell23_6548125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_6548125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548125 prefixEnd_6548125 := by exact prefixLift 6548125
  have htrace : WordTrace (prefixWord ++ tailWord_6548125) baseStart_6548125 baseEnd_6548125 := by
    simpa [prefixWord, tailWord_6548125, baseEnd_6548125] using wordTrace_append hprefix tailTrace_6548125
  have hstable : (prefixWord ++ tailWord_6548125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548125).length < 2 ^ (prefixWord ++ tailWord_6548125).sum := by decide
  have hdescent : baseEnd_6548125 < baseStart_6548125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548126 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6548126 : Nat := 118140960795 + 6548126 * 2 ^ 59
def prefixEnd_6548126 : Nat := 4983230072969 + 3 ^ 40 * 6548126 * 2
def baseEnd_6548126 : Nat := 3362336024202952660610723

theorem tailTrace_6548126 : CollatzResearch.WordTrace tailWord_6548126 prefixEnd_6548126 3362336024202952660610723 := by
  unfold tailWord_6548126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853721984408163466380029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159219850583510205154026821 29853721984408163466380029)
  ·
    refine ⟨11195145744153061299892511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29853721984408163466380029 11195145744153061299892511)
    ·
      refine ⟨16792718616229591949838767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195145744153061299892511 16792718616229591949838767)
      ·
        refine ⟨25189077924344387924758151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792718616229591949838767 25189077924344387924758151)
        ·
          refine ⟨37783616886516581887137227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25189077924344387924758151 37783616886516581887137227)
          ·
            refine ⟨56675425329774872830705841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37783616886516581887137227 56675425329774872830705841)
            ·
              refine ⟨42506568997331154623029381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56675425329774872830705841 42506568997331154623029381)
              ·
                refine ⟨7969981686999591491818009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42506568997331154623029381 7969981686999591491818009)
                ·
                  refine ⟨5977486265249693618863507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969981686999591491818009 5977486265249693618863507)
                  ·
                    refine ⟨8966229397874540428295261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977486265249693618863507 8966229397874540428295261)
                    ·
                      refine ⟨3362336024202952660610723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966229397874540428295261 3362336024202952660610723)
                      ·
                        rfl

theorem cell23_6548126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6548126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548126 prefixEnd_6548126 := by exact prefixLift 6548126
  have htrace : WordTrace (prefixWord ++ tailWord_6548126) baseStart_6548126 baseEnd_6548126 := by
    simpa [prefixWord, tailWord_6548126, baseEnd_6548126] using wordTrace_append hprefix tailTrace_6548126
  have hstable : (prefixWord ++ tailWord_6548126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548126).length < 2 ^ (prefixWord ++ tailWord_6548126).sum := by decide
  have hdescent : baseEnd_6548126 < baseStart_6548126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548349 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_6548349 : Nat := 118140960795 + 6548349 * 2 ^ 59
def prefixEnd_6548349 : Nat := 4983230072969 + 3 ^ 40 * 6548349 * 2
def baseEnd_6548349 : Nat := 3362450530388905288122197

theorem tailTrace_6548349 : CollatzResearch.WordTrace tailWord_6548349 prefixEnd_6548349 3362450530388905288122197 := by
  unfold tailWord_6548349
  simp only [CollatzResearch.WordTrace]
  refine ⟨238837909353457416816408101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159225272902304944544272067 238837909353457416816408101)
  ·
    refine ⟨44782108003773265653076519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238837909353457416816408101 44782108003773265653076519)
    ·
      refine ⟨67173162005659898479614779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44782108003773265653076519 67173162005659898479614779)
      ·
        refine ⟨100759743008489847719422169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67173162005659898479614779 100759743008489847719422169)
        ·
          refine ⟨75569807256367385789566627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100759743008489847719422169 75569807256367385789566627)
          ·
            refine ⟨113354710884551078684349941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75569807256367385789566627 113354710884551078684349941)
            ·
              refine ⟨10627004145426663626657807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113354710884551078684349941 10627004145426663626657807)
              ·
                refine ⟨15940506218139995439986711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10627004145426663626657807 15940506218139995439986711)
                ·
                  refine ⟨23910759327209993159980067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15940506218139995439986711 23910759327209993159980067)
                  ·
                    refine ⟨35866138990814989739970101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23910759327209993159980067 35866138990814989739970101)
                    ·
                      refine ⟨3362450530388905288122197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35866138990814989739970101 3362450530388905288122197)
                      ·
                        rfl

theorem cell23_6548349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_6548349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548349 prefixEnd_6548349 := by exact prefixLift 6548349
  have htrace : WordTrace (prefixWord ++ tailWord_6548349) baseStart_6548349 baseEnd_6548349 := by
    simpa [prefixWord, tailWord_6548349, baseEnd_6548349] using wordTrace_append hprefix tailTrace_6548349
  have hstable : (prefixWord ++ tailWord_6548349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548349).length < 2 ^ (prefixWord ++ tailWord_6548349).sum := by decide
  have hdescent : baseEnd_6548349 < baseStart_6548349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548380 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6548380 : Nat := 118140960795 + 6548380 * 2 ^ 59
def prefixEnd_6548380 : Nat := 4983230072969 + 3 ^ 40 * 6548380 * 2
def baseEnd_6548380 : Nat := 3362466448289194666834555

theorem tailTrace_6548380 : CollatzResearch.WordTrace tailWord_6548380 prefixEnd_6548380 3362466448289194666834555 := by
  unfold tailWord_6548380
  simp only [CollatzResearch.WordTrace]
  refine ⟨119419520008172554555393297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159226026677563406073857729 119419520008172554555393297)
  ·
    refine ⟨89564640006129415916544973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119419520008172554555393297 89564640006129415916544973)
    ·
      refine ⟨33586740002298530968704365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89564640006129415916544973 33586740002298530968704365)
      ·
        refine ⟨12595027500861949113264137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33586740002298530968704365 12595027500861949113264137)
        ·
          refine ⟨9446270625646461834948103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595027500861949113264137 9446270625646461834948103)
          ·
            refine ⟨14169405938469692752422155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446270625646461834948103 14169405938469692752422155)
            ·
              refine ⟨21254108907704539128633233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14169405938469692752422155 21254108907704539128633233)
              ·
                refine ⟨15940581680778404346474925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21254108907704539128633233 15940581680778404346474925)
                ·
                  refine ⟨5977718130291901629928097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15940581680778404346474925 5977718130291901629928097)
                  ·
                    refine ⟨4483288597718926222446073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5977718130291901629928097 4483288597718926222446073)
                    ·
                      refine ⟨3362466448289194666834555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483288597718926222446073 3362466448289194666834555)
                      ·
                        rfl

theorem cell23_6548380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6548380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548380 prefixEnd_6548380 := by exact prefixLift 6548380
  have htrace : WordTrace (prefixWord ++ tailWord_6548380) baseStart_6548380 baseEnd_6548380 := by
    simpa [prefixWord, tailWord_6548380, baseEnd_6548380] using wordTrace_append hprefix tailTrace_6548380
  have hstable : (prefixWord ++ tailWord_6548380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548380).length < 2 ^ (prefixWord ++ tailWord_6548380).sum := by decide
  have hdescent : baseEnd_6548380 < baseStart_6548380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548386 : List Nat := [3, 3, 1, 2, 2, 2, 3, 7]
def baseStart_6548386 : Nat := 118140960795 + 6548386 * 2 ^ 59
def prefixEnd_6548386 : Nat := 4983230072969 + 3 ^ 40 * 6548386 * 2
def baseEnd_6548386 : Nat := 124535908487893394198501

theorem tailTrace_6548386 : CollatzResearch.WordTrace tailWord_6548386 prefixEnd_6548386 124535908487893394198501 := by
  unfold tailWord_6548386
  simp only [CollatzResearch.WordTrace]
  refine ⟨59709814713580843033876253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159226172569548914757003341 59709814713580843033876253)
  ·
    refine ⟨22391180517592816137703595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59709814713580843033876253 22391180517592816137703595)
    ·
      refine ⟨33586770776389224206555393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22391180517592816137703595 33586770776389224206555393)
      ·
        refine ⟨25190078082291918154916545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33586770776389224206555393 25190078082291918154916545)
        ·
          refine ⟨18892558561718938616187409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25190078082291918154916545 18892558561718938616187409)
          ·
            refine ⟨14169418921289203962140557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18892558561718938616187409 14169418921289203962140557)
            ·
              refine ⟨5313532095483451485802709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14169418921289203962140557 5313532095483451485802709)
              ·
                refine ⟨124535908487893394198501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5313532095483451485802709 124535908487893394198501)
                ·
                  rfl

theorem cell23_6548386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_6548386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548386 prefixEnd_6548386 := by exact prefixLift 6548386
  have htrace : WordTrace (prefixWord ++ tailWord_6548386) baseStart_6548386 baseEnd_6548386 := by
    simpa [prefixWord, tailWord_6548386, baseEnd_6548386] using wordTrace_append hprefix tailTrace_6548386
  have hstable : (prefixWord ++ tailWord_6548386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548386).length < 2 ^ (prefixWord ++ tailWord_6548386).sum := by decide
  have hdescent : baseEnd_6548386 < baseStart_6548386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548397 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6548397 : Nat := 118140960795 + 6548397 * 2 ^ 59
def prefixEnd_6548397 : Nat := 4983230072969 + 3 ^ 40 * 6548397 * 2
def baseEnd_6548397 : Nat := 3362475177460321100321977

theorem tailTrace_6548397 : CollatzResearch.WordTrace tailWord_6548397 prefixEnd_6548397 3362475177460321100321977 := by
  unfold tailWord_6548397
  simp only [CollatzResearch.WordTrace]
  refine ⟨238839660057283521014155445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159226440038189014009436963 238839660057283521014155445)
  ·
    refine ⟨22391218130370330095077073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238839660057283521014155445 22391218130370330095077073)
    ·
      refine ⟨16793413597777747571307805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22391218130370330095077073 16793413597777747571307805)
      ·
        refine ⟨6297530099166655339240427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16793413597777747571307805 6297530099166655339240427)
        ·
          refine ⟨9446295148749983008860641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297530099166655339240427 9446295148749983008860641)
          ·
            refine ⟨7084721361562487256645481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9446295148749983008860641 7084721361562487256645481)
            ·
              refine ⟨5313541021171865442484111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7084721361562487256645481 5313541021171865442484111)
              ·
                refine ⟨7970311531757798163726167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313541021171865442484111 7970311531757798163726167)
                ·
                  refine ⟨11955467297636697245589251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970311531757798163726167 11955467297636697245589251)
                  ·
                    refine ⟨17933200946455045868383877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11955467297636697245589251 17933200946455045868383877)
                    ·
                      refine ⟨3362475177460321100321977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17933200946455045868383877 3362475177460321100321977)
                      ·
                        rfl

theorem cell23_6548397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6548397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548397 prefixEnd_6548397 := by exact prefixLift 6548397
  have htrace : WordTrace (prefixWord ++ tailWord_6548397) baseStart_6548397 baseEnd_6548397 := by
    simpa [prefixWord, tailWord_6548397, baseEnd_6548397] using wordTrace_append hprefix tailTrace_6548397
  have hstable : (prefixWord ++ tailWord_6548397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548397).length < 2 ^ (prefixWord ++ tailWord_6548397).sum := by decide
  have hdescent : baseEnd_6548397 < baseStart_6548397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548413 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6548413 : Nat := 118140960795 + 6548413 * 2 ^ 59
def prefixEnd_6548413 : Nat := 4983230072969 + 3 ^ 40 * 6548413 * 2
def baseEnd_6548413 : Nat := 3362483393150793037721903

theorem tailTrace_6548413 : CollatzResearch.WordTrace tailWord_6548413 prefixEnd_6548413 3362483393150793037721903 := by
  unfold tailWord_6548413
  simp only [CollatzResearch.WordTrace]
  refine ⟨238840243625225555746737893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159226829083483703831158595 238840243625225555746737893)
  ·
    refine ⟨44782545679729791702513355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238840243625225555746737893 44782545679729791702513355)
    ·
      refine ⟨67173818519594687553770033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44782545679729791702513355 67173818519594687553770033)
      ·
        refine ⟨50380363889696015665327525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67173818519594687553770033 50380363889696015665327525)
        ·
          refine ⟨9446318229318002937248911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50380363889696015665327525 9446318229318002937248911)
          ·
            refine ⟨14169477343977004405873367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446318229318002937248911 14169477343977004405873367)
            ·
              refine ⟨21254216015965506608810051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14169477343977004405873367 21254216015965506608810051)
              ·
                refine ⟨31881324023948259913215077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21254216015965506608810051 31881324023948259913215077)
                ·
                  refine ⟨5977748254490298733727827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31881324023948259913215077 5977748254490298733727827)
                  ·
                    refine ⟨8966622381735448100591741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977748254490298733727827 8966622381735448100591741)
                    ·
                      refine ⟨3362483393150793037721903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966622381735448100591741 3362483393150793037721903)
                      ·
                        rfl

theorem cell23_6548413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6548413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548413 prefixEnd_6548413 := by exact prefixLift 6548413
  have htrace : WordTrace (prefixWord ++ tailWord_6548413) baseStart_6548413 baseEnd_6548413 := by
    simpa [prefixWord, tailWord_6548413, baseEnd_6548413] using wordTrace_append hprefix tailTrace_6548413
  have hstable : (prefixWord ++ tailWord_6548413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548413).length < 2 ^ (prefixWord ++ tailWord_6548413).sum := by decide
  have hdescent : baseEnd_6548413 < baseStart_6548413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548430 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_6548430 : Nat := 118140960795 + 6548430 * 2 ^ 59
def prefixEnd_6548430 : Nat := 4983230072969 + 3 ^ 40 * 6548430 * 2
def baseEnd_6548430 : Nat := 3362492122321919471209325

theorem tailTrace_6548430 : CollatzResearch.WordTrace tailWord_6548430 prefixEnd_6548430 3362492122321919471209325 := by
  unfold tailWord_6548430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29855107958270495956263343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159227242444109311766737829 29855107958270495956263343)
  ·
    refine ⟨44782661937405743934395015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29855107958270495956263343 44782661937405743934395015)
    ·
      refine ⟨67173992906108615901592523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44782661937405743934395015 67173992906108615901592523)
      ·
        refine ⟨100760989359162923852388785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67173992906108615901592523 100760989359162923852388785)
        ·
          refine ⟨75570742019372192889291589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100760989359162923852388785 75570742019372192889291589)
          ·
            refine ⟨14169514128632286166742173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75570742019372192889291589 14169514128632286166742173)
            ·
              refine ⟨5313567798237107312528315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14169514128632286166742173 5313567798237107312528315)
              ·
                refine ⟨7970351697355660968792473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313567798237107312528315 7970351697355660968792473)
                ·
                  refine ⟨5977763773016745726594355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7970351697355660968792473 5977763773016745726594355)
                  ·
                    refine ⟨8966645659525118589891533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977763773016745726594355 8966645659525118589891533)
                    ·
                      refine ⟨3362492122321919471209325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966645659525118589891533 3362492122321919471209325)
                      ·
                        rfl

theorem cell23_6548430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_6548430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548430 prefixEnd_6548430 := by exact prefixLift 6548430
  have htrace : WordTrace (prefixWord ++ tailWord_6548430) baseStart_6548430 baseEnd_6548430 := by
    simpa [prefixWord, tailWord_6548430, baseEnd_6548430] using wordTrace_append hprefix tailTrace_6548430
  have hstable : (prefixWord ++ tailWord_6548430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548430).length < 2 ^ (prefixWord ++ tailWord_6548430).sum := by decide
  have hdescent : baseEnd_6548430 < baseStart_6548430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548470 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6548470 : Nat := 118140960795 + 6548470 * 2 ^ 59
def prefixEnd_6548470 : Nat := 4983230072969 + 3 ^ 40 * 6548470 * 2
def baseEnd_6548470 : Nat := 3362512661548099314709141

theorem tailTrace_6548470 : CollatzResearch.WordTrace tailWord_6548470 prefixEnd_6548470 3362512661548099314709141 := by
  unfold tailWord_6548470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927645161626190905097679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159228215057346036321041909 14927645161626190905097679)
  ·
    refine ⟨22391467742439286357646519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927645161626190905097679 22391467742439286357646519)
    ·
      refine ⟨33587201613658929536469779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22391467742439286357646519 33587201613658929536469779)
      ·
        refine ⟨50380802420488394304704669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33587201613658929536469779 50380802420488394304704669)
        ·
          refine ⟨18892800907683147864264251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50380802420488394304704669 18892800907683147864264251)
          ·
            refine ⟨28339201361524721796396377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18892800907683147864264251 28339201361524721796396377)
            ·
              refine ⟨21254401021143541347297283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28339201361524721796396377 21254401021143541347297283)
              ·
                refine ⟨31881601531715312020945925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21254401021143541347297283 31881601531715312020945925)
                ·
                  refine ⟨5977800287196621003927361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31881601531715312020945925 5977800287196621003927361)
                  ·
                    refine ⟨4483350215397465752945521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5977800287196621003927361 4483350215397465752945521)
                    ·
                      refine ⟨3362512661548099314709141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483350215397465752945521 3362512661548099314709141)
                      ·
                        rfl

theorem cell23_6548470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6548470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548470 prefixEnd_6548470 := by exact prefixLift 6548470
  have htrace : WordTrace (prefixWord ++ tailWord_6548470) baseStart_6548470 baseEnd_6548470 := by
    simpa [prefixWord, tailWord_6548470, baseEnd_6548470] using wordTrace_append hprefix tailTrace_6548470
  have hstable : (prefixWord ++ tailWord_6548470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548470).length < 2 ^ (prefixWord ++ tailWord_6548470).sum := by decide
  have hdescent : baseEnd_6548470 < baseStart_6548470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548476 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 7]
def baseStart_6548476 : Nat := 118140960795 + 6548476 * 2 ^ 59
def prefixEnd_6548476 : Nat := 4983230072969 + 3 ^ 40 * 6548476 * 2
def baseEnd_6548476 : Nat := 373612860270225143470457

theorem tailTrace_6548476 : CollatzResearch.WordTrace tailWord_6548476 prefixEnd_6548476 373612860270225143470457 := by
  unfold tailWord_6548476
  simp only [CollatzResearch.WordTrace]
  refine ⟨119421270711998658753140641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159228360949331545004187521 119421270711998658753140641)
  ·
    refine ⟨89565953033998994064855481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119421270711998658753140641 89565953033998994064855481)
    ·
      refine ⟨67174464775499245548641611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89565953033998994064855481 67174464775499245548641611)
      ·
        refine ⟨100761697163248868322962417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67174464775499245548641611 100761697163248868322962417)
        ·
          refine ⟨75571272872436651242221813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100761697163248868322962417 75571272872436651242221813)
          ·
            refine ⟨7084806831790936053958295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75571272872436651242221813 7084806831790936053958295)
            ·
              refine ⟨10627210247686404080937443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084806831790936053958295 10627210247686404080937443)
              ·
                refine ⟨15940815371529606121406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10627210247686404080937443 15940815371529606121406165)
                ·
                  refine ⟨373612860270225143470457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15940815371529606121406165 373612860270225143470457)
                  ·
                    rfl

theorem cell23_6548476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_6548476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548476 prefixEnd_6548476 := by exact prefixLift 6548476
  have htrace : WordTrace (prefixWord ++ tailWord_6548476) baseStart_6548476 baseEnd_6548476 := by
    simpa [prefixWord, tailWord_6548476, baseEnd_6548476] using wordTrace_append hprefix tailTrace_6548476
  have hstable : (prefixWord ++ tailWord_6548476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548476).length < 2 ^ (prefixWord ++ tailWord_6548476).sum := by decide
  have hdescent : baseEnd_6548476 < baseStart_6548476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548506 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_6548506 : Nat := 118140960795 + 6548506 * 2 ^ 59
def prefixEnd_6548506 : Nat := 4983230072969 + 3 ^ 40 * 6548506 * 2
def baseEnd_6548506 : Nat := 1120843715617220391286325

theorem tailTrace_6548506 : CollatzResearch.WordTrace tailWord_6548506 prefixEnd_6548506 1120843715617220391286325 := by
  unfold tailWord_6548506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59710908903472158157468343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159229090409259088419915581 59710908903472158157468343)
  ·
    refine ⟨89566363355208237236202515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59710908903472158157468343 89566363355208237236202515)
    ·
      refine ⟨134349545032812355854303773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89566363355208237236202515 134349545032812355854303773)
      ·
        refine ⟨50381079387304633445363915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134349545032812355854303773 50381079387304633445363915)
        ·
          refine ⟨75571619080956950168045873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50381079387304633445363915 75571619080956950168045873)
          ·
            refine ⟨56678714310717712626034405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75571619080956950168045873 56678714310717712626034405)
            ·
              refine ⟨10627258933259571117381451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56678714310717712626034405 10627258933259571117381451)
              ·
                refine ⟨15940888399889356676072177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10627258933259571117381451 15940888399889356676072177)
                ·
                  refine ⟨11955666299917017507054133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15940888399889356676072177 11955666299917017507054133)
                  ·
                    refine ⟨1120843715617220391286325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11955666299917017507054133 1120843715617220391286325)
                    ·
                      rfl

theorem cell23_6548506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_6548506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548506 prefixEnd_6548506 := by exact prefixLift 6548506
  have htrace : WordTrace (prefixWord ++ tailWord_6548506) baseStart_6548506 baseEnd_6548506 := by
    simpa [prefixWord, tailWord_6548506, baseEnd_6548506] using wordTrace_append hprefix tailTrace_6548506
  have hstable : (prefixWord ++ tailWord_6548506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548506).length < 2 ^ (prefixWord ++ tailWord_6548506).sum := by decide
  have hdescent : baseEnd_6548506 < baseStart_6548506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548516 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6548516 : Nat := 118140960795 + 6548516 * 2 ^ 59
def prefixEnd_6548516 : Nat := 4983230072969 + 3 ^ 40 * 6548516 * 2
def baseEnd_6548516 : Nat := 3362536281658206134733929

theorem tailTrace_6548516 : CollatzResearch.WordTrace tailWord_6548516 prefixEnd_6548516 3362536281658206134733929 := by
  unfold tailWord_6548516
  simp only [CollatzResearch.WordTrace]
  refine ⟨119422000171926202168868701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159229333562568269558491601 119422000171926202168868701)
  ·
    refine ⟨44783250064472325813325763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119422000171926202168868701 44783250064472325813325763)
    ·
      refine ⟨67174875096708488719988645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44783250064472325813325763 67174875096708488719988645)
      ·
        refine ⟨12595289080632841634997871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67174875096708488719988645 12595289080632841634997871)
        ·
          refine ⟨18892933620949262452496807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595289080632841634997871 18892933620949262452496807)
          ·
            refine ⟨28339400431423893678745211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18892933620949262452496807 28339400431423893678745211)
            ·
              refine ⟨42509100647135840518117817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28339400431423893678745211 42509100647135840518117817)
              ·
                refine ⟨31881825485351880388588363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42509100647135840518117817 31881825485351880388588363)
                ·
                  refine ⟨47822738228027820582882545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31881825485351880388588363 47822738228027820582882545)
                  ·
                    refine ⟨35867053671020865437161909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47822738228027820582882545 35867053671020865437161909)
                    ·
                      refine ⟨3362536281658206134733929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35867053671020865437161909 3362536281658206134733929)
                      ·
                        rfl

theorem cell23_6548516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6548516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548516 prefixEnd_6548516 := by exact prefixLift 6548516
  have htrace : WordTrace (prefixWord ++ tailWord_6548516) baseStart_6548516 baseEnd_6548516 := by
    simpa [prefixWord, tailWord_6548516, baseEnd_6548516] using wordTrace_append hprefix tailTrace_6548516
  have hstable : (prefixWord ++ tailWord_6548516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548516).length < 2 ^ (prefixWord ++ tailWord_6548516).sum := by decide
  have hdescent : baseEnd_6548516 < baseStart_6548516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548529 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6548529 : Nat := 118140960795 + 6548529 * 2 ^ 59
def prefixEnd_6548529 : Nat := 4983230072969 + 3 ^ 40 * 6548529 * 2
def baseEnd_6548529 : Nat := 3362542956906714583871369

theorem tailTrace_6548529 : CollatzResearch.WordTrace tailWord_6548529 prefixEnd_6548529 3362542956906714583871369 := by
  unfold tailWord_6548529
  simp only [CollatzResearch.WordTrace]
  refine ⟨238844474492805307557960641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159229649661870205038640427 238844474492805307557960641)
  ·
    refine ⟨179133355869603980668470481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238844474492805307557960641 179133355869603980668470481)
    ·
      refine ⟨134350016902202985501352861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179133355869603980668470481 134350016902202985501352861)
      ·
        refine ⟨50381256338326119563007323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134350016902202985501352861 50381256338326119563007323)
        ·
          refine ⟨75571884507489179344510985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50381256338326119563007323 75571884507489179344510985)
          ·
            refine ⟨56678913380616884508383239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75571884507489179344510985 56678913380616884508383239)
            ·
              refine ⟨85018370070925326762574859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56678913380616884508383239 85018370070925326762574859)
              ·
                refine ⟨127527555106387990143862289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85018370070925326762574859 127527555106387990143862289)
                ·
                  refine ⟨95645666329790992607896717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127527555106387990143862289 95645666329790992607896717)
                  ·
                    refine ⟨35867124873671622227961269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95645666329790992607896717 35867124873671622227961269)
                    ·
                      refine ⟨3362542956906714583871369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35867124873671622227961269 3362542956906714583871369)
                      ·
                        rfl

theorem cell23_6548529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6548529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548529 prefixEnd_6548529 := by exact prefixLift 6548529
  have htrace : WordTrace (prefixWord ++ tailWord_6548529) baseStart_6548529 baseEnd_6548529 := by
    simpa [prefixWord, tailWord_6548529, baseEnd_6548529] using wordTrace_append hprefix tailTrace_6548529
  have hstable : (prefixWord ++ tailWord_6548529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548529).length < 2 ^ (prefixWord ++ tailWord_6548529).sum := by decide
  have hdescent : baseEnd_6548529 < baseStart_6548529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548583 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 6]
def baseStart_6548583 : Nat := 118140960795 + 6548583 * 2 ^ 59
def prefixEnd_6548583 : Nat := 4983230072969 + 3 ^ 40 * 6548583 * 2
def baseEnd_6548583 : Nat := 373618964984673041399569

theorem tailTrace_6548583 : CollatzResearch.WordTrace tailWord_6548583 prefixEnd_6548583 373618964984673041399569 := by
  unfold tailWord_6548583
  simp only [CollatzResearch.WordTrace]
  refine ⟨238846444034609674780426403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159230962689739783186950935 238846444034609674780426403)
  ·
    refine ⟨358269666051914512170639605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238846444034609674780426403 358269666051914512170639605)
    ·
      refine ⟨33587781192366985515997463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 358269666051914512170639605 33587781192366985515997463)
      ·
        refine ⟨50381671788550478273996195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33587781192366985515997463 50381671788550478273996195)
        ·
          refine ⟨75572507682825717410994293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50381671788550478273996195 75572507682825717410994293)
          ·
            refine ⟨7084922595264911007280715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75572507682825717410994293 7084922595264911007280715)
            ·
              refine ⟨10627383892897366510921073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7084922595264911007280715 10627383892897366510921073)
              ·
                refine ⟨7970537919673024883190805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10627383892897366510921073 7970537919673024883190805)
                ·
                  refine ⟨373618964984673041399569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7970537919673024883190805 373618964984673041399569)
                  ·
                    rfl

theorem cell23_6548583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 6].length) (baseStart_6548583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548583 prefixEnd_6548583 := by exact prefixLift 6548583
  have htrace : WordTrace (prefixWord ++ tailWord_6548583) baseStart_6548583 baseEnd_6548583 := by
    simpa [prefixWord, tailWord_6548583, baseEnd_6548583] using wordTrace_append hprefix tailTrace_6548583
  have hstable : (prefixWord ++ tailWord_6548583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548583).length < 2 ^ (prefixWord ++ tailWord_6548583).sum := by decide
  have hdescent : baseEnd_6548583 < baseStart_6548583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548586 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6548586 : Nat := 118140960795 + 6548586 * 2 ^ 59
def prefixEnd_6548586 : Nat := 4983230072969 + 3 ^ 40 * 6548586 * 2
def baseEnd_6548586 : Nat := 3362572225304020860858607

theorem tailTrace_6548586 : CollatzResearch.WordTrace tailWord_6548586 prefixEnd_6548586 3362572225304020860858607 := by
  unfold tailWord_6548586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59711638363399701573196403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159231035635732537528523741 59711638363399701573196403)
  ·
    refine ⟨89567457545099552359794605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59711638363399701573196403 89567457545099552359794605)
    ·
      refine ⟨33587796579412332134922977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89567457545099552359794605 33587796579412332134922977)
      ·
        refine ⟨25190847434559249101192233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33587796579412332134922977 25190847434559249101192233)
        ·
          refine ⟨18893135575919436825894175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25190847434559249101192233 18893135575919436825894175)
          ·
            refine ⟨28339703363879155238841263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18893135575919436825894175 28339703363879155238841263)
            ·
              refine ⟨42509555045818732858261895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28339703363879155238841263 42509555045818732858261895)
              ·
                refine ⟨63764332568728099287392843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42509555045818732858261895 63764332568728099287392843)
                ·
                  refine ⟨95646498853092148931089265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63764332568728099287392843 95646498853092148931089265)
                  ·
                    refine ⟨71734874139819111698316949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95646498853092148931089265 71734874139819111698316949)
                    ·
                      refine ⟨3362572225304020860858607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71734874139819111698316949 3362572225304020860858607)
                      ·
                        rfl

theorem cell23_6548586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6548586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548586 prefixEnd_6548586 := by exact prefixLift 6548586
  have htrace : WordTrace (prefixWord ++ tailWord_6548586) baseStart_6548586 baseEnd_6548586 := by
    simpa [prefixWord, tailWord_6548586, baseEnd_6548586] using wordTrace_append hprefix tailTrace_6548586
  have hstable : (prefixWord ++ tailWord_6548586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548586).length < 2 ^ (prefixWord ++ tailWord_6548586).sum := by decide
  have hdescent : baseEnd_6548586 < baseStart_6548586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548644 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_6548644 : Nat := 118140960795 + 6548644 * 2 ^ 59
def prefixEnd_6548644 : Nat := 4983230072969 + 3 ^ 40 * 6548644 * 2
def baseEnd_6548644 : Nat := 3362602007181981633933341

theorem tailTrace_6548644 : CollatzResearch.WordTrace tailWord_6548644 prefixEnd_6548644 3362602007181981633933341 := by
  unfold tailWord_6548644
  simp only [CollatzResearch.WordTrace]
  refine ⟨119424334443694341099198493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159232445924925788132264657 119424334443694341099198493)
  ·
    refine ⟨44784125416385377912199435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119424334443694341099198493 44784125416385377912199435)
    ·
      refine ⟨67176188124578066868299153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44784125416385377912199435 67176188124578066868299153)
      ·
        refine ⟨50382141093433550151224365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67176188124578066868299153 50382141093433550151224365)
        ·
          refine ⟨18893302910037581306709137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50382141093433550151224365 18893302910037581306709137)
          ·
            refine ⟨14169977182528185980031853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18893302910037581306709137 14169977182528185980031853)
            ·
              refine ⟨5313741443448069742511945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14169977182528185980031853 5313741443448069742511945)
              ·
                refine ⟨3985306082586052306883959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5313741443448069742511945 3985306082586052306883959)
                ·
                  refine ⟨5977959123879078460325939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985306082586052306883959 5977959123879078460325939)
                  ·
                    refine ⟨8966938685818617690488909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977959123879078460325939 8966938685818617690488909)
                    ·
                      refine ⟨3362602007181981633933341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966938685818617690488909 3362602007181981633933341)
                      ·
                        rfl

theorem cell23_6548644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_6548644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548644 prefixEnd_6548644 := by exact prefixLift 6548644
  have htrace : WordTrace (prefixWord ++ tailWord_6548644) baseStart_6548644 baseEnd_6548644 := by
    simpa [prefixWord, tailWord_6548644, baseEnd_6548644] using wordTrace_append hprefix tailTrace_6548644
  have hstable : (prefixWord ++ tailWord_6548644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548644).length < 2 ^ (prefixWord ++ tailWord_6548644).sum := by decide
  have hdescent : baseEnd_6548644 < baseStart_6548644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548670 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_6548670 : Nat := 118140960795 + 6548670 * 2 ^ 59
def prefixEnd_6548670 : Nat := 4983230072969 + 3 ^ 40 * 6548670 * 2
def baseEnd_6548670 : Nat := 3362615357678998532208221

theorem tailTrace_6548670 : CollatzResearch.WordTrace tailWord_6548670 prefixEnd_6548670 3362615357678998532208221 := by
  unfold tailWord_6548670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856202148161811079855433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159233078123529659092562309 29856202148161811079855433)
  ·
    refine ⟨22392151611121358309891575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29856202148161811079855433 22392151611121358309891575)
    ·
      refine ⟨33588227416682037464837363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22392151611121358309891575 33588227416682037464837363)
      ·
        refine ⟨50382341125023056197256045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33588227416682037464837363 50382341125023056197256045)
        ·
          refine ⟨18893377921883646073971017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50382341125023056197256045 18893377921883646073971017)
          ·
            refine ⟨14170033441412734555478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18893377921883646073971017 14170033441412734555478263)
            ·
              refine ⟨21255050162119101833217395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14170033441412734555478263 21255050162119101833217395)
              ·
                refine ⟨31882575243178652749826093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21255050162119101833217395 31882575243178652749826093)
                ·
                  refine ⟨11955965716191994781184785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31882575243178652749826093 11955965716191994781184785)
                  ·
                    refine ⟨8966974287143996085888589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11955965716191994781184785 8966974287143996085888589)
                    ·
                      refine ⟨3362615357678998532208221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966974287143996085888589 3362615357678998532208221)
                      ·
                        rfl

theorem cell23_6548670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_6548670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548670 prefixEnd_6548670 := by exact prefixLift 6548670
  have htrace : WordTrace (prefixWord ++ tailWord_6548670) baseStart_6548670 baseEnd_6548670 := by
    simpa [prefixWord, tailWord_6548670, baseEnd_6548670] using wordTrace_append hprefix tailTrace_6548670
  have hstable : (prefixWord ++ tailWord_6548670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548670).length < 2 ^ (prefixWord ++ tailWord_6548670).sum := by decide
  have hdescent : baseEnd_6548670 < baseStart_6548670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548673 : List Nat := [1, 2, 6, 1, 1, 1, 2, 9]
def baseStart_6548673 : Nat := 118140960795 + 6548673 * 2 ^ 59
def prefixEnd_6548673 : Nat := 4983230072969 + 3 ^ 40 * 6548673 * 2
def baseEnd_6548673 : Nat := 124541366597072667424841

theorem tailTrace_6548673 : CollatzResearch.WordTrace tailWord_6548673 prefixEnd_6548673 124541366597072667424841 := by
  unfold tailWord_6548673
  simp only [CollatzResearch.WordTrace]
  refine ⟨238849726604283620151202673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159233151069522413434135115 238849726604283620151202673)
  ·
    refine ⟨179137294953212715113402005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238849726604283620151202673 179137294953212715113402005)
    ·
      refine ⟨8397060700931846020940719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179137294953212715113402005 8397060700931846020940719)
      ·
        refine ⟨12595591051397769031411079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397060700931846020940719 12595591051397769031411079)
        ·
          refine ⟨18893386577096653547116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595591051397769031411079 18893386577096653547116619)
          ·
            refine ⟨28340079865644980320674929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18893386577096653547116619 28340079865644980320674929)
            ·
              refine ⟨21255059899233735240506197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28340079865644980320674929 21255059899233735240506197)
              ·
                refine ⟨124541366597072667424841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21255059899233735240506197 124541366597072667424841)
                ·
                  rfl

theorem cell23_6548673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 9].length) (baseStart_6548673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548673 prefixEnd_6548673 := by exact prefixLift 6548673
  have htrace : WordTrace (prefixWord ++ tailWord_6548673) baseStart_6548673 baseEnd_6548673 := by
    simpa [prefixWord, tailWord_6548673, baseEnd_6548673] using wordTrace_append hprefix tailTrace_6548673
  have hstable : (prefixWord ++ tailWord_6548673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548673).length < 2 ^ (prefixWord ++ tailWord_6548673).sum := by decide
  have hdescent : baseEnd_6548673 < baseStart_6548673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548683 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 3]
def baseStart_6548683 : Nat := 118140960795 + 6548683 * 2 ^ 59
def prefixEnd_6548683 : Nat := 4983230072969 + 3 ^ 40 * 6548683 * 2
def baseEnd_6548683 : Nat := 3362622032927506981345661

theorem tailTrace_6548683 : CollatzResearch.WordTrace tailWord_6548683 prefixEnd_6548683 3362622032927506981345661 := by
  unfold tailWord_6548683
  simp only [CollatzResearch.WordTrace]
  refine ⟨238850091334247391859066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159233394222831594572711135 238850091334247391859066703)
  ·
    refine ⟨358275137001371087788600055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238850091334247391859066703 358275137001371087788600055)
    ·
      refine ⟨537412705502056631682900083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358275137001371087788600055 537412705502056631682900083)
      ·
        refine ⟨806119058253084947524350125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537412705502056631682900083 806119058253084947524350125)
        ·
          refine ⟨302294646844906855321631297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806119058253084947524350125 302294646844906855321631297)
          ·
            refine ⟨226720985133680141491223473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302294646844906855321631297 226720985133680141491223473)
            ·
              refine ⟨170040738850260106118417605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226720985133680141491223473 170040738850260106118417605)
              ·
                refine ⟨31882638534423769897203301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170040738850260106118417605 31882638534423769897203301)
                ·
                  refine ⟨5977994725204456855725619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31882638534423769897203301 5977994725204456855725619)
                  ·
                    refine ⟨8966992087806685283588429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977994725204456855725619 8966992087806685283588429)
                    ·
                      refine ⟨3362622032927506981345661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8966992087806685283588429 3362622032927506981345661)
                      ·
                        rfl

theorem cell23_6548683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 3].length) (baseStart_6548683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548683 prefixEnd_6548683 := by exact prefixLift 6548683
  have htrace : WordTrace (prefixWord ++ tailWord_6548683) baseStart_6548683 baseEnd_6548683 := by
    simpa [prefixWord, tailWord_6548683, baseEnd_6548683] using wordTrace_append hprefix tailTrace_6548683
  have hstable : (prefixWord ++ tailWord_6548683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548683).length < 2 ^ (prefixWord ++ tailWord_6548683).sum := by decide
  have hdescent : baseEnd_6548683 < baseStart_6548683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548694 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_6548694 : Nat := 118140960795 + 6548694 * 2 ^ 59
def prefixEnd_6548694 : Nat := 4983230072969 + 3 ^ 40 * 6548694 * 2
def baseEnd_6548694 : Nat := 1120875893738235479436037

theorem tailTrace_6548694 : CollatzResearch.WordTrace tailWord_6548694 prefixEnd_6548694 1120875893738235479436037 := by
  unfold tailWord_6548694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928155783575471296107321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159233661691471693825144757 14928155783575471296107321)
  ·
    refine ⟨11196116837681603472080491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14928155783575471296107321 11196116837681603472080491)
    ·
      refine ⟨16794175256522405208120737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11196116837681603472080491 16794175256522405208120737)
      ·
        refine ⟨12595631442391803906090553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16794175256522405208120737 12595631442391803906090553)
        ·
          refine ⟨9446723581793852929567915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595631442391803906090553 9446723581793852929567915)
          ·
            refine ⟨14170085372690779394351873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446723581793852929567915 14170085372690779394351873)
            ·
              refine ⟨10627564029518084545763905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14170085372690779394351873 10627564029518084545763905)
              ·
                refine ⟨7970673022138563409322929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10627564029518084545763905 7970673022138563409322929)
                ·
                  refine ⟨5978004766603922556992197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7970673022138563409322929 5978004766603922556992197)
                  ·
                    refine ⟨1120875893738235479436037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5978004766603922556992197 1120875893738235479436037)
                    ·
                      rfl

theorem cell23_6548694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_6548694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548694 prefixEnd_6548694 := by exact prefixLift 6548694
  have htrace : WordTrace (prefixWord ++ tailWord_6548694) baseStart_6548694 baseEnd_6548694 := by
    simpa [prefixWord, tailWord_6548694, baseEnd_6548694] using wordTrace_append hprefix tailTrace_6548694
  have hstable : (prefixWord ++ tailWord_6548694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548694).length < 2 ^ (prefixWord ++ tailWord_6548694).sum := by decide
  have hdescent : baseEnd_6548694 < baseStart_6548694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548701 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6548701 : Nat := 118140960795 + 6548701 * 2 ^ 59
def prefixEnd_6548701 : Nat := 4983230072969 + 3 ^ 40 * 6548701 * 2
def baseEnd_6548701 : Nat := 3362631275579287910920579

theorem tailTrace_6548701 : CollatzResearch.WordTrace tailWord_6548701 prefixEnd_6548701 3362631275579287910920579 := by
  unfold tailWord_6548701
  simp only [CollatzResearch.WordTrace]
  refine ⟨238850747848182180933221957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159233831898788120622147971 238850747848182180933221957)
  ·
    refine ⟨44784515221534158924979117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238850747848182180933221957 44784515221534158924979117)
    ·
      refine ⟨16794193208075309596867169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44784515221534158924979117 16794193208075309596867169)
      ·
        refine ⟨12595644906056482197650377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16794193208075309596867169 12595644906056482197650377)
        ·
          refine ⟨9446733679542361648237783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595644906056482197650377 9446733679542361648237783)
          ·
            refine ⟨14170100519313542472356675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446733679542361648237783 14170100519313542472356675)
            ·
              refine ⟨21255150778970313708535013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14170100519313542472356675 21255150778970313708535013)
              ·
                refine ⟨3985340771056933820350315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21255150778970313708535013 3985340771056933820350315)
                ·
                  refine ⟨5978011156585400730525473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985340771056933820350315 5978011156585400730525473)
                  ·
                    refine ⟨4483508367439050547894105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5978011156585400730525473 4483508367439050547894105)
                    ·
                      refine ⟨3362631275579287910920579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483508367439050547894105 3362631275579287910920579)
                      ·
                        rfl

theorem cell23_6548701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6548701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548701 prefixEnd_6548701 := by exact prefixLift 6548701
  have htrace : WordTrace (prefixWord ++ tailWord_6548701) baseStart_6548701 baseEnd_6548701 := by
    simpa [prefixWord, tailWord_6548701, baseEnd_6548701] using wordTrace_append hprefix tailTrace_6548701
  have hstable : (prefixWord ++ tailWord_6548701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548701).length < 2 ^ (prefixWord ++ tailWord_6548701).sum := by decide
  have hdescent : baseEnd_6548701 < baseStart_6548701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548716 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_6548716 : Nat := 118140960795 + 6548716 * 2 ^ 59
def prefixEnd_6548716 : Nat := 4983230072969 + 3 ^ 40 * 6548716 * 2
def baseEnd_6548716 : Nat := 1120879659263035117411003

theorem tailTrace_6548716 : CollatzResearch.WordTrace tailWord_6548716 prefixEnd_6548716 1120879659263035117411003 := by
  unfold tailWord_6548716
  simp only [CollatzResearch.WordTrace]
  refine ⟨119425647471563919247509001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159234196628751892330012001 119425647471563919247509001)
  ·
    refine ⟨89569235603672939435631751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119425647471563919247509001 89569235603672939435631751)
    ·
      refine ⟨134353853405509409153447627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89569235603672939435631751 134353853405509409153447627)
      ·
        refine ⟨201530780108264113730171441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134353853405509409153447627 201530780108264113730171441)
        ·
          refine ⟨151148085081198085297628581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201530780108264113730171441 151148085081198085297628581)
          ·
            refine ⟨28340265952724640993305359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151148085081198085297628581 28340265952724640993305359)
            ·
              refine ⟨42510398929086961489958039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28340265952724640993305359 42510398929086961489958039)
              ·
                refine ⟨63765598393630442234937059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42510398929086961489958039 63765598393630442234937059)
                ·
                  refine ⟨95648397590445663352405589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63765598393630442234937059 95648397590445663352405589)
                  ·
                    refine ⟨1120879659263035117411003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95648397590445663352405589 1120879659263035117411003)
                    ·
                      rfl

theorem cell23_6548716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_6548716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548716 prefixEnd_6548716 := by exact prefixLift 6548716
  have htrace : WordTrace (prefixWord ++ tailWord_6548716) baseStart_6548716 baseEnd_6548716 := by
    simpa [prefixWord, tailWord_6548716, baseEnd_6548716] using wordTrace_append hprefix tailTrace_6548716
  have hstable : (prefixWord ++ tailWord_6548716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548716).length < 2 ^ (prefixWord ++ tailWord_6548716).sum := by decide
  have hdescent : baseEnd_6548716 < baseStart_6548716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548717 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6548717 : Nat := 118140960795 + 6548717 * 2 ^ 59
def prefixEnd_6548717 : Nat := 4983230072969 + 3 ^ 40 * 6548717 * 2
def baseEnd_6548717 : Nat := 3362639491269759848320505

theorem tailTrace_6548717 : CollatzResearch.WordTrace tailWord_6548717 prefixEnd_6548717 3362639491269759848320505 := by
  unfold tailWord_6548717
  simp only [CollatzResearch.WordTrace]
  refine ⟨238851331416124215665804405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159234220944082810443869603 238851331416124215665804405)
  ·
    refine ⟨22392312320261645218669163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238851331416124215665804405 22392312320261645218669163)
    ·
      refine ⟨33588468480392467828003745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22392312320261645218669163 33588468480392467828003745)
      ·
        refine ⟨25191351360294350871002809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33588468480392467828003745 25191351360294350871002809)
        ·
          refine ⟨18893513520220763153252107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25191351360294350871002809 18893513520220763153252107)
          ·
            refine ⟨28340270280331144729878161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18893513520220763153252107 28340270280331144729878161)
            ·
              refine ⟨21255202710248358547408621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28340270280331144729878161 21255202710248358547408621)
              ·
                refine ⟨7970701016343134455278233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21255202710248358547408621 7970701016343134455278233)
                ·
                  refine ⟨5978025762257350841458675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7970701016343134455278233 5978025762257350841458675)
                  ·
                    refine ⟨8967038643386026262188013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978025762257350841458675 8967038643386026262188013)
                    ·
                      refine ⟨3362639491269759848320505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8967038643386026262188013 3362639491269759848320505)
                      ·
                        rfl

theorem cell23_6548717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6548717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548717 prefixEnd_6548717 := by exact prefixLift 6548717
  have htrace : WordTrace (prefixWord ++ tailWord_6548717) baseStart_6548717 baseEnd_6548717 := by
    simpa [prefixWord, tailWord_6548717, baseEnd_6548717] using wordTrace_append hprefix tailTrace_6548717
  have hstable : (prefixWord ++ tailWord_6548717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548717).length < 2 ^ (prefixWord ++ tailWord_6548717).sum := by decide
  have hdescent : baseEnd_6548717 < baseStart_6548717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548724 : List Nat := [2, 6, 1, 2, 1, 1, 3, 7]
def baseStart_6548724 : Nat := 118140960795 + 6548724 * 2 ^ 59
def prefixEnd_6548724 : Nat := 4983230072969 + 3 ^ 40 * 6548724 * 2
def baseEnd_6548724 : Nat := 124542336504975604478999

theorem tailTrace_6548724 : CollatzResearch.WordTrace tailWord_6548724 prefixEnd_6548724 124542336504975604478999 := by
  unfold tailWord_6548724
  simp only [CollatzResearch.WordTrace]
  refine ⟨119425793363549427930654613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159234391151399237240872817 119425793363549427930654613)
  ·
    refine ⟨5598084063916379434249435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119425793363549427930654613 5598084063916379434249435)
    ·
      refine ⟨8397126095874569151374153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598084063916379434249435 8397126095874569151374153)
      ·
        refine ⟨6297844571905926863530615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8397126095874569151374153 6297844571905926863530615)
        ·
          refine ⟨9446766857858890295295923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297844571905926863530615 9446766857858890295295923)
          ·
            refine ⟨14170150286788335442943885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446766857858890295295923 14170150286788335442943885)
            ·
              refine ⟨5313806357545625791103957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14170150286788335442943885 5313806357545625791103957)
              ·
                refine ⟨124542336504975604478999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5313806357545625791103957 124542336504975604478999)
                ·
                  rfl

theorem cell23_6548724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 7].length) (baseStart_6548724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548724 prefixEnd_6548724 := by exact prefixLift 6548724
  have htrace : WordTrace (prefixWord ++ tailWord_6548724) baseStart_6548724 baseEnd_6548724 := by
    simpa [prefixWord, tailWord_6548724, baseEnd_6548724] using wordTrace_append hprefix tailTrace_6548724
  have hstable : (prefixWord ++ tailWord_6548724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548724).length < 2 ^ (prefixWord ++ tailWord_6548724).sum := by decide
  have hdescent : baseEnd_6548724 < baseStart_6548724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548736 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_6548736 : Nat := 118140960795 + 6548736 * 2 ^ 59
def prefixEnd_6548736 : Nat := 4983230072969 + 3 ^ 40 * 6548736 * 2
def baseEnd_6548736 : Nat := 3362649247402195273982917

theorem tailTrace_6548736 : CollatzResearch.WordTrace tailWord_6548736 prefixEnd_6548736 3362649247402195273982917 := by
  unfold tailWord_6548736
  simp only [CollatzResearch.WordTrace]
  refine ⟨119426012201527690955373031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159234682935370254607164041 119426012201527690955373031)
  ·
    refine ⟨179139018302291536433059547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119426012201527690955373031 179139018302291536433059547)
    ·
      refine ⟨268708527453437304649589321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179139018302291536433059547 268708527453437304649589321)
      ·
        refine ⟨201531395590077978487191991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268708527453437304649589321 201531395590077978487191991)
        ·
          refine ⟨302297093385116967730787987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201531395590077978487191991 302297093385116967730787987)
          ·
            refine ⟨453445640077675451596181981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302297093385116967730787987 453445640077675451596181981)
            ·
              refine ⟨170042115029128294348568243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453445640077675451596181981 170042115029128294348568243)
              ·
                refine ⟨255063172543692441522852365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170042115029128294348568243 255063172543692441522852365)
                ·
                  refine ⟨95648689703884665571069637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255063172543692441522852365 95648689703884665571069637)
                  ·
                    refine ⟨17934129319478374794575557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95648689703884665571069637 17934129319478374794575557)
                    ·
                      refine ⟨3362649247402195273982917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17934129319478374794575557 3362649247402195273982917)
                      ·
                        rfl

theorem cell23_6548736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_6548736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548736 prefixEnd_6548736 := by exact prefixLift 6548736
  have htrace : WordTrace (prefixWord ++ tailWord_6548736) baseStart_6548736 baseEnd_6548736 := by
    simpa [prefixWord, tailWord_6548736, baseEnd_6548736] using wordTrace_append hprefix tailTrace_6548736
  have hstable : (prefixWord ++ tailWord_6548736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548736).length < 2 ^ (prefixWord ++ tailWord_6548736).sum := by decide
  have hdescent : baseEnd_6548736 < baseStart_6548736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548746 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_6548746 : Nat := 118140960795 + 6548746 * 2 ^ 59
def prefixEnd_6548746 : Nat := 4983230072969 + 3 ^ 40 * 6548746 * 2
def baseEnd_6548746 : Nat := 373628264689860026095319

theorem tailTrace_6548746 : CollatzResearch.WordTrace tailWord_6548746 prefixEnd_6548746 373628264689860026095319 := by
  unfold tailWord_6548746
  simp only [CollatzResearch.WordTrace]
  refine ⟨59713097283254788404652523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159234926088679435745740061 59713097283254788404652523)
  ·
    refine ⟨89569645924882182606978785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59713097283254788404652523 89569645924882182606978785)
    ·
      refine ⟨67177234443661636955234089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89569645924882182606978785 67177234443661636955234089)
      ·
        refine ⟨50382925832746227716425567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67177234443661636955234089 50382925832746227716425567)
        ·
          refine ⟨75574388749119341574638351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50382925832746227716425567 75574388749119341574638351)
          ·
            refine ⟨113361583123679012361957527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75574388749119341574638351 113361583123679012361957527)
            ·
              refine ⟨170042374685518518542936291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113361583123679012361957527 170042374685518518542936291)
              ·
                refine ⟨255063562028277777814404437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170042374685518518542936291 255063562028277777814404437)
                ·
                  refine ⟨373628264689860026095319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 255063562028277777814404437 373628264689860026095319)
                  ·
                    rfl

theorem cell23_6548746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_6548746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548746 prefixEnd_6548746 := by exact prefixLift 6548746
  have htrace : WordTrace (prefixWord ++ tailWord_6548746) baseStart_6548746 baseEnd_6548746 := by
    simpa [prefixWord, tailWord_6548746, baseEnd_6548746] using wordTrace_append hprefix tailTrace_6548746
  have hstable : (prefixWord ++ tailWord_6548746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548746).length < 2 ^ (prefixWord ++ tailWord_6548746).sum := by decide
  have hdescent : baseEnd_6548746 < baseStart_6548746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548833 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_6548833 : Nat := 118140960795 + 6548833 * 2 ^ 59
def prefixEnd_6548833 : Nat := 4983230072969 + 3 ^ 40 * 6548833 * 2
def baseEnd_6548833 : Nat := 3362699055025681394469971

theorem tailTrace_6548833 : CollatzResearch.WordTrace tailWord_6548833 prefixEnd_6548833 3362699055025681394469971 := by
  unfold tailWord_6548833
  simp only [CollatzResearch.WordTrace]
  refine ⟨238855562283703967477027153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159237041522469311651351435 238855562283703967477027153)
  ·
    refine ⟨179141671712777975607770365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238855562283703967477027153 179141671712777975607770365)
    ·
      refine ⟨67178126892291740852913887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179141671712777975607770365 67178126892291740852913887)
      ·
        refine ⟨100767190338437611279370831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67178126892291740852913887 100767190338437611279370831)
        ·
          refine ⟨151150785507656416919056247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100767190338437611279370831 151150785507656416919056247)
          ·
            refine ⟨226726178261484625378584371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151150785507656416919056247 226726178261484625378584371)
            ·
              refine ⟨340089267392226938067876557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226726178261484625378584371 340089267392226938067876557)
              ·
                refine ⟨127533475272085101775453709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340089267392226938067876557 127533475272085101775453709)
                ·
                  refine ⟨47825053227031913165795141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127533475272085101775453709 47825053227031913165795141)
                  ·
                    refine ⟨8967197480068483718586589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47825053227031913165795141 8967197480068483718586589)
                    ·
                      refine ⟨3362699055025681394469971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8967197480068483718586589 3362699055025681394469971)
                      ·
                        rfl

theorem cell23_6548833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_6548833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548833 prefixEnd_6548833 := by exact prefixLift 6548833
  have htrace : WordTrace (prefixWord ++ tailWord_6548833) baseStart_6548833 baseEnd_6548833 := by
    simpa [prefixWord, tailWord_6548833, baseEnd_6548833] using wordTrace_append hprefix tailTrace_6548833
  have hstable : (prefixWord ++ tailWord_6548833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548833).length < 2 ^ (prefixWord ++ tailWord_6548833).sum := by decide
  have hdescent : baseEnd_6548833 < baseStart_6548833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548900 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_6548900 : Nat := 118140960795 + 6548900 * 2 ^ 59
def prefixEnd_6548900 : Nat := 4983230072969 + 3 ^ 40 * 6548900 * 2
def baseEnd_6548900 : Nat := 1120911152743177544110721

theorem tailTrace_6548900 : CollatzResearch.WordTrace tailWord_6548900 prefixEnd_6548900 1120911152743177544110721 := by
  unfold tailWord_6548900
  simp only [CollatzResearch.WordTrace]
  refine ⟨119429002987230618959858077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159238670649640825279810769 119429002987230618959858077)
  ·
    refine ⟨44785876120211482109946779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119429002987230618959858077 44785876120211482109946779)
    ·
      refine ⟨67178814180317223164920169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44785876120211482109946779 67178814180317223164920169)
      ·
        refine ⟨50384110635237917373690127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67178814180317223164920169 50384110635237917373690127)
        ·
          refine ⟨75576165952856876060535191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50384110635237917373690127 75576165952856876060535191)
          ·
            refine ⟨113364248929285314090802787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75576165952856876060535191 113364248929285314090802787)
            ·
              refine ⟨170046373393927971136204181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113364248929285314090802787 170046373393927971136204181)
              ·
                refine ⟨7970923752840373647009571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170046373393927971136204181 7970923752840373647009571)
                ·
                  refine ⟨11956385629260560470514357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970923752840373647009571 11956385629260560470514357)
                  ·
                    refine ⟨1120911152743177544110721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11956385629260560470514357 1120911152743177544110721)
                    ·
                      rfl

theorem cell23_6548900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_6548900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548900 prefixEnd_6548900 := by exact prefixLift 6548900
  have htrace : WordTrace (prefixWord ++ tailWord_6548900) baseStart_6548900 baseEnd_6548900 := by
    simpa [prefixWord, tailWord_6548900, baseEnd_6548900] using wordTrace_append hprefix tailTrace_6548900
  have hstable : (prefixWord ++ tailWord_6548900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548900).length < 2 ^ (prefixWord ++ tailWord_6548900).sum := by decide
  have hdescent : baseEnd_6548900 < baseStart_6548900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548917 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6548917 : Nat := 118140960795 + 6548917 * 2 ^ 59
def prefixEnd_6548917 : Nat := 4983230072969 + 3 ^ 40 * 6548917 * 2
def baseEnd_6548917 : Nat := 1120914062466886355273195

theorem tailTrace_6548917 : CollatzResearch.WordTrace tailWord_6548917 prefixEnd_6548917 1120914062466886355273195 := by
  unfold tailWord_6548917
  simp only [CollatzResearch.WordTrace]
  refine ⟨238858626015399649823085005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159239084010266433215390003 238858626015399649823085005)
  ·
    refine ⟨89571984755774868683656877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238858626015399649823085005 89571984755774868683656877)
    ·
      refine ⟨33589494283415575756371329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89571984755774868683656877 33589494283415575756371329)
      ·
        refine ⟨25192120712561681817278497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33589494283415575756371329 25192120712561681817278497)
        ·
          refine ⟨18894090534421261362958873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25192120712561681817278497 18894090534421261362958873)
          ·
            refine ⟨14170567900815946022219155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18894090534421261362958873 14170567900815946022219155)
            ·
              refine ⟨21255851851223919033328733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14170567900815946022219155 21255851851223919033328733)
              ·
                refine ⟨7970944444208969637498275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21255851851223919033328733 7970944444208969637498275)
                ·
                  refine ⟨11956416666313454456247413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970944444208969637498275 11956416666313454456247413)
                  ·
                    refine ⟨1120914062466886355273195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11956416666313454456247413 1120914062466886355273195)
                    ·
                      rfl

theorem cell23_6548917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6548917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548917 prefixEnd_6548917 := by exact prefixLift 6548917
  have htrace : WordTrace (prefixWord ++ tailWord_6548917) baseStart_6548917 baseEnd_6548917 := by
    simpa [prefixWord, tailWord_6548917, baseEnd_6548917] using wordTrace_append hprefix tailTrace_6548917
  have hstable : (prefixWord ++ tailWord_6548917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548917).length < 2 ^ (prefixWord ++ tailWord_6548917).sum := by decide
  have hdescent : baseEnd_6548917 < baseStart_6548917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548933 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_6548933 : Nat := 118140960795 + 6548933 * 2 ^ 59
def prefixEnd_6548933 : Nat := 4983230072969 + 3 ^ 40 * 6548933 * 2
def baseEnd_6548933 : Nat := 3362750403091131003219511

theorem tailTrace_6548933 : CollatzResearch.WordTrace tailWord_6548933 prefixEnd_6548933 3362750403091131003219511 := by
  unfold tailWord_6548933
  simp only [CollatzResearch.WordTrace]
  refine ⟨238859209583341684555667453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159239473055561123037111635 238859209583341684555667453)
  ·
    refine ⟨89572203593753131708375295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238859209583341684555667453 89572203593753131708375295)
    ·
      refine ⟨134358305390629697562562943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89572203593753131708375295 134358305390629697562562943)
      ·
        refine ⟨201537458085944546343844415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134358305390629697562562943 201537458085944546343844415)
        ·
          refine ⟨302306187128916819515766623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201537458085944546343844415 302306187128916819515766623)
          ·
            refine ⟨453459280693375229273649935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302306187128916819515766623 453459280693375229273649935)
            ·
              refine ⟨680188921040062843910474903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453459280693375229273649935 680188921040062843910474903)
              ·
                refine ⟨1020283381560094265865712355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680188921040062843910474903 1020283381560094265865712355)
                ·
                  refine ⟨1530425072340141398798568533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020283381560094265865712355 1530425072340141398798568533)
                  ·
                    refine ⟨17934668816486032017170725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1530425072340141398798568533 17934668816486032017170725)
                    ·
                      refine ⟨3362750403091131003219511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17934668816486032017170725 3362750403091131003219511)
                      ·
                        rfl

theorem cell23_6548933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_6548933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548933 prefixEnd_6548933 := by exact prefixLift 6548933
  have htrace : WordTrace (prefixWord ++ tailWord_6548933) baseStart_6548933 baseEnd_6548933 := by
    simpa [prefixWord, tailWord_6548933, baseEnd_6548933] using wordTrace_append hprefix tailTrace_6548933
  have hstable : (prefixWord ++ tailWord_6548933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548933).length < 2 ^ (prefixWord ++ tailWord_6548933).sum := by decide
  have hdescent : baseEnd_6548933 < baseStart_6548933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548940 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_6548940 : Nat := 118140960795 + 6548940 * 2 ^ 59
def prefixEnd_6548940 : Nat := 4983230072969 + 3 ^ 40 * 6548940 * 2
def baseEnd_6548940 : Nat := 3362753997455712475831979

theorem tailTrace_6548940 : CollatzResearch.WordTrace tailWord_6548940 prefixEnd_6548940 3362753997455712475831979 := by
  unfold tailWord_6548940
  simp only [CollatzResearch.WordTrace]
  refine ⟨119429732447158162375586137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159239643262877549834114849 119429732447158162375586137)
  ·
    refine ⟨89572299335368621781689603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119429732447158162375586137 89572299335368621781689603)
    ·
      refine ⟨134358449003052932672534405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89572299335368621781689603 134358449003052932672534405)
      ·
        refine ⟨25192209188072424876100201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134358449003052932672534405 25192209188072424876100201)
        ·
          refine ⟨18894156891054318657075151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25192209188072424876100201 18894156891054318657075151)
          ·
            refine ⟨28341235336581477985612727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894156891054318657075151 28341235336581477985612727)
            ·
              refine ⟨42511853004872216978419091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28341235336581477985612727 42511853004872216978419091)
              ·
                refine ⟨63767779507308325467628637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42511853004872216978419091 63767779507308325467628637)
                ·
                  refine ⟨23912917315240622050360739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63767779507308325467628637 23912917315240622050360739)
                  ·
                    refine ⟨35869375972860933075541109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23912917315240622050360739 35869375972860933075541109)
                    ·
                      refine ⟨3362753997455712475831979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35869375972860933075541109 3362753997455712475831979)
                      ·
                        rfl

theorem cell23_6548940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_6548940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548940 prefixEnd_6548940 := by exact prefixLift 6548940
  have htrace : WordTrace (prefixWord ++ tailWord_6548940) baseStart_6548940 baseEnd_6548940 := by
    simpa [prefixWord, tailWord_6548940, baseEnd_6548940] using wordTrace_append hprefix tailTrace_6548940
  have hstable : (prefixWord ++ tailWord_6548940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548940).length < 2 ^ (prefixWord ++ tailWord_6548940).sum := by decide
  have hdescent : baseEnd_6548940 < baseStart_6548940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548954 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_6548954 : Nat := 118140960795 + 6548954 * 2 ^ 59
def prefixEnd_6548954 : Nat := 4983230072969 + 3 ^ 40 * 6548954 * 2
def baseEnd_6548954 : Nat := 3362761186184875421056915

theorem tailTrace_6548954 : CollatzResearch.WordTrace tailWord_6548954 prefixEnd_6548954 3362761186184875421056915 := by
  unfold tailWord_6548954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59714993879066401285545479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159239983677510403428121277 59714993879066401285545479)
  ·
    refine ⟨89572490818599601928318219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59714993879066401285545479 89572490818599601928318219)
    ·
      refine ⟨134358736227899402892477329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89572490818599601928318219 134358736227899402892477329)
      ·
        refine ⟨100769052170924552169357997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134358736227899402892477329 100769052170924552169357997)
        ·
          refine ⟨37788394564096707063509249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100769052170924552169357997 37788394564096707063509249)
          ·
            refine ⟨28341295923072530297631937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37788394564096707063509249 28341295923072530297631937)
            ·
              refine ⟨21255971942304397723223953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28341295923072530297631937 21255971942304397723223953)
              ·
                refine ⟨15941978956728298292417965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21255971942304397723223953 15941978956728298292417965)
                ·
                  refine ⟨5978242108773111859656737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15941978956728298292417965 5978242108773111859656737)
                  ·
                    refine ⟨4483681581579833894742553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5978242108773111859656737 4483681581579833894742553)
                    ·
                      refine ⟨3362761186184875421056915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483681581579833894742553 3362761186184875421056915)
                      ·
                        rfl

theorem cell23_6548954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_6548954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548954 prefixEnd_6548954 := by exact prefixLift 6548954
  have htrace : WordTrace (prefixWord ++ tailWord_6548954) baseStart_6548954 baseEnd_6548954 := by
    simpa [prefixWord, tailWord_6548954, baseEnd_6548954] using wordTrace_append hprefix tailTrace_6548954
  have hstable : (prefixWord ++ tailWord_6548954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548954).length < 2 ^ (prefixWord ++ tailWord_6548954).sum := by decide
  have hdescent : baseEnd_6548954 < baseStart_6548954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6548997 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_6548997 : Nat := 118140960795 + 6548997 * 2 ^ 59
def prefixEnd_6548997 : Nat := 4983230072969 + 3 ^ 40 * 6548997 * 2
def baseEnd_6548997 : Nat := 3362783265853018752819217

theorem tailTrace_6548997 : CollatzResearch.WordTrace tailWord_6548997 prefixEnd_6548997 3362783265853018752819217 := by
  unfold tailWord_6548997
  simp only [CollatzResearch.WordTrace]
  refine ⟨238861543855109823485997245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159241029236739882323998163 238861543855109823485997245)
  ·
    refine ⟨89573078945666183807248967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238861543855109823485997245 89573078945666183807248967)
    ·
      refine ⟨134359618418499275710873451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89573078945666183807248967 134359618418499275710873451)
      ·
        refine ⟨201539427627748913566310177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134359618418499275710873451 201539427627748913566310177)
        ·
          refine ⟨151154570720811685174732633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201539427627748913566310177 151154570720811685174732633)
          ·
            refine ⟨113365928040608763881049475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151154570720811685174732633 113365928040608763881049475)
            ·
              refine ⟨170048892060913145821574213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113365928040608763881049475 170048892060913145821574213)
              ·
                refine ⟨31884167261421214841545165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170048892060913145821574213 31884167261421214841545165)
                ·
                  refine ⟨11956562723032955565579437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31884167261421214841545165 11956562723032955565579437)
                  ·
                    refine ⟨4483711021137358337092289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11956562723032955565579437 4483711021137358337092289)
                    ·
                      refine ⟨3362783265853018752819217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4483711021137358337092289 3362783265853018752819217)
                      ·
                        rfl

theorem cell23_6548997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_6548997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6548997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6548997 prefixEnd_6548997 := by exact prefixLift 6548997
  have htrace : WordTrace (prefixWord ++ tailWord_6548997) baseStart_6548997 baseEnd_6548997 := by
    simpa [prefixWord, tailWord_6548997, baseEnd_6548997] using wordTrace_append hprefix tailTrace_6548997
  have hstable : (prefixWord ++ tailWord_6548997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6548997).length < 2 ^ (prefixWord ++ tailWord_6548997).sum := by decide
  have hdescent : baseEnd_6548997 < baseStart_6548997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6548997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549005 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6549005 : Nat := 118140960795 + 6549005 * 2 ^ 59
def prefixEnd_6549005 : Nat := 4983230072969 + 3 ^ 40 * 6549005 * 2
def baseEnd_6549005 : Nat := 3362787373698254721519181

theorem tailTrace_6549005 : CollatzResearch.WordTrace tailWord_6549005 prefixEnd_6549005 3362787373698254721519181 := by
  unfold tailWord_6549005
  simp only [CollatzResearch.WordTrace]
  refine ⟨238861835639080840852288469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159241223759387227234858979 238861835639080840852288469)
  ·
    refine ⟨5598324272790957207475511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 238861835639080840852288469 5598324272790957207475511)
    ·
      refine ⟨8397486409186435811213267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598324272790957207475511 8397486409186435811213267)
      ·
        refine ⟨12596229613779653716819901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397486409186435811213267 12596229613779653716819901)
        ·
          refine ⟨4723586105167370143807463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12596229613779653716819901 4723586105167370143807463)
          ·
            refine ⟨7085379157751055215711195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723586105167370143807463 7085379157751055215711195)
            ·
              refine ⟨10628068736626582823566793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085379157751055215711195 10628068736626582823566793)
              ·
                refine ⟨7971051552469937117675095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10628068736626582823566793 7971051552469937117675095)
                ·
                  refine ⟨11956577328704905676512643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971051552469937117675095 11956577328704905676512643)
                  ·
                    refine ⟨17934865993057358514768965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11956577328704905676512643 17934865993057358514768965)
                    ·
                      refine ⟨3362787373698254721519181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17934865993057358514768965 3362787373698254721519181)
                      ·
                        rfl

theorem cell23_6549005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6549005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549005 prefixEnd_6549005 := by exact prefixLift 6549005
  have htrace : WordTrace (prefixWord ++ tailWord_6549005) baseStart_6549005 baseEnd_6549005 := by
    simpa [prefixWord, tailWord_6549005, baseEnd_6549005] using wordTrace_append hprefix tailTrace_6549005
  have hstable : (prefixWord ++ tailWord_6549005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549005).length < 2 ^ (prefixWord ++ tailWord_6549005).sum := by decide
  have hdescent : baseEnd_6549005 < baseStart_6549005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549040 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_6549040 : Nat := 118140960795 + 6549040 * 2 ^ 59
def prefixEnd_6549040 : Nat := 4983230072969 + 3 ^ 40 * 6549040 * 2
def baseEnd_6549040 : Nat := 3362805345521162084581519

theorem tailTrace_6549040 : CollatzResearch.WordTrace tailWord_6549040 prefixEnd_6549040 3362805345521162084581519 := by
  unfold tailWord_6549040
  simp only [CollatzResearch.WordTrace]
  refine ⟨119431556096977020914906287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159242074795969361219875049 119431556096977020914906287)
  ·
    refine ⟨179147334145465531372359431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119431556096977020914906287 179147334145465531372359431)
    ·
      refine ⟨268721001218198297058539147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179147334145465531372359431 268721001218198297058539147)
      ·
        refine ⟨403081501827297445587808721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268721001218198297058539147 403081501827297445587808721)
        ·
          refine ⟨302311126370473084190856541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403081501827297445587808721 302311126370473084190856541)
          ·
            refine ⟨113366672388927406571571203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302311126370473084190856541 113366672388927406571571203)
            ·
              refine ⟨170050008583391109857356805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113366672388927406571571203 170050008583391109857356805)
              ·
                refine ⟨31884376609385833098254401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170050008583391109857356805 31884376609385833098254401)
                ·
                  refine ⟨23913282457039374823690801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31884376609385833098254401 23913282457039374823690801)
                  ·
                    refine ⟨17934961842779531117768101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23913282457039374823690801 17934961842779531117768101)
                    ·
                      refine ⟨3362805345521162084581519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17934961842779531117768101 3362805345521162084581519)
                      ·
                        rfl

theorem cell23_6549040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_6549040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549040 prefixEnd_6549040 := by exact prefixLift 6549040
  have htrace : WordTrace (prefixWord ++ tailWord_6549040) baseStart_6549040 baseEnd_6549040 := by
    simpa [prefixWord, tailWord_6549040, baseEnd_6549040] using wordTrace_append hprefix tailTrace_6549040
  have hstable : (prefixWord ++ tailWord_6549040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549040).length < 2 ^ (prefixWord ++ tailWord_6549040).sum := by decide
  have hdescent : baseEnd_6549040 < baseStart_6549040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549050 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_6549050 : Nat := 118140960795 + 6549050 * 2 ^ 59
def prefixEnd_6549050 : Nat := 4983230072969 + 3 ^ 40 * 6549050 * 2
def baseEnd_6549050 : Nat := 373645608925300782828497

theorem tailTrace_6549050 : CollatzResearch.WordTrace tailWord_6549050 prefixEnd_6549050 373645608925300782828497 := by
  unfold tailWord_6549050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59715869230979453384419151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159242317949278542358451069 59715869230979453384419151)
  ·
    refine ⟨89573803846469180076628727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59715869230979453384419151 89573803846469180076628727)
    ·
      refine ⟨134360705769703770114943091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89573803846469180076628727 134360705769703770114943091)
      ·
        refine ⟨201541058654555655172414637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134360705769703770114943091 201541058654555655172414637)
        ·
          refine ⟨75577896995458370689655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201541058654555655172414637 75577896995458370689655489)
          ·
            refine ⟨56683422746593778017241617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75577896995458370689655489 56683422746593778017241617)
            ·
              refine ⟨42512567059945333512931213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56683422746593778017241617 42512567059945333512931213)
              ·
                refine ⟨15942212647479500067349205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42512567059945333512931213 15942212647479500067349205)
                ·
                  refine ⟨373645608925300782828497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15942212647479500067349205 373645608925300782828497)
                  ·
                    rfl

theorem cell23_6549050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_6549050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549050 prefixEnd_6549050 := by exact prefixLift 6549050
  have htrace : WordTrace (prefixWord ++ tailWord_6549050) baseStart_6549050 baseEnd_6549050 := by
    simpa [prefixWord, tailWord_6549050, baseEnd_6549050] using wordTrace_append hprefix tailTrace_6549050
  have hstable : (prefixWord ++ tailWord_6549050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549050).length < 2 ^ (prefixWord ++ tailWord_6549050).sum := by decide
  have hdescent : baseEnd_6549050 < baseStart_6549050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549057 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6549057 : Nat := 118140960795 + 6549057 * 2 ^ 59
def prefixEnd_6549057 : Nat := 4983230072969 + 3 ^ 40 * 6549057 * 2
def baseEnd_6549057 : Nat := 3362814074692288518068941

theorem tailTrace_6549057 : CollatzResearch.WordTrace tailWord_6549057 prefixEnd_6549057 3362814074692288518068941 := by
  unfold tailWord_6549057
  simp only [CollatzResearch.WordTrace]
  refine ⟨238863732234892453733181425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159242488156594969155454283 238863732234892453733181425)
  ·
    refine ⟨179147799176169340299886069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238863732234892453733181425 179147799176169340299886069)
    ·
      refine ⟨16795106172765875653114319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179147799176169340299886069 16795106172765875653114319)
      ·
        refine ⟨25192659259148813479671479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16795106172765875653114319 25192659259148813479671479)
        ·
          refine ⟨37788988888723220219507219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25192659259148813479671479 37788988888723220219507219)
          ·
            refine ⟨56683483333084830329260829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37788988888723220219507219 56683483333084830329260829)
            ·
              refine ⟨21256306249906811373472811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56683483333084830329260829 21256306249906811373472811)
              ·
                refine ⟨31884459374860217060209217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21256306249906811373472811 31884459374860217060209217)
                ·
                  refine ⟨23913344531145162795156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31884459374860217060209217 23913344531145162795156913)
                  ·
                    refine ⟨17935008398358872096367685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23913344531145162795156913 17935008398358872096367685)
                    ·
                      refine ⟨3362814074692288518068941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17935008398358872096367685 3362814074692288518068941)
                      ·
                        rfl

theorem cell23_6549057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6549057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549057 prefixEnd_6549057 := by exact prefixLift 6549057
  have htrace : WordTrace (prefixWord ++ tailWord_6549057) baseStart_6549057 baseEnd_6549057 := by
    simpa [prefixWord, tailWord_6549057, baseEnd_6549057] using wordTrace_append hprefix tailTrace_6549057
  have hstable : (prefixWord ++ tailWord_6549057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549057).length < 2 ^ (prefixWord ++ tailWord_6549057).sum := by decide
  have hdescent : baseEnd_6549057 < baseStart_6549057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549084 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 5]
def baseStart_6549084 : Nat := 118140960795 + 6549084 * 2 ^ 59
def prefixEnd_6549084 : Nat := 4983230072969 + 3 ^ 40 * 6549084 * 2
def baseEnd_6549084 : Nat := 373647548741106656936813

theorem tailTrace_6549084 : CollatzResearch.WordTrace tailWord_6549084 prefixEnd_6549084 373647548741106656936813 := by
  unfold tailWord_6549084
  simp only [CollatzResearch.WordTrace]
  refine ⟨119432358502897318672207153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159243144670529758229609537 119432358502897318672207153)
  ·
    refine ⟨89574268877172989004155365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119432358502897318672207153 89574268877172989004155365)
    ·
      refine ⟨16795175414469935438279131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89574268877172989004155365 16795175414469935438279131)
      ·
        refine ⟨25192763121704903157418697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16795175414469935438279131 25192763121704903157418697)
        ·
          refine ⟨18894572341278677368064023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25192763121704903157418697 18894572341278677368064023)
          ·
            refine ⟨28341858511918016052096035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894572341278677368064023 28341858511918016052096035)
            ·
              refine ⟨42512787767877024078144053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28341858511918016052096035 42512787767877024078144053)
              ·
                refine ⟨3985573853238471007326005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42512787767877024078144053 3985573853238471007326005)
                ·
                  refine ⟨373647548741106656936813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3985573853238471007326005 373647548741106656936813)
                  ·
                    rfl

theorem cell23_6549084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_6549084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549084 prefixEnd_6549084 := by exact prefixLift 6549084
  have htrace : WordTrace (prefixWord ++ tailWord_6549084) baseStart_6549084 baseEnd_6549084 := by
    simpa [prefixWord, tailWord_6549084, baseEnd_6549084] using wordTrace_append hprefix tailTrace_6549084
  have hstable : (prefixWord ++ tailWord_6549084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549084).length < 2 ^ (prefixWord ++ tailWord_6549084).sum := by decide
  have hdescent : baseEnd_6549084 < baseStart_6549084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549117 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_6549117 : Nat := 118140960795 + 6549117 * 2 ^ 59
def prefixEnd_6549117 : Nat := 4983230072969 + 3 ^ 40 * 6549117 * 2
def baseEnd_6549117 : Nat := 3362844883531558283318665

theorem tailTrace_6549117 : CollatzResearch.WordTrace tailWord_6549117 prefixEnd_6549117 3362844883531558283318665 := by
  unfold tailWord_6549117
  simp only [CollatzResearch.WordTrace]
  refine ⟨238865920614675083980365605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159243947076450055986910403 238865920614675083980365605)
  ·
    refine ⟨44787360115251578246318551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238865920614675083980365605 44787360115251578246318551)
    ·
      refine ⟨67181040172877367369477827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44787360115251578246318551 67181040172877367369477827)
      ·
        refine ⟨100771560259316051054216741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67181040172877367369477827 100771560259316051054216741)
        ·
          refine ⟨18894667548621759572665639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100771560259316051054216741 18894667548621759572665639)
          ·
            refine ⟨28342001322932639358998459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894667548621759572665639 28342001322932639358998459)
            ·
              refine ⟨42513001984398959038497689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28342001322932639358998459 42513001984398959038497689)
              ·
                refine ⟨31884751488299219278873267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42513001984398959038497689 31884751488299219278873267)
                ·
                  refine ⟨47827127232448828918309901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31884751488299219278873267 47827127232448828918309901)
                  ·
                    refine ⟨17935172712168310844366213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47827127232448828918309901 17935172712168310844366213)
                    ·
                      refine ⟨3362844883531558283318665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17935172712168310844366213 3362844883531558283318665)
                      ·
                        rfl

theorem cell23_6549117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_6549117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549117 prefixEnd_6549117 := by exact prefixLift 6549117
  have htrace : WordTrace (prefixWord ++ tailWord_6549117) baseStart_6549117 baseEnd_6549117 := by
    simpa [prefixWord, tailWord_6549117, baseEnd_6549117] using wordTrace_append hprefix tailTrace_6549117
  have hstable : (prefixWord ++ tailWord_6549117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549117).length < 2 ^ (prefixWord ++ tailWord_6549117).sum := by decide
  have hdescent : baseEnd_6549117 < baseStart_6549117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549151 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6549151 : Nat := 118140960795 + 6549151 * 2 ^ 59
def prefixEnd_6549151 : Nat := 4983230072969 + 3 ^ 40 * 6549151 * 2
def baseEnd_6549151 : Nat := 3362862341873811150293509

theorem tailTrace_6549151 : CollatzResearch.WordTrace tailWord_6549151 prefixEnd_6549151 3362862341873811150293509 := by
  unfold tailWord_6549151
  simp only [CollatzResearch.WordTrace]
  refine ⟨238867160696551907787103307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159244773797701271858068871 238867160696551907787103307)
  ·
    refine ⟨358300741044827861680654961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238867160696551907787103307 358300741044827861680654961)
    ·
      refine ⟨268725555783620896260491221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358300741044827861680654961 268725555783620896260491221)
      ·
        refine ⟨6298255213678614756105263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 268725555783620896260491221 6298255213678614756105263)
        ·
          refine ⟨9447382820517922134157895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298255213678614756105263 9447382820517922134157895)
          ·
            refine ⟨14171074230776883201236843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447382820517922134157895 14171074230776883201236843)
            ·
              refine ⟨21256611346165324801855265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14171074230776883201236843 21256611346165324801855265)
              ·
                refine ⟨15942458509623993601391449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21256611346165324801855265 15942458509623993601391449)
                ·
                  refine ⟨11956843882217995201043587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15942458509623993601391449 11956843882217995201043587)
                  ·
                    refine ⟨17935265823326992801565381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11956843882217995201043587 17935265823326992801565381)
                    ·
                      refine ⟨3362862341873811150293509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17935265823326992801565381 3362862341873811150293509)
                      ·
                        rfl

theorem cell23_6549151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6549151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549151 prefixEnd_6549151 := by exact prefixLift 6549151
  have htrace : WordTrace (prefixWord ++ tailWord_6549151) baseStart_6549151 baseEnd_6549151 := by
    simpa [prefixWord, tailWord_6549151, baseEnd_6549151] using wordTrace_append hprefix tailTrace_6549151
  have hstable : (prefixWord ++ tailWord_6549151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549151).length < 2 ^ (prefixWord ++ tailWord_6549151).sum := by decide
  have hdescent : baseEnd_6549151 < baseStart_6549151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549184 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_6549184 : Nat := 118140960795 + 6549184 * 2 ^ 59
def prefixEnd_6549184 : Nat := 4983230072969 + 3 ^ 40 * 6549184 * 2
def baseEnd_6549184 : Nat := 3362879286735409521180857

theorem tailTrace_6549184 : CollatzResearch.WordTrace tailWord_6549184 prefixEnd_6549184 3362879286735409521180857 := by
  unfold tailWord_6549184
  simp only [CollatzResearch.WordTrace]
  refine ⟨119434182152716177211527303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159245576203621569615369737 119434182152716177211527303)
  ·
    refine ⟨179151273229074265817290955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119434182152716177211527303 179151273229074265817290955)
    ·
      refine ⟨268726909843611398725936433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179151273229074265817290955 268726909843611398725936433)
      ·
        refine ⟨201545182382708549044452325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268726909843611398725936433 201545182382708549044452325)
        ·
          refine ⟨37789721696757852945834811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201545182382708549044452325 37789721696757852945834811)
          ·
            refine ⟨56684582545136779418752217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37789721696757852945834811 56684582545136779418752217)
            ·
              refine ⟨42513436908852584564064163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56684582545136779418752217 42513436908852584564064163)
              ·
                refine ⟨63770155363278876846096245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42513436908852584564064163 63770155363278876846096245)
                ·
                  refine ⟨5978452065307394704321523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63770155363278876846096245 5978452065307394704321523)
                  ·
                    refine ⟨8967678097961092056482285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978452065307394704321523 8967678097961092056482285)
                    ·
                      refine ⟨3362879286735409521180857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8967678097961092056482285 3362879286735409521180857)
                      ·
                        rfl

theorem cell23_6549184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_6549184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549184 prefixEnd_6549184 := by exact prefixLift 6549184
  have htrace : WordTrace (prefixWord ++ tailWord_6549184) baseStart_6549184 baseEnd_6549184 := by
    simpa [prefixWord, tailWord_6549184, baseEnd_6549184] using wordTrace_append hprefix tailTrace_6549184
  have hstable : (prefixWord ++ tailWord_6549184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549184).length < 2 ^ (prefixWord ++ tailWord_6549184).sum := by decide
  have hdescent : baseEnd_6549184 < baseStart_6549184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549212 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6549212 : Nat := 118140960795 + 6549212 * 2 ^ 59
def prefixEnd_6549212 : Nat := 4983230072969 + 3 ^ 40 * 6549212 * 2
def baseEnd_6549212 : Nat := 1120964554731245137210243

theorem tailTrace_6549212 : CollatzResearch.WordTrace tailWord_6549212 prefixEnd_6549212 1120964554731245137210243 := by
  unfold tailWord_6549212
  simp only [CollatzResearch.WordTrace]
  refine ⟨119434692774665457602536945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159246257032887276803382593 119434692774665457602536945)
  ·
    refine ⟨89576019580999093201902709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119434692774665457602536945 89576019580999093201902709)
    ·
      refine ⟨8397751835718664987678379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89576019580999093201902709 8397751835718664987678379)
      ·
        refine ⟨12596627753577997481517569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397751835718664987678379 12596627753577997481517569)
        ·
          refine ⟨9447470815183498111138177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12596627753577997481517569 9447470815183498111138177)
          ·
            refine ⟨7085603111387623583353633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9447470815183498111138177 7085603111387623583353633)
            ·
              refine ⟨5314202333540717687515225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7085603111387623583353633 5314202333540717687515225)
              ·
                refine ⟨3985651750155538265636419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314202333540717687515225 3985651750155538265636419)
                ·
                  refine ⟨5978477625233307398454629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985651750155538265636419 5978477625233307398454629)
                  ·
                    refine ⟨1120964554731245137210243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5978477625233307398454629 1120964554731245137210243)
                    ·
                      rfl

theorem cell23_6549212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6549212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549212 prefixEnd_6549212 := by exact prefixLift 6549212
  have htrace : WordTrace (prefixWord ++ tailWord_6549212) baseStart_6549212 baseEnd_6549212 := by
    simpa [prefixWord, tailWord_6549212, baseEnd_6549212] using wordTrace_append hprefix tailTrace_6549212
  have hstable : (prefixWord ++ tailWord_6549212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549212).length < 2 ^ (prefixWord ++ tailWord_6549212).sum := by decide
  have hdescent : baseEnd_6549212 < baseStart_6549212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549224 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6549224 : Nat := 118140960795 + 6549224 * 2 ^ 59
def prefixEnd_6549224 : Nat := 4983230072969 + 3 ^ 40 * 6549224 * 2
def baseEnd_6549224 : Nat := 3362899825961589364680673

theorem tailTrace_6549224 : CollatzResearch.WordTrace tailWord_6549224 prefixEnd_6549224 3362899825961589364680673 := by
  unfold tailWord_6549224
  simp only [CollatzResearch.WordTrace]
  refine ⟨119434911612643720627255363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159246548816858294169673817 119434911612643720627255363)
  ·
    refine ⟨179152367418965580940883045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119434911612643720627255363 179152367418965580940883045)
    ·
      refine ⟨33591068891056046426415571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179152367418965580940883045 33591068891056046426415571)
      ·
        refine ⟨50386603336584069639623357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33591068891056046426415571 50386603336584069639623357)
        ·
          refine ⟨18894976251219026114858759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50386603336584069639623357 18894976251219026114858759)
          ·
            refine ⟨28342464376828539172288139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894976251219026114858759 28342464376828539172288139)
            ·
              refine ⟨42513696565242808758432209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28342464376828539172288139 42513696565242808758432209)
              ·
                refine ⟨31885272423932106568824157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42513696565242808758432209 31885272423932106568824157)
                ·
                  refine ⟨11956977158974539963309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31885272423932106568824157 11956977158974539963309059)
                  ·
                    refine ⟨17935465738461809944963589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11956977158974539963309059 17935465738461809944963589)
                    ·
                      refine ⟨3362899825961589364680673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17935465738461809944963589 3362899825961589364680673)
                      ·
                        rfl

theorem cell23_6549224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6549224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549224 prefixEnd_6549224 := by exact prefixLift 6549224
  have htrace : WordTrace (prefixWord ++ tailWord_6549224) baseStart_6549224 baseEnd_6549224 := by
    simpa [prefixWord, tailWord_6549224, baseEnd_6549224] using wordTrace_append hprefix tailTrace_6549224
  have hstable : (prefixWord ++ tailWord_6549224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549224).length < 2 ^ (prefixWord ++ tailWord_6549224).sum := by decide
  have hdescent : baseEnd_6549224 < baseStart_6549224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549227 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_6549227 : Nat := 118140960795 + 6549227 * 2 ^ 59
def prefixEnd_6549227 : Nat := 4983230072969 + 3 ^ 40 * 6549227 * 2
def baseEnd_6549227 : Nat := 3362901366403552852943159

theorem tailTrace_6549227 : CollatzResearch.WordTrace tailWord_6549227 prefixEnd_6549227 3362901366403552852943159 := by
  unfold tailWord_6549227
  simp only [CollatzResearch.WordTrace]
  refine ⟨238869932644276572766869935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159246621762851048511246623 238869932644276572766869935)
  ·
    refine ⟨358304898966414859150304903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238869932644276572766869935 358304898966414859150304903)
    ·
      refine ⟨537457348449622288725457355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358304898966414859150304903 537457348449622288725457355)
      ·
        refine ⟨806186022674433433088186033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537457348449622288725457355 806186022674433433088186033)
        ·
          refine ⟨604639517005825074816139525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 806186022674433433088186033 604639517005825074816139525)
          ·
            refine ⟨113369909438592201528026161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 604639517005825074816139525 113369909438592201528026161)
            ·
              refine ⟨85027432078944151146019621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113369909438592201528026161 85027432078944151146019621)
              ·
                refine ⟨15942643514802028339878679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85027432078944151146019621 15942643514802028339878679)
                ·
                  refine ⟨23913965272203042509818019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942643514802028339878679 23913965272203042509818019)
                  ·
                    refine ⟨35870947908304563764727029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23913965272203042509818019 35870947908304563764727029)
                    ·
                      refine ⟨3362901366403552852943159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35870947908304563764727029 3362901366403552852943159)
                      ·
                        rfl

theorem cell23_6549227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_6549227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549227 prefixEnd_6549227 := by exact prefixLift 6549227
  have htrace : WordTrace (prefixWord ++ tailWord_6549227) baseStart_6549227 baseEnd_6549227 := by
    simpa [prefixWord, tailWord_6549227, baseEnd_6549227] using wordTrace_append hprefix tailTrace_6549227
  have hstable : (prefixWord ++ tailWord_6549227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549227).length < 2 ^ (prefixWord ++ tailWord_6549227).sum := by decide
  have hdescent : baseEnd_6549227 < baseStart_6549227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549234 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_6549234 : Nat := 118140960795 + 6549234 * 2 ^ 59
def prefixEnd_6549234 : Nat := 4983230072969 + 3 ^ 40 * 6549234 * 2
def baseEnd_6549234 : Nat := 1120968320256044775185209

theorem tailTrace_6549234 : CollatzResearch.WordTrace tailWord_6549234 prefixEnd_6549234 1120968320256044775185209 := by
  unfold tailWord_6549234
  simp only [CollatzResearch.WordTrace]
  refine ⟨59717546988812803240593689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159246791970167475308249837 59717546988812803240593689)
  ·
    refine ⟨44788160241609602430445267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59717546988812803240593689 44788160241609602430445267)
    ·
      refine ⟨67182240362414403645667901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44788160241609602430445267 67182240362414403645667901)
      ·
        refine ⟨25193340135905401367125463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67182240362414403645667901 25193340135905401367125463)
        ·
          refine ⟨37790010203858102050688195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25193340135905401367125463 37790010203858102050688195)
          ·
            refine ⟨56685015305787153076032293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37790010203858102050688195 56685015305787153076032293)
            ·
              refine ⟨10628440369835091201756055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56685015305787153076032293 10628440369835091201756055)
              ·
                refine ⟨15942660554752636802634083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10628440369835091201756055 15942660554752636802634083)
                ·
                  refine ⟨23913990832128955203951125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942660554752636802634083 23913990832128955203951125)
                  ·
                    refine ⟨1120968320256044775185209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23913990832128955203951125 1120968320256044775185209)
                    ·
                      rfl

theorem cell23_6549234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_6549234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549234 prefixEnd_6549234 := by exact prefixLift 6549234
  have htrace : WordTrace (prefixWord ++ tailWord_6549234) baseStart_6549234 baseEnd_6549234 := by
    simpa [prefixWord, tailWord_6549234, baseEnd_6549234] using wordTrace_append hprefix tailTrace_6549234
  have hstable : (prefixWord ++ tailWord_6549234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549234).length < 2 ^ (prefixWord ++ tailWord_6549234).sum := by decide
  have hdescent : baseEnd_6549234 < baseStart_6549234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549244 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_6549244 : Nat := 118140960795 + 6549244 * 2 ^ 59
def prefixEnd_6549244 : Nat := 4983230072969 + 3 ^ 40 * 6549244 * 2
def baseEnd_6549244 : Nat := 3362910095574679286430581

theorem tailTrace_6549244 : CollatzResearch.WordTrace tailWord_6549244 prefixEnd_6549244 3362910095574679286430581 := by
  unfold tailWord_6549244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119435276342607492335119393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159247035123476656446825857 119435276342607492335119393)
  ·
    refine ⟨89576457256955619251339545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119435276342607492335119393 89576457256955619251339545)
    ·
      refine ⟨67182342942716714438504659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89576457256955619251339545 67182342942716714438504659)
      ·
        refine ⟨100773514414075071657756989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67182342942716714438504659 100773514414075071657756989)
        ·
          refine ⟨37790067905278151871658871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100773514414075071657756989 37790067905278151871658871)
          ·
            refine ⟨56685101857917227807488307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37790067905278151871658871 56685101857917227807488307)
            ·
              refine ⟨85027652786875841711232461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56685101857917227807488307 85027652786875841711232461)
              ·
                refine ⟨31885369795078440641712173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85027652786875841711232461 31885369795078440641712173)
                ·
                  refine ⟨11957013673154415240642065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31885369795078440641712173 11957013673154415240642065)
                  ·
                    refine ⟨8967760254865811430481549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11957013673154415240642065 8967760254865811430481549)
                    ·
                      refine ⟨3362910095574679286430581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8967760254865811430481549 3362910095574679286430581)
                      ·
                        rfl

theorem cell23_6549244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_6549244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549244 prefixEnd_6549244 := by exact prefixLift 6549244
  have htrace : WordTrace (prefixWord ++ tailWord_6549244) baseStart_6549244 baseEnd_6549244 := by
    simpa [prefixWord, tailWord_6549244, baseEnd_6549244] using wordTrace_append hprefix tailTrace_6549244
  have hstable : (prefixWord ++ tailWord_6549244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549244).length < 2 ^ (prefixWord ++ tailWord_6549244).sum := by decide
  have hdescent : baseEnd_6549244 < baseStart_6549244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549255 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 1, 5]
def baseStart_6549255 : Nat := 118140960795 + 6549255 * 2 ^ 59
def prefixEnd_6549255 : Nat := 4983230072969 + 3 ^ 40 * 6549255 * 2
def baseEnd_6549255 : Nat := 1120971914620626247797677

theorem tailTrace_6549255 : CollatzResearch.WordTrace tailWord_6549255 prefixEnd_6549255 1120971914620626247797677 := by
  unfold tailWord_6549255
  simp only [CollatzResearch.WordTrace]
  refine ⟨238870953888175133548889219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159247302592116755699259479 238870953888175133548889219)
  ·
    refine ⟨358306430832262700323333829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238870953888175133548889219 358306430832262700323333829)
    ·
      refine ⟨67182455781049256310625093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358306430832262700323333829 67182455781049256310625093)
      ·
        refine ⟨12596710458946735558242205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67182455781049256310625093 12596710458946735558242205)
        ·
          refine ⟨4723766422105025834340827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12596710458946735558242205 4723766422105025834340827)
          ·
            refine ⟨7085649633157538751511241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723766422105025834340827 7085649633157538751511241)
            ·
              refine ⟨5314237224868154063633431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7085649633157538751511241 5314237224868154063633431)
              ·
                refine ⟨7971355837302231095450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314237224868154063633431 7971355837302231095450147)
                ·
                  refine ⟨11957033755953346643175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971355837302231095450147 11957033755953346643175221)
                  ·
                    refine ⟨1120971914620626247797677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11957033755953346643175221 1120971914620626247797677)
                    ·
                      rfl

theorem cell23_6549255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_6549255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549255 prefixEnd_6549255 := by exact prefixLift 6549255
  have htrace : WordTrace (prefixWord ++ tailWord_6549255) baseStart_6549255 baseEnd_6549255 := by
    simpa [prefixWord, tailWord_6549255, baseEnd_6549255] using wordTrace_append hprefix tailTrace_6549255
  have hstable : (prefixWord ++ tailWord_6549255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549255).length < 2 ^ (prefixWord ++ tailWord_6549255).sum := by decide
  have hdescent : baseEnd_6549255 < baseStart_6549255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549258 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_6549258 : Nat := 118140960795 + 6549258 * 2 ^ 59
def prefixEnd_6549258 : Nat := 4983230072969 + 3 ^ 40 * 6549258 * 2
def baseEnd_6549258 : Nat := 3362917284303842231655517

theorem tailTrace_6549258 : CollatzResearch.WordTrace tailWord_6549258 prefixEnd_6549258 3362917284303842231655517 := by
  unfold tailWord_6549258
  simp only [CollatzResearch.WordTrace]
  refine ⟨59717765826791066265312107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159247375538109510040832285 59717765826791066265312107)
  ·
    refine ⟨89576648740186599397968161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59717765826791066265312107 89576648740186599397968161)
    ·
      refine ⟨67182486555139949548476121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89576648740186599397968161 67182486555139949548476121)
      ·
        refine ⟨50386864916354962161357091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67182486555139949548476121 50386864916354962161357091)
        ·
          refine ⟨75580297374532443242035637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50386864916354962161357091 75580297374532443242035637)
          ·
            refine ⟨7085652878862416553940841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75580297374532443242035637 7085652878862416553940841)
            ·
              refine ⟨5314239659146812415455631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7085652878862416553940841 5314239659146812415455631)
              ·
                refine ⟨7971359488720218623183447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5314239659146812415455631 7971359488720218623183447)
                ·
                  refine ⟨11957039233080327934775171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971359488720218623183447 11957039233080327934775171)
                  ·
                    refine ⟨17935558849620491902162757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11957039233080327934775171 17935558849620491902162757)
                    ·
                      refine ⟨3362917284303842231655517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17935558849620491902162757 3362917284303842231655517)
                      ·
                        rfl

theorem cell23_6549258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_6549258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549258 prefixEnd_6549258 := by exact prefixLift 6549258
  have htrace : WordTrace (prefixWord ++ tailWord_6549258) baseStart_6549258 baseEnd_6549258 := by
    simpa [prefixWord, tailWord_6549258, baseEnd_6549258] using wordTrace_append hprefix tailTrace_6549258
  have hstable : (prefixWord ++ tailWord_6549258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549258).length < 2 ^ (prefixWord ++ tailWord_6549258).sum := by decide
  have hdescent : baseEnd_6549258 < baseStart_6549258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549438 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_6549438 : Nat := 118140960795 + 6549438 * 2 ^ 59
def prefixEnd_6549438 : Nat := 4983230072969 + 3 ^ 40 * 6549438 * 2
def baseEnd_6549438 : Nat := 3363009710821651527404689

theorem tailTrace_6549438 : CollatzResearch.WordTrace tailWord_6549438 prefixEnd_6549438 3363009710821651527404689 := by
  unfold tailWord_6549438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29859703555814019475350121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159251752297674770535200645 29859703555814019475350121)
  ·
    refine ⟨22394777666860514606512591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29859703555814019475350121 22394777666860514606512591)
    ·
      refine ⟨33592166500290771909768887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22394777666860514606512591 33592166500290771909768887)
      ·
        refine ⟨50388249750436157864653331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33592166500290771909768887 50388249750436157864653331)
        ·
          refine ⟨75582374625654236796979997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50388249750436157864653331 75582374625654236796979997)
          ·
            refine ⟨28343390484620338798867499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75582374625654236796979997 28343390484620338798867499)
            ·
              refine ⟨42515085726930508198301249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28343390484620338798867499 42515085726930508198301249)
              ·
                refine ⟨31886314295197881148725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42515085726930508198301249 31886314295197881148725937)
                ·
                  refine ⟨23914735721398410861544453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31886314295197881148725937 23914735721398410861544453)
                  ·
                    refine ⟨4484012947762202036539585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23914735721398410861544453 4484012947762202036539585)
                    ·
                      refine ⟨3363009710821651527404689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4484012947762202036539585 3363009710821651527404689)
                      ·
                        rfl

theorem cell23_6549438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_6549438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549438 prefixEnd_6549438 := by exact prefixLift 6549438
  have htrace : WordTrace (prefixWord ++ tailWord_6549438) baseStart_6549438 baseEnd_6549438 := by
    simpa [prefixWord, tailWord_6549438, baseEnd_6549438] using wordTrace_append hprefix tailTrace_6549438
  have hstable : (prefixWord ++ tailWord_6549438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549438).length < 2 ^ (prefixWord ++ tailWord_6549438).sum := by decide
  have hdescent : baseEnd_6549438 < baseStart_6549438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549448 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_6549448 : Nat := 118140960795 + 6549448 * 2 ^ 59
def prefixEnd_6549448 : Nat := 4983230072969 + 3 ^ 40 * 6549448 * 2
def baseEnd_6549448 : Nat := 1121004948542732162759881

theorem tailTrace_6549448 : CollatzResearch.WordTrace tailWord_6549448 prefixEnd_6549448 1121004948542732162759881 := by
  unfold tailWord_6549448
  simp only [CollatzResearch.WordTrace]
  refine ⟨119438996588237963755332499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159251995450983951673776665 119438996588237963755332499)
  ·
    refine ⟨179158494882356945632998749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119438996588237963755332499 179158494882356945632998749)
    ·
      refine ⟨67184435580883854612374531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179158494882356945632998749 67184435580883854612374531)
      ·
        refine ⟨100776653371325781918561797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67184435580883854612374531 100776653371325781918561797)
        ·
          refine ⟨18895622507123584109730337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100776653371325781918561797 18895622507123584109730337)
          ·
            refine ⟨14171716880342688082297753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18895622507123584109730337 14171716880342688082297753)
            ·
              refine ⟨10628787660257016061723315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14171716880342688082297753 10628787660257016061723315)
              ·
                refine ⟨15943181490385524092584973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10628787660257016061723315 15943181490385524092584973)
                ·
                  refine ⟨5978693058894571534719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15943181490385524092584973 5978693058894571534719365)
                  ·
                    refine ⟨1121004948542732162759881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5978693058894571534719365 1121004948542732162759881)
                    ·
                      rfl

theorem cell23_6549448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_6549448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549448 prefixEnd_6549448 := by exact prefixLift 6549448
  have htrace : WordTrace (prefixWord ++ tailWord_6549448) baseStart_6549448 baseEnd_6549448 := by
    simpa [prefixWord, tailWord_6549448, baseEnd_6549448] using wordTrace_append hprefix tailTrace_6549448
  have hstable : (prefixWord ++ tailWord_6549448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549448).length < 2 ^ (prefixWord ++ tailWord_6549448).sum := by decide
  have hdescent : baseEnd_6549448 < baseStart_6549448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549464 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6549464 : Nat := 118140960795 + 6549464 * 2 ^ 59
def prefixEnd_6549464 : Nat := 4983230072969 + 3 ^ 40 * 6549464 * 2
def baseEnd_6549464 : Nat := 3363023061318668425679569

theorem tailTrace_6549464 : CollatzResearch.WordTrace tailWord_6549464 prefixEnd_6549464 3363023061318668425679569 := by
  unfold tailWord_6549464
  simp only [CollatzResearch.WordTrace]
  refine ⟨119439288372208981121623723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159252384496278641495498297 119439288372208981121623723)
  ·
    refine ⟨179158932558313471682435585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119439288372208981121623723 179158932558313471682435585)
    ·
      refine ⟨134369199418735103761826689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179158932558313471682435585 134369199418735103761826689)
      ·
        refine ⟨100776899564051327821370017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134369199418735103761826689 100776899564051327821370017)
        ·
          refine ⟨75582674673038495866027513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100776899564051327821370017 75582674673038495866027513)
          ·
            refine ⟨56687006004778871899520635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75582674673038495866027513 56687006004778871899520635)
            ·
              refine ⟨85030509007168307849280953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56687006004778871899520635 85030509007168307849280953)
              ·
                refine ⟨63772881755376230886960715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85030509007168307849280953 63772881755376230886960715)
                ·
                  refine ⟨95659322633064346330441073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63772881755376230886960715 95659322633064346330441073)
                  ·
                    refine ⟨71744491974798259747830805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95659322633064346330441073 71744491974798259747830805)
                    ·
                      refine ⟨3363023061318668425679569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71744491974798259747830805 3363023061318668425679569)
                      ·
                        rfl

theorem cell23_6549464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6549464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549464 prefixEnd_6549464 := by exact prefixLift 6549464
  have htrace : WordTrace (prefixWord ++ tailWord_6549464) baseStart_6549464 baseEnd_6549464 := by
    simpa [prefixWord, tailWord_6549464, baseEnd_6549464] using wordTrace_append hprefix tailTrace_6549464
  have hstable : (prefixWord ++ tailWord_6549464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549464).length < 2 ^ (prefixWord ++ tailWord_6549464).sum := by decide
  have hdescent : baseEnd_6549464 < baseStart_6549464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_6549504 : Nat := 118140960795 + 6549504 * 2 ^ 59
def prefixEnd_6549504 : Nat := 4983230072969 + 3 ^ 40 * 6549504 * 2
def baseEnd_6549504 : Nat := 1121014533514949423059795

theorem tailTrace_6549504 : CollatzResearch.WordTrace tailWord_6549504 prefixEnd_6549504 1121014533514949423059795 := by
  unfold tailWord_6549504
  simp only [CollatzResearch.WordTrace]
  refine ⟨119440017832136524537351783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159253357109515366049802377 119440017832136524537351783)
  ·
    refine ⟨179160026748204786806027675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119440017832136524537351783 179160026748204786806027675)
    ·
      refine ⟨268740040122307180209041513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179160026748204786806027675 268740040122307180209041513)
      ·
        refine ⟨201555030091730385156781135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268740040122307180209041513 201555030091730385156781135)
        ·
          refine ⟨302332545137595577735171703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201555030091730385156781135 302332545137595577735171703)
          ·
            refine ⟨453498817706393366602757555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302332545137595577735171703 453498817706393366602757555)
            ·
              refine ⟨680248226559590049904136333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453498817706393366602757555 680248226559590049904136333)
              ·
                refine ⟨255093084959846268714051125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680248226559590049904136333 255093084959846268714051125)
                ·
                  refine ⟨23914976714985587691942293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255093084959846268714051125 23914976714985587691942293)
                  ·
                    refine ⟨1121014533514949423059795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23914976714985587691942293 1121014533514949423059795)
                    ·
                      rfl

theorem cell23_6549504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_6549504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549504 prefixEnd_6549504 := by exact prefixLift 6549504
  have htrace : WordTrace (prefixWord ++ tailWord_6549504) baseStart_6549504 baseEnd_6549504 := by
    simpa [prefixWord, tailWord_6549504, baseEnd_6549504] using wordTrace_append hprefix tailTrace_6549504
  have hstable : (prefixWord ++ tailWord_6549504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549504).length < 2 ^ (prefixWord ++ tailWord_6549504).sum := by decide
  have hdescent : baseEnd_6549504 < baseStart_6549504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549525 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_6549525 : Nat := 118140960795 + 6549525 * 2 ^ 59
def prefixEnd_6549525 : Nat := 4983230072969 + 3 ^ 40 * 6549525 * 2
def baseEnd_6549525 : Nat := 1121018127879530895672263

theorem tailTrace_6549525 : CollatzResearch.WordTrace tailWord_6549525 prefixEnd_6549525 1121018127879530895672263 := by
  unfold tailWord_6549525
  simp only [CollatzResearch.WordTrace]
  refine ⟨238880801597196969661218029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159253867731464646440812019 238880801597196969661218029)
  ·
    refine ⟨89580300598948863622956761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238880801597196969661218029 89580300598948863622956761)
    ·
      refine ⟨67185225449211647717217571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89580300598948863622956761 67185225449211647717217571)
      ·
        refine ⟨100777838173817471575826357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67185225449211647717217571 100777838173817471575826357)
        ·
          refine ⟨9447922328795387960233721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100777838173817471575826357 9447922328795387960233721)
          ·
            refine ⟨7085941746596540970175291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9447922328795387960233721 7085941746596540970175291)
            ·
              refine ⟨10628912619894811455262937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085941746596540970175291 10628912619894811455262937)
              ·
                refine ⟨7971684464921108591447203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10628912619894811455262937 7971684464921108591447203)
                ·
                  refine ⟨11957526697381662887170805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7971684464921108591447203 11957526697381662887170805)
                  ·
                    refine ⟨1121018127879530895672263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11957526697381662887170805 1121018127879530895672263)
                    ·
                      rfl

theorem cell23_6549525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_6549525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549525 prefixEnd_6549525 := by exact prefixLift 6549525
  have htrace : WordTrace (prefixWord ++ tailWord_6549525) baseStart_6549525 baseEnd_6549525 := by
    simpa [prefixWord, tailWord_6549525, baseEnd_6549525] using wordTrace_append hprefix tailTrace_6549525
  have hstable : (prefixWord ++ tailWord_6549525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549525).length < 2 ^ (prefixWord ++ tailWord_6549525).sum := by decide
  have hdescent : baseEnd_6549525 < baseStart_6549525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6549541 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_6549541 : Nat := 118140960795 + 6549541 * 2 ^ 59
def prefixEnd_6549541 : Nat := 4983230072969 + 3 ^ 40 * 6549541 * 2
def baseEnd_6549541 : Nat := 3363062599329064624416715

theorem tailTrace_6549541 : CollatzResearch.WordTrace tailWord_6549541 prefixEnd_6549541 3363062599329064624416715 := by
  unfold tailWord_6549541
  simp only [CollatzResearch.WordTrace]
  refine ⟨238881385165139004393800477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159254256776759336262533651 238881385165139004393800477)
  ·
    refine ⟨89580519436927126647675179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238881385165139004393800477 89580519436927126647675179)
    ·
      refine ⟨134370779155390689971512769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89580519436927126647675179 134370779155390689971512769)
      ·
        refine ⟨100778084366543017478634577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134370779155390689971512769 100778084366543017478634577)
        ·
          refine ⟨75583563274907263108975933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100778084366543017478634577 75583563274907263108975933)
          ·
            refine ⟨28343836228090223665865975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75583563274907263108975933 28343836228090223665865975)
            ·
              refine ⟨42515754342135335498798963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28343836228090223665865975 42515754342135335498798963)
              ·
                refine ⟨63773631513203003248198445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42515754342135335498798963 63773631513203003248198445)
                ·
                  refine ⟨23915111817451126218074417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63773631513203003248198445 23915111817451126218074417)
                  ·
                    refine ⟨17936333863088344663555813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23915111817451126218074417 17936333863088344663555813)
                    ·
                      refine ⟨3363062599329064624416715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17936333863088344663555813 3363062599329064624416715)
                      ·
                        rfl

theorem cell23_6549541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_6549541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6549541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6549541 prefixEnd_6549541 := by exact prefixLift 6549541
  have htrace : WordTrace (prefixWord ++ tailWord_6549541) baseStart_6549541 baseEnd_6549541 := by
    simpa [prefixWord, tailWord_6549541, baseEnd_6549541] using wordTrace_append hprefix tailTrace_6549541
  have hstable : (prefixWord ++ tailWord_6549541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6549541).length < 2 ^ (prefixWord ++ tailWord_6549541).sum := by decide
  have hdescent : baseEnd_6549541 < baseStart_6549541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6549541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
