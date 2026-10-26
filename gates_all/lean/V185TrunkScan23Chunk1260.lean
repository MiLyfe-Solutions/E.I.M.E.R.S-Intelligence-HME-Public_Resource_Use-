import V185TrunkScan23Chunk1259

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7462938 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_7462938 : Nat := 118140960795 + 7462938 * 2 ^ 59
def prefixEnd_7462938 : Nat := 4983230072969 + 3 ^ 40 * 7462938 * 2
def baseEnd_7462938 : Nat := 3832074288703827454453579

theorem tailTrace_7462938 : CollatzResearch.WordTrace tailWord_7462938 prefixEnd_7462938 3832074288703827454453579 := by
  unfold tailWord_7462938
  simp only [CollatzResearch.WordTrace]
  refine ⟨68048927659264417295485367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181463807091371779454627645 68048927659264417295485367)
  ·
    refine ⟨102073391488896625943228051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68048927659264417295485367 102073391488896625943228051)
    ·
      refine ⟨153110087233344938914842077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102073391488896625943228051 153110087233344938914842077)
      ·
        refine ⟨57416282712504352093065779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153110087233344938914842077 57416282712504352093065779)
        ·
          refine ⟨86124424068756528139598669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57416282712504352093065779 86124424068756528139598669)
          ·
            refine ⟨32296659025783698052349501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86124424068756528139598669 32296659025783698052349501)
            ·
              refine ⟨12111247134668886769631063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32296659025783698052349501 12111247134668886769631063)
              ·
                refine ⟨18166870702003330154446595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111247134668886769631063 18166870702003330154446595)
                ·
                  refine ⟨27250306053004995231669893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18166870702003330154446595 27250306053004995231669893)
                  ·
                    refine ⟨5109432384938436605938105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27250306053004995231669893 5109432384938436605938105)
                    ·
                      refine ⟨3832074288703827454453579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109432384938436605938105 3832074288703827454453579)
                      ·
                        rfl

theorem cell23_7462938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_7462938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462938 prefixEnd_7462938 := by exact prefixLift 7462938
  have htrace : WordTrace (prefixWord ++ tailWord_7462938) baseStart_7462938 baseEnd_7462938 := by
    simpa [prefixWord, tailWord_7462938, baseEnd_7462938] using wordTrace_append hprefix tailTrace_7462938
  have hstable : (prefixWord ++ tailWord_7462938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462938).length < 2 ^ (prefixWord ++ tailWord_7462938).sum := by decide
  have hdescent : baseEnd_7462938 < baseStart_7462938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7462981 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 5, 2]
def baseStart_7462981 : Nat := 118140960795 + 7462981 * 2 ^ 59
def prefixEnd_7462981 : Nat := 4983230072969 + 3 ^ 40 * 7462981 * 2
def baseEnd_7462981 : Nat := 3832096368371970786215881

theorem tailTrace_7462981 : CollatzResearch.WordTrace tailWord_7462981 prefixEnd_7462981 3832096368371970786215881 := by
  unfold tailWord_7462981
  simp only [CollatzResearch.WordTrace]
  refine ⟨272197278975901887525756797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181464852650601258350504531 272197278975901887525756797)
  ·
    refine ⟨102073979615963207822158799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272197278975901887525756797 102073979615963207822158799)
    ·
      refine ⟨153110969423944811733238199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102073979615963207822158799 153110969423944811733238199)
      ·
        refine ⟨229666454135917217599857299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153110969423944811733238199 229666454135917217599857299)
        ·
          refine ⟨344499681203875826399785949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229666454135917217599857299 344499681203875826399785949)
          ·
            refine ⟨129187380451453434899919731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344499681203875826399785949 129187380451453434899919731)
            ·
              refine ⟨193781070677180152349879597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129187380451453434899919731 193781070677180152349879597)
              ·
                refine ⟨72667901503942557131204849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193781070677180152349879597 72667901503942557131204849)
                ·
                  refine ⟨54500926127956917848403637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72667901503942557131204849 54500926127956917848403637)
                  ·
                    refine ⟨5109461824495961048287841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54500926127956917848403637 5109461824495961048287841)
                    ·
                      refine ⟨3832096368371970786215881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109461824495961048287841 3832096368371970786215881)
                      ·
                        rfl

theorem cell23_7462981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_7462981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7462981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7462981 prefixEnd_7462981 := by exact prefixLift 7462981
  have htrace : WordTrace (prefixWord ++ tailWord_7462981) baseStart_7462981 baseEnd_7462981 := by
    simpa [prefixWord, tailWord_7462981, baseEnd_7462981] using wordTrace_append hprefix tailTrace_7462981
  have hstable : (prefixWord ++ tailWord_7462981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7462981).length < 2 ^ (prefixWord ++ tailWord_7462981).sum := by decide
  have hdescent : baseEnd_7462981 < baseStart_7462981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7462981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463011 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7463011 : Nat := 118140960795 + 7463011 * 2 ^ 59
def prefixEnd_7463011 : Nat := 4983230072969 + 3 ^ 40 * 7463011 * 2
def baseEnd_7463011 : Nat := 3832111772791605668840743

theorem tailTrace_7463011 : CollatzResearch.WordTrace tailWord_7463011 prefixEnd_7463011 3832111772791605668840743 := by
  unfold tailWord_7463011
  simp only [CollatzResearch.WordTrace]
  refine ⟨272198373165793202649348887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181465582110528801766232591 272198373165793202649348887)
  ·
    refine ⟨408297559748689803974023331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272198373165793202649348887 408297559748689803974023331)
    ·
      refine ⟨612446339623034705961034997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408297559748689803974023331 612446339623034705961034997)
      ·
        refine ⟨57416844339659503683847031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612446339623034705961034997 57416844339659503683847031)
        ·
          refine ⟨86125266509489255525770547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57416844339659503683847031 86125266509489255525770547)
          ·
            refine ⟨129187899764233883288655821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86125266509489255525770547 129187899764233883288655821)
            ·
              refine ⟨48445462411587706233245933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129187899764233883288655821 48445462411587706233245933)
              ·
                refine ⟨18167048404345389837467225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48445462411587706233245933 18167048404345389837467225)
                ·
                  refine ⟨13625286303259042378100419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18167048404345389837467225 13625286303259042378100419)
                  ·
                    refine ⟨20437929454888563567150629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13625286303259042378100419 20437929454888563567150629)
                    ·
                      refine ⟨3832111772791605668840743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20437929454888563567150629 3832111772791605668840743)
                      ·
                        rfl

theorem cell23_7463011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7463011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463011 prefixEnd_7463011 := by exact prefixLift 7463011
  have htrace : WordTrace (prefixWord ++ tailWord_7463011) baseStart_7463011 baseEnd_7463011 := by
    simpa [prefixWord, tailWord_7463011, baseEnd_7463011] using wordTrace_append hprefix tailTrace_7463011
  have hstable : (prefixWord ++ tailWord_7463011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463011).length < 2 ^ (prefixWord ++ tailWord_7463011).sum := by decide
  have hdescent : baseEnd_7463011 < baseStart_7463011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463085 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 6]
def baseStart_7463085 : Nat := 118140960795 + 7463085 * 2 ^ 59
def prefixEnd_7463085 : Nat := 4983230072969 + 3 ^ 40 * 7463085 * 2
def baseEnd_7463085 : Nat := 425794418928893153257267

theorem tailTrace_7463085 : CollatzResearch.WordTrace tailWord_7463085 prefixEnd_7463085 425794418928893153257267 := by
  unfold tailWord_7463085
  simp only [CollatzResearch.WordTrace]
  refine ⟨272201072167525113287542709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181467381445016742191695139 272201072167525113287542709)
  ·
    refine ⟨25518850515705479370707129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272201072167525113287542709 25518850515705479370707129)
    ·
      refine ⟨19139137886779109528030347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25518850515705479370707129 19139137886779109528030347)
      ·
        refine ⟨28708706830168664292045521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19139137886779109528030347 28708706830168664292045521)
        ·
          refine ⟨21531530122626498219034141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28708706830168664292045521 21531530122626498219034141)
          ·
            refine ⟨8074323795984936832137803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21531530122626498219034141 8074323795984936832137803)
            ·
              refine ⟨12111485693977405248206705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074323795984936832137803 12111485693977405248206705)
              ·
                refine ⟨9083614270483053936155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12111485693977405248206705 9083614270483053936155029)
                ·
                  refine ⟨425794418928893153257267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9083614270483053936155029 425794418928893153257267)
                  ·
                    rfl

theorem cell23_7463085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_7463085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463085 prefixEnd_7463085 := by exact prefixLift 7463085
  have htrace : WordTrace (prefixWord ++ tailWord_7463085) baseStart_7463085 baseEnd_7463085 := by
    simpa [prefixWord, tailWord_7463085, baseEnd_7463085] using wordTrace_append hprefix tailTrace_7463085
  have hstable : (prefixWord ++ tailWord_7463085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463085).length < 2 ^ (prefixWord ++ tailWord_7463085).sum := by decide
  have hdescent : baseEnd_7463085 < baseStart_7463085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463095 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_7463095 : Nat := 118140960795 + 7463095 * 2 ^ 59
def prefixEnd_7463095 : Nat := 4983230072969 + 3 ^ 40 * 7463095 * 2
def baseEnd_7463095 : Nat := 3832154905166583340190357

theorem tailTrace_7463095 : CollatzResearch.WordTrace tailWord_7463095 prefixEnd_7463095 3832154905166583340190357 := by
  unfold tailWord_7463095
  simp only [CollatzResearch.WordTrace]
  refine ⟨272201436897488884995406739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181467624598325923330271159 272201436897488884995406739)
  ·
    refine ⟨408302155346233327493110109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272201436897488884995406739 408302155346233327493110109)
    ·
      refine ⟨153113308254837497809916291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408302155346233327493110109 153113308254837497809916291)
      ·
        refine ⟨229669962382256246714874437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153113308254837497809916291 229669962382256246714874437)
        ·
          refine ⟨43063117946673046259038957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229669962382256246714874437 43063117946673046259038957)
          ·
            refine ⟨16148669230002392347139609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43063117946673046259038957 16148669230002392347139609)
            ·
              refine ⟨12111501922501794260354707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16148669230002392347139609 12111501922501794260354707)
              ·
                refine ⟨18167252883752691390532061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12111501922501794260354707 18167252883752691390532061)
                ·
                  refine ⟨6812719831407259271449523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18167252883752691390532061 6812719831407259271449523)
                  ·
                    refine ⟨10219079747110888907174285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6812719831407259271449523 10219079747110888907174285)
                    ·
                      refine ⟨3832154905166583340190357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219079747110888907174285 3832154905166583340190357)
                      ·
                        rfl

theorem cell23_7463095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_7463095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463095 prefixEnd_7463095 := by exact prefixLift 7463095
  have htrace : WordTrace (prefixWord ++ tailWord_7463095) baseStart_7463095 baseEnd_7463095 := by
    simpa [prefixWord, tailWord_7463095, baseEnd_7463095] using wordTrace_append hprefix tailTrace_7463095
  have hstable : (prefixWord ++ tailWord_7463095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463095).length < 2 ^ (prefixWord ++ tailWord_7463095).sum := by decide
  have hdescent : baseEnd_7463095 < baseStart_7463095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463128 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_7463128 : Nat := 118140960795 + 7463128 * 2 ^ 59
def prefixEnd_7463128 : Nat := 4983230072969 + 3 ^ 40 * 7463128 * 2
def baseEnd_7463128 : Nat := 1277390616676060570359235

theorem tailTrace_7463128 : CollatzResearch.WordTrace tailWord_7463128 prefixEnd_7463128 1277390616676060570359235 := by
  unfold tailWord_7463128
  simp only [CollatzResearch.WordTrace]
  refine ⟨136101320253184665815679019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181468427004246221087572025 136101320253184665815679019)
  ·
    refine ⟨204151980379776998723518529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136101320253184665815679019 204151980379776998723518529)
    ·
      refine ⟨153113985284832749042638897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204151980379776998723518529 153113985284832749042638897)
      ·
        refine ⟨114835488963624561781979173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153113985284832749042638897 114835488963624561781979173)
        ·
          refine ⟨21531654180679605334121095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114835488963624561781979173 21531654180679605334121095)
          ·
            refine ⟨32297481271019408001181643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531654180679605334121095 32297481271019408001181643)
            ·
              refine ⟨48446221906529112001772465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32297481271019408001181643 48446221906529112001772465)
              ·
                refine ⟨36334666429896834001329349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48446221906529112001772465 36334666429896834001329349)
                ·
                  refine ⟨6812749955605656375249253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36334666429896834001329349 6812749955605656375249253)
                  ·
                    refine ⟨1277390616676060570359235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812749955605656375249253 1277390616676060570359235)
                    ·
                      rfl

theorem cell23_7463128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_7463128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463128 prefixEnd_7463128 := by exact prefixLift 7463128
  have htrace : WordTrace (prefixWord ++ tailWord_7463128) baseStart_7463128 baseEnd_7463128 := by
    simpa [prefixWord, tailWord_7463128, baseEnd_7463128] using wordTrace_append hprefix tailTrace_7463128
  have hstable : (prefixWord ++ tailWord_7463128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463128).length < 2 ^ (prefixWord ++ tailWord_7463128).sum := by decide
  have hdescent : baseEnd_7463128 < baseStart_7463128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463141 : List Nat := [1, 3, 1, 4, 2, 1, 11]
def baseStart_7463141 : Nat := 118140960795 + 7463141 * 2 ^ 59
def prefixEnd_7463141 : Nat := 4983230072969 + 3 ^ 40 * 7463141 * 2
def baseEnd_7463141 : Nat := 47310845991070248891545

theorem tailTrace_7463141 : CollatzResearch.WordTrace tailWord_7463141 prefixEnd_7463141 47310845991070248891545 := by
  unfold tailWord_7463141
  simp only [CollatzResearch.WordTrace]
  refine ⟨272203114655322234851581277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181468743103548156567720851 272203114655322234851581277)
  ·
    refine ⟨102076167995745838069342979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272203114655322234851581277 102076167995745838069342979)
    ·
      refine ⟨153114251993618757104014469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102076167995745838069342979 153114251993618757104014469)
      ·
        refine ⟨28708922248803516957002713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153114251993618757104014469 28708922248803516957002713)
        ·
          refine ⟨21531691686602637717752035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28708922248803516957002713 21531691686602637717752035)
          ·
            refine ⟨32297537529903956576628053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531691686602637717752035 32297537529903956576628053)
            ·
              refine ⟨47310845991070248891545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32297537529903956576628053 47310845991070248891545)
              ·
                rfl

theorem cell23_7463141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 11].length) (baseStart_7463141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463141 prefixEnd_7463141 := by exact prefixLift 7463141
  have htrace : WordTrace (prefixWord ++ tailWord_7463141) baseStart_7463141 baseEnd_7463141 := by
    simpa [prefixWord, tailWord_7463141, baseEnd_7463141] using wordTrace_append hprefix tailTrace_7463141
  have hstable : (prefixWord ++ tailWord_7463141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463141).length < 2 ^ (prefixWord ++ tailWord_7463141).sum := by decide
  have hdescent : baseEnd_7463141 < baseStart_7463141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463152 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 1, 2, 2]
def baseStart_7463152 : Nat := 118140960795 + 7463152 * 2 ^ 59
def prefixEnd_7463152 : Nat := 4983230072969 + 3 ^ 40 * 7463152 * 2
def baseEnd_7463152 : Nat := 3832184173563889617177595

theorem tailTrace_7463152 : CollatzResearch.WordTrace tailWord_7463152 prefixEnd_7463152 3832184173563889617177595 := by
  unfold tailWord_7463152
  simp only [CollatzResearch.WordTrace]
  refine ⟨136101757929141191865115855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181469010572188255820154473 136101757929141191865115855)
  ·
    refine ⟨204152636893711787797673783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136101757929141191865115855 204152636893711787797673783)
    ·
      refine ⟨306228955340567681696510675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204152636893711787797673783 306228955340567681696510675)
      ·
        refine ⟨459343433010851522544766013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306228955340567681696510675 459343433010851522544766013)
        ·
          refine ⟨172253787379069320954287255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459343433010851522544766013 172253787379069320954287255)
          ·
            refine ⟨258380681068603981431430883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172253787379069320954287255 258380681068603981431430883)
            ·
              refine ⟨387571021602905972147146325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258380681068603981431430883 387571021602905972147146325)
              ·
                refine ⟨4541847909409054361099371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 387571021602905972147146325 4541847909409054361099371)
                ·
                  refine ⟨6812771864113581541649057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4541847909409054361099371 6812771864113581541649057)
                  ·
                    refine ⟨5109578898085186156236793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812771864113581541649057 5109578898085186156236793)
                    ·
                      refine ⟨3832184173563889617177595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109578898085186156236793 3832184173563889617177595)
                      ·
                        rfl

theorem cell23_7463152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 1, 2, 2].length) (baseStart_7463152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463152 prefixEnd_7463152 := by exact prefixLift 7463152
  have htrace : WordTrace (prefixWord ++ tailWord_7463152) baseStart_7463152 baseEnd_7463152 := by
    simpa [prefixWord, tailWord_7463152, baseEnd_7463152] using wordTrace_append hprefix tailTrace_7463152
  have hstable : (prefixWord ++ tailWord_7463152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463152).length < 2 ^ (prefixWord ++ tailWord_7463152).sum := by decide
  have hdescent : baseEnd_7463152 < baseStart_7463152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463162 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_7463162 : Nat := 118140960795 + 7463162 * 2 ^ 59
def prefixEnd_7463162 : Nat := 4983230072969 + 3 ^ 40 * 7463162 * 2
def baseEnd_7463162 : Nat := 1277396436123478192684183

theorem tailTrace_7463162 : CollatzResearch.WordTrace tailWord_7463162 prefixEnd_7463162 1277396436123478192684183 := by
  unfold tailWord_7463162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68050970147061538859523935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181469253725497436958730493 68050970147061538859523935)
  ·
    refine ⟨102076455220592308289285903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68050970147061538859523935 102076455220592308289285903)
    ·
      refine ⟨153114682830888462433928855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102076455220592308289285903 153114682830888462433928855)
      ·
        refine ⟨229672024246332693650893283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153114682830888462433928855 229672024246332693650893283)
        ·
          refine ⟨344508036369499040476339925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229672024246332693650893283 344508036369499040476339925)
          ·
            refine ⟨8074407102410133761164217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 344508036369499040476339925 8074407102410133761164217)
            ·
              refine ⟨6055805326807600320873163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074407102410133761164217 6055805326807600320873163)
              ·
                refine ⟨9083707990211400481309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055805326807600320873163 9083707990211400481309745)
                ·
                  refine ⟨6812780992658550360982309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083707990211400481309745 6812780992658550360982309)
                  ·
                    refine ⟨1277396436123478192684183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6812780992658550360982309 1277396436123478192684183)
                    ·
                      rfl

theorem cell23_7463162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_7463162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463162 prefixEnd_7463162 := by exact prefixLift 7463162
  have htrace : WordTrace (prefixWord ++ tailWord_7463162) baseStart_7463162 baseEnd_7463162 := by
    simpa [prefixWord, tailWord_7463162, baseEnd_7463162] using wordTrace_append hprefix tailTrace_7463162
  have hstable : (prefixWord ++ tailWord_7463162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463162).length < 2 ^ (prefixWord ++ tailWord_7463162).sum := by decide
  have hdescent : baseEnd_7463162 < baseStart_7463162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463195 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 1, 3, 2]
def baseStart_7463195 : Nat := 118140960795 + 7463195 * 2 ^ 59
def prefixEnd_7463195 : Nat := 4983230072969 + 3 ^ 40 * 7463195 * 2
def baseEnd_7463195 : Nat := 3832206253232032948939897

theorem tailTrace_7463195 : CollatzResearch.WordTrace tailWord_7463195 prefixEnd_7463195 3832206253232032948939897 := by
  unfold tailWord_7463195
  simp only [CollatzResearch.WordTrace]
  refine ⟨272205084197126602074047039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181470056131417734716031359 272205084197126602074047039)
  ·
    refine ⟨408307626295689903111070559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272205084197126602074047039 408307626295689903111070559)
    ·
      refine ⟨612461439443534854666605839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408307626295689903111070559 612461439443534854666605839)
      ·
        refine ⟨918692159165302281999908759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612461439443534854666605839 918692159165302281999908759)
        ·
          refine ⟨1378038238747953422999863139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918692159165302281999908759 1378038238747953422999863139)
          ·
            refine ⟨2067057358121930134499794709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378038238747953422999863139 2067057358121930134499794709)
            ·
              refine ⟨96893313661965475054677877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2067057358121930134499794709 96893313661965475054677877)
              ·
                refine ⟨9083748155809263286376051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96893313661965475054677877 9083748155809263286376051)
                ·
                  refine ⟨13625622233713894929564077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9083748155809263286376051 13625622233713894929564077)
                  ·
                    refine ⟨5109608337642710598586529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13625622233713894929564077 5109608337642710598586529)
                    ·
                      refine ⟨3832206253232032948939897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109608337642710598586529 3832206253232032948939897)
                      ·
                        rfl

theorem cell23_7463195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 3, 2].length) (baseStart_7463195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463195 prefixEnd_7463195 := by exact prefixLift 7463195
  have htrace : WordTrace (prefixWord ++ tailWord_7463195) baseStart_7463195 baseEnd_7463195 := by
    simpa [prefixWord, tailWord_7463195, baseEnd_7463195] using wordTrace_append hprefix tailTrace_7463195
  have hstable : (prefixWord ++ tailWord_7463195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463195).length < 2 ^ (prefixWord ++ tailWord_7463195).sum := by decide
  have hdescent : baseEnd_7463195 < baseStart_7463195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463202 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_7463202 : Nat := 118140960795 + 7463202 * 2 ^ 59
def prefixEnd_7463202 : Nat := 4983230072969 + 3 ^ 40 * 7463202 * 2
def baseEnd_7463202 : Nat := 3832209847596614421552365

theorem tailTrace_7463202 : CollatzResearch.WordTrace tailWord_7463202 prefixEnd_7463202 3832209847596614421552365 := by
  unfold tailWord_7463202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68051334877025310567387965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181470226338734161513034573 68051334877025310567387965)
  ·
    refine ⟨25519250578884491462770487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68051334877025310567387965 25519250578884491462770487)
    ·
      refine ⟨38278875868326737194155731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25519250578884491462770487 38278875868326737194155731)
      ·
        refine ⟨57418313802490105791233597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38278875868326737194155731 57418313802490105791233597)
        ·
          refine ⟨21531867675933789671712599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57418313802490105791233597 21531867675933789671712599)
          ·
            refine ⟨32297801513900684507568899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531867675933789671712599 32297801513900684507568899)
            ·
              refine ⟨48446702270851026761353349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32297801513900684507568899 48446702270851026761353349)
              ·
                refine ⟨9083756675784567517753753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48446702270851026761353349 9083756675784567517753753)
                ·
                  refine ⟨6812817506838425638315315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083756675784567517753753 6812817506838425638315315)
                  ·
                    refine ⟨10219226260257638457472973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6812817506838425638315315 10219226260257638457472973)
                    ·
                      refine ⟨3832209847596614421552365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219226260257638457472973 3832209847596614421552365)
                      ·
                        rfl

theorem cell23_7463202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_7463202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463202 prefixEnd_7463202 := by exact prefixLift 7463202
  have htrace : WordTrace (prefixWord ++ tailWord_7463202) baseStart_7463202 baseEnd_7463202 := by
    simpa [prefixWord, tailWord_7463202, baseEnd_7463202] using wordTrace_append hprefix tailTrace_7463202
  have hstable : (prefixWord ++ tailWord_7463202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463202).length < 2 ^ (prefixWord ++ tailWord_7463202).sum := by decide
  have hdescent : baseEnd_7463202 < baseStart_7463202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463228 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_7463228 : Nat := 118140960795 + 7463228 * 2 ^ 59
def prefixEnd_7463228 : Nat := 4983230072969 + 3 ^ 40 * 7463228 * 2
def baseEnd_7463228 : Nat := 3832223198093631319827245

theorem tailTrace_7463228 : CollatzResearch.WordTrace tailWord_7463228 prefixEnd_7463228 3832223198093631319827245 := by
  unfold tailWord_7463228
  simp only [CollatzResearch.WordTrace]
  refine ⟨136103143903003524354999169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181470858537338032473332225 136103143903003524354999169)
  ·
    refine ⟨102077357927252643266249377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136103143903003524354999169 102077357927252643266249377)
    ·
      refine ⟨76558018445439482449687033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102077357927252643266249377 76558018445439482449687033)
      ·
        refine ⟨57418513834079611837265275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76558018445439482449687033 57418513834079611837265275)
        ·
          refine ⟨86127770751119417755897913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57418513834079611837265275 86127770751119417755897913)
          ·
            refine ⟨64595828063339563316923435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86127770751119417755897913 64595828063339563316923435)
            ·
              refine ⟨96893742095009344975385153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64595828063339563316923435 96893742095009344975385153)
              ·
                refine ⟨72670306571257008731538865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96893742095009344975385153 72670306571257008731538865)
                ·
                  refine ⟨54502729928442756548654149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72670306571257008731538865 54502729928442756548654149)
                  ·
                    refine ⟨10219261861583016852872653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54502729928442756548654149 10219261861583016852872653)
                    ·
                      refine ⟨3832223198093631319827245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219261861583016852872653 3832223198093631319827245)
                      ·
                        rfl

theorem cell23_7463228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_7463228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463228 prefixEnd_7463228 := by exact prefixLift 7463228
  have htrace : WordTrace (prefixWord ++ tailWord_7463228) baseStart_7463228 baseEnd_7463228 := by
    simpa [prefixWord, tailWord_7463228, baseEnd_7463228] using wordTrace_append hprefix tailTrace_7463228
  have hstable : (prefixWord ++ tailWord_7463228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463228).length < 2 ^ (prefixWord ++ tailWord_7463228).sum := by decide
  have hdescent : baseEnd_7463228 < baseStart_7463228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463241 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_7463241 : Nat := 118140960795 + 7463241 * 2 ^ 59
def prefixEnd_7463241 : Nat := 4983230072969 + 3 ^ 40 * 7463241 * 2
def baseEnd_7463241 : Nat := 3832229873342139768964685

theorem tailTrace_7463241 : CollatzResearch.WordTrace tailWord_7463241 prefixEnd_7463241 3832229873342139768964685 := by
  unfold tailWord_7463241
  simp only [CollatzResearch.WordTrace]
  refine ⟨272206761954959951930221577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181471174636639967953481051 272206761954959951930221577)
  ·
    refine ⟨204155071466219963947666183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272206761954959951930221577 204155071466219963947666183)
    ·
      refine ⟨306232607199329945921499275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204155071466219963947666183 306232607199329945921499275)
      ·
        refine ⟨459348910798994918882248913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306232607199329945921499275 459348910798994918882248913)
        ·
          refine ⟨344511683099246189161686685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459348910798994918882248913 344511683099246189161686685)
          ·
            refine ⟨129191881162217320935632507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344511683099246189161686685 129191881162217320935632507)
            ·
              refine ⟨193787821743325981403448761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129191881162217320935632507 193787821743325981403448761)
              ·
                refine ⟨145340866307494486052586571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193787821743325981403448761 145340866307494486052586571)
                ·
                  refine ⟨218011299461241729078879857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145340866307494486052586571 218011299461241729078879857)
                  ·
                    refine ⟨163508474595931296809159893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218011299461241729078879857 163508474595931296809159893)
                    ·
                      refine ⟨3832229873342139768964685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163508474595931296809159893 3832229873342139768964685)
                      ·
                        rfl

theorem cell23_7463241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_7463241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463241 prefixEnd_7463241 := by exact prefixLift 7463241
  have htrace : WordTrace (prefixWord ++ tailWord_7463241) baseStart_7463241 baseEnd_7463241 := by
    simpa [prefixWord, tailWord_7463241, baseEnd_7463241] using wordTrace_append hprefix tailTrace_7463241
  have hstable : (prefixWord ++ tailWord_7463241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463241).length < 2 ^ (prefixWord ++ tailWord_7463241).sum := by decide
  have hdescent : baseEnd_7463241 < baseStart_7463241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463276 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_7463276 : Nat := 118140960795 + 7463276 * 2 ^ 59
def prefixEnd_7463276 : Nat := 4983230072969 + 3 ^ 40 * 7463276 * 2
def baseEnd_7463276 : Nat := 3832247845165047132027025

theorem tailTrace_7463276 : CollatzResearch.WordTrace tailWord_7463276 prefixEnd_7463276 3832247845165047132027025 := by
  unfold tailWord_7463276
  simp only [CollatzResearch.WordTrace]
  refine ⟨136104019254916576453872841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181472025673222101938497121 136104019254916576453872841)
  ·
    refine ⟨102078014441187432340404631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136104019254916576453872841 102078014441187432340404631)
    ·
      refine ⟨153117021661781148510606947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102078014441187432340404631 153117021661781148510606947)
      ·
        refine ⟨229675532492671722765910421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153117021661781148510606947 229675532492671722765910421)
        ·
          refine ⟨10766040585593987004652051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229675532492671722765910421 10766040585593987004652051)
          ·
            refine ⟨16149060878390980506978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766040585593987004652051 16149060878390980506978077)
            ·
              refine ⟨6055897829396617690116779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16149060878390980506978077 6055897829396617690116779)
              ·
                refine ⟨9083846744094926535175169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055897829396617690116779 9083846744094926535175169)
                ·
                  refine ⟨6812885058071194901381377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9083846744094926535175169 6812885058071194901381377)
                  ·
                    refine ⟨5109663793553396176036033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6812885058071194901381377 5109663793553396176036033)
                    ·
                      refine ⟨3832247845165047132027025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109663793553396176036033 3832247845165047132027025)
                      ·
                        rfl

theorem cell23_7463276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_7463276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463276 prefixEnd_7463276 := by exact prefixLift 7463276
  have htrace : WordTrace (prefixWord ++ tailWord_7463276) baseStart_7463276 baseEnd_7463276 := by
    simpa [prefixWord, tailWord_7463276, baseEnd_7463276] using wordTrace_append hprefix tailTrace_7463276
  have hstable : (prefixWord ++ tailWord_7463276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463276).length < 2 ^ (prefixWord ++ tailWord_7463276).sum := by decide
  have hdescent : baseEnd_7463276 < baseStart_7463276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463299 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 5]
def baseStart_7463299 : Nat := 118140960795 + 7463299 * 2 ^ 59
def prefixEnd_7463299 : Nat := 4983230072969 + 3 ^ 40 * 7463299 * 2
def baseEnd_7463299 : Nat := 425806628357788949115491

theorem tailTrace_7463299 : CollatzResearch.WordTrace tailWord_7463299 prefixEnd_7463299 425806628357788949115491 := by
  unfold tailWord_7463299
  simp only [CollatzResearch.WordTrace]
  refine ⟨272208877388749827835832951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181472584925833218557221967 272208877388749827835832951)
  ·
    refine ⟨408313316083124741753749427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272208877388749827835832951 408313316083124741753749427)
    ·
      refine ⟨612469974124687112630624141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408313316083124741753749427 612469974124687112630624141)
      ·
        refine ⟨229676240296757667236484053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612469974124687112630624141 229676240296757667236484053)
        ·
          refine ⟨5383036881955257825855095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 229676240296757667236484053 5383036881955257825855095)
          ·
            refine ⟨8074555322932886738782643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383036881955257825855095 8074555322932886738782643)
            ·
              refine ⟨12111832984399330108173965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8074555322932886738782643 12111832984399330108173965)
              ·
                refine ⟨4541937369149748790565237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12111832984399330108173965 4541937369149748790565237)
                ·
                  refine ⟨425806628357788949115491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541937369149748790565237 425806628357788949115491)
                  ·
                    rfl

theorem cell23_7463299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 5].length) (baseStart_7463299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463299 prefixEnd_7463299 := by exact prefixLift 7463299
  have htrace : WordTrace (prefixWord ++ tailWord_7463299) baseStart_7463299 baseEnd_7463299 := by
    simpa [prefixWord, tailWord_7463299, baseEnd_7463299] using wordTrace_append hprefix tailTrace_7463299
  have hstable : (prefixWord ++ tailWord_7463299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463299).length < 2 ^ (prefixWord ++ tailWord_7463299).sum := by decide
  have hdescent : baseEnd_7463299 < baseStart_7463299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463372 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 6]
def baseStart_7463372 : Nat := 118140960795 + 7463372 * 2 ^ 59
def prefixEnd_7463372 : Nat := 4983230072969 + 3 ^ 40 * 7463372 * 2
def baseEnd_7463372 : Nat := 425810793256430972936287

theorem tailTrace_7463372 : CollatzResearch.WordTrace tailWord_7463372 prefixEnd_7463372 425810793256430972936287 := by
  unfold tailWord_7463372
  simp only [CollatzResearch.WordTrace]
  refine ⟨136105769958742680651620185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181474359944990240868826913 136105769958742680651620185)
  ·
    refine ⟨102079327469057010488715139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136105769958742680651620185 102079327469057010488715139)
    ·
      refine ⟨153118991203585515733072709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102079327469057010488715139 153118991203585515733072709)
      ·
        refine ⟨28709810850672284199951133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153118991203585515733072709 28709810850672284199951133)
        ·
          refine ⟨10766179069002106574981675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28709810850672284199951133 10766179069002106574981675)
          ·
            refine ⟨16149268603503159862472513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766179069002106574981675 16149268603503159862472513)
            ·
              refine ⟨12111951452627369896854385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16149268603503159862472513 12111951452627369896854385)
              ·
                refine ⟨9083963589470527422640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12111951452627369896854385 9083963589470527422640789)
                ·
                  refine ⟨425810793256430972936287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9083963589470527422640789 425810793256430972936287)
                  ·
                    rfl

theorem cell23_7463372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_7463372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463372 prefixEnd_7463372 := by exact prefixLift 7463372
  have htrace : WordTrace (prefixWord ++ tailWord_7463372) baseStart_7463372 baseEnd_7463372 := by
    simpa [prefixWord, tailWord_7463372, baseEnd_7463372] using wordTrace_append hprefix tailTrace_7463372
  have hstable : (prefixWord ++ tailWord_7463372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463372).length < 2 ^ (prefixWord ++ tailWord_7463372).sum := by decide
  have hdescent : baseEnd_7463372 < baseStart_7463372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463375 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 5, 2]
def baseStart_7463375 : Nat := 118140960795 + 7463375 * 2 ^ 59
def prefixEnd_7463375 : Nat := 4983230072969 + 3 ^ 40 * 7463375 * 2
def baseEnd_7463375 : Nat := 3832298679749842244689069

theorem tailTrace_7463375 : CollatzResearch.WordTrace tailWord_7463375 prefixEnd_7463375 3832298679749842244689069 := by
  unfold tailWord_7463375
  simp only [CollatzResearch.WordTrace]
  refine ⟨272211649336474492815599579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181474432890982995210399719 272211649336474492815599579)
  ·
    refine ⟨408317474004711739223399369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272211649336474492815599579 408317474004711739223399369)
    ·
      refine ⟨306238105503533804417549527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408317474004711739223399369 306238105503533804417549527)
      ·
        refine ⟨459357158255300706626324291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306238105503533804417549527 459357158255300706626324291)
        ·
          refine ⟨689035737382951059939486437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459357158255300706626324291 689035737382951059939486437)
          ·
            refine ⟨129194200759303323738653707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689035737382951059939486437 129194200759303323738653707)
            ·
              refine ⟨193791301138954985607980561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129194200759303323738653707 193791301138954985607980561)
              ·
                refine ⟨145343475854216239205985421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193791301138954985607980561 145343475854216239205985421)
                ·
                  refine ⟨54503803445331089702244533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145343475854216239205985421 54503803445331089702244533)
                  ·
                    refine ⟨5109731572999789659585425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54503803445331089702244533 5109731572999789659585425)
                    ·
                      refine ⟨3832298679749842244689069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109731572999789659585425 3832298679749842244689069)
                      ·
                        rfl

theorem cell23_7463375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 5, 2].length) (baseStart_7463375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463375 prefixEnd_7463375 := by exact prefixLift 7463375
  have htrace : WordTrace (prefixWord ++ tailWord_7463375) baseStart_7463375 baseEnd_7463375 := by
    simpa [prefixWord, tailWord_7463375, baseEnd_7463375] using wordTrace_append hprefix tailTrace_7463375
  have hstable : (prefixWord ++ tailWord_7463375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463375).length < 2 ^ (prefixWord ++ tailWord_7463375).sum := by decide
  have hdescent : baseEnd_7463375 < baseStart_7463375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463452 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7463452 : Nat := 118140960795 + 7463452 * 2 ^ 59
def prefixEnd_7463452 : Nat := 4983230072969 + 3 ^ 40 * 7463452 * 2
def baseEnd_7463452 : Nat := 3832338217760238443426215

theorem tailTrace_7463452 : CollatzResearch.WordTrace tailWord_7463452 prefixEnd_7463452 3832338217760238443426215 := by
  unfold tailWord_7463452
  simp only [CollatzResearch.WordTrace]
  refine ⟨136107228878597767483076305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181476305171463689977435073 136107228878597767483076305)
  ·
    refine ⟨102080421658948325612307229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136107228878597767483076305 102080421658948325612307229)
    ·
      refine ⟨38280158122105622104615211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102080421658948325612307229 38280158122105622104615211)
      ·
        refine ⟨57420237183158433156922817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38280158122105622104615211 57420237183158433156922817)
        ·
          refine ⟨43065177887368824867692113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57420237183158433156922817 43065177887368824867692113)
          ·
            refine ⟨32298883415526618650769085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43065177887368824867692113 32298883415526618650769085)
            ·
              refine ⟨12112081280822481994038407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32298883415526618650769085 12112081280822481994038407)
              ·
                refine ⟨18168121921233722991057611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112081280822481994038407 18168121921233722991057611)
                ·
                  refine ⟨27252182881850584486586417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18168121921233722991057611 27252182881850584486586417)
                  ·
                    refine ⟨20439137161387938364939813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27252182881850584486586417 20439137161387938364939813)
                    ·
                      refine ⟨3832338217760238443426215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20439137161387938364939813 3832338217760238443426215)
                      ·
                        rfl

theorem cell23_7463452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7463452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463452 prefixEnd_7463452 := by exact prefixLift 7463452
  have htrace : WordTrace (prefixWord ++ tailWord_7463452) baseStart_7463452 baseEnd_7463452 := by
    simpa [prefixWord, tailWord_7463452, baseEnd_7463452] using wordTrace_append hprefix tailTrace_7463452
  have hstable : (prefixWord ++ tailWord_7463452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463452).length < 2 ^ (prefixWord ++ tailWord_7463452).sum := by decide
  have hdescent : baseEnd_7463452 < baseStart_7463452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463459 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 3]
def baseStart_7463459 : Nat := 118140960795 + 7463459 * 2 ^ 59
def prefixEnd_7463459 : Nat := 4983230072969 + 3 ^ 40 * 7463459 * 2
def baseEnd_7463459 : Nat := 3832341812124819916038683

theorem tailTrace_7463459 : CollatzResearch.WordTrace tailWord_7463459 prefixEnd_7463459 3832341812124819916038683 := by
  unfold tailWord_7463459
  simp only [CollatzResearch.WordTrace]
  refine ⟨272214713068170175161657431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181476475378780116774438287 272214713068170175161657431)
  ·
    refine ⟨408322069602255262742486147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272214713068170175161657431 408322069602255262742486147)
    ·
      refine ⟨612483104403382894113729221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408322069602255262742486147 612483104403382894113729221)
      ·
        refine ⟨114840582075634292646324229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 612483104403382894113729221 114840582075634292646324229)
        ·
          refine ⟨21532609139181429871185793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114840582075634292646324229 21532609139181429871185793)
          ·
            refine ⟨16149456854386072403389345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21532609139181429871185793 16149456854386072403389345)
            ·
              refine ⟨12112092640789554302542009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16149456854386072403389345 12112092640789554302542009)
              ·
                refine ⟨9084069480592165726906507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12112092640789554302542009 9084069480592165726906507)
                ·
                  refine ⟨13626104220888248590359761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084069480592165726906507 13626104220888248590359761)
                  ·
                    refine ⟨10219578165666186442769821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13626104220888248590359761 10219578165666186442769821)
                    ·
                      refine ⟨3832341812124819916038683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219578165666186442769821 3832341812124819916038683)
                      ·
                        rfl

theorem cell23_7463459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_7463459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463459 prefixEnd_7463459 := by exact prefixLift 7463459
  have htrace : WordTrace (prefixWord ++ tailWord_7463459) baseStart_7463459 baseEnd_7463459 := by
    simpa [prefixWord, tailWord_7463459, baseEnd_7463459] using wordTrace_append hprefix tailTrace_7463459
  have hstable : (prefixWord ++ tailWord_7463459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463459).length < 2 ^ (prefixWord ++ tailWord_7463459).sum := by decide
  have hdescent : baseEnd_7463459 < baseStart_7463459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463472 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_7463472 : Nat := 118140960795 + 7463472 * 2 ^ 59
def prefixEnd_7463472 : Nat := 4983230072969 + 3 ^ 40 * 7463472 * 2
def baseEnd_7463472 : Nat := 3832348487373328365176123

theorem tailTrace_7463472 : CollatzResearch.WordTrace tailWord_7463472 prefixEnd_7463472 3832348487373328365176123 := by
  unfold tailWord_7463472
  simp only [CollatzResearch.WordTrace]
  refine ⟨136107593608561539190940335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181476791478082052254587113 136107593608561539190940335)
  ·
    refine ⟨204161390412842308786410503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136107593608561539190940335 204161390412842308786410503)
    ·
      refine ⟨306242085619263463179615755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204161390412842308786410503 306242085619263463179615755)
      ·
        refine ⟨459363128428895194769423633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306242085619263463179615755 459363128428895194769423633)
        ·
          refine ⟨344522346321671396077067725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459363128428895194769423633 344522346321671396077067725)
          ·
            refine ⟨129195879870626773528900397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344522346321671396077067725 129195879870626773528900397)
            ·
              refine ⟨48448454951485040073337649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129195879870626773528900397 48448454951485040073337649)
              ·
                refine ⟨36336341213613780055003237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48448454951485040073337649 36336341213613780055003237)
                ·
                  refine ⟨6813063977552583760313107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36336341213613780055003237 6813063977552583760313107)
                  ·
                    refine ⟨10219595966328875640469661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6813063977552583760313107 10219595966328875640469661)
                    ·
                      refine ⟨3832348487373328365176123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219595966328875640469661 3832348487373328365176123)
                      ·
                        rfl

theorem cell23_7463472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_7463472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463472 prefixEnd_7463472 := by exact prefixLift 7463472
  have htrace : WordTrace (prefixWord ++ tailWord_7463472) baseStart_7463472 baseEnd_7463472 := by
    simpa [prefixWord, tailWord_7463472, baseEnd_7463472] using wordTrace_append hprefix tailTrace_7463472
  have hstable : (prefixWord ++ tailWord_7463472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463472).length < 2 ^ (prefixWord ++ tailWord_7463472).sum := by decide
  have hdescent : baseEnd_7463472 < baseStart_7463472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463476 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7463476 : Nat := 118140960795 + 7463476 * 2 ^ 59
def prefixEnd_7463476 : Nat := 4983230072969 + 3 ^ 40 * 7463476 * 2
def baseEnd_7463476 : Nat := 3832350541295946349526105

theorem tailTrace_7463476 : CollatzResearch.WordTrace tailWord_7463476 prefixEnd_7463476 3832350541295946349526105 := by
  unfold tailWord_7463476
  simp only [CollatzResearch.WordTrace]
  refine ⟨136107666554554293532513141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181476888739405724710017521 136107666554554293532513141)
  ·
    refine ⟨12760093739489465018673107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136107666554554293532513141 12760093739489465018673107)
    ·
      refine ⟨19140140609234197528009661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12760093739489465018673107 19140140609234197528009661)
      ·
        refine ⟨7177552728462824073003623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19140140609234197528009661 7177552728462824073003623)
        ·
          refine ⟨10766329092694236109505435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7177552728462824073003623 10766329092694236109505435)
          ·
            refine ⟨16149493639041354164258153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766329092694236109505435 16149493639041354164258153)
            ·
              refine ⟨12112120229281015623193615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16149493639041354164258153 12112120229281015623193615)
              ·
                refine ⟨18168180343921523434790423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112120229281015623193615 18168180343921523434790423)
                ·
                  refine ⟨27252270515882285152185635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18168180343921523434790423 27252270515882285152185635)
                  ·
                    refine ⟨40878405773823427728278453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27252270515882285152185635 40878405773823427728278453)
                    ·
                      refine ⟨3832350541295946349526105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40878405773823427728278453 3832350541295946349526105)
                      ·
                        rfl

theorem cell23_7463476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7463476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463476 prefixEnd_7463476 := by exact prefixLift 7463476
  have htrace : WordTrace (prefixWord ++ tailWord_7463476) baseStart_7463476 baseEnd_7463476 := by
    simpa [prefixWord, tailWord_7463476, baseEnd_7463476] using wordTrace_append hprefix tailTrace_7463476
  have hstable : (prefixWord ++ tailWord_7463476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463476).length < 2 ^ (prefixWord ++ tailWord_7463476).sum := by decide
  have hdescent : baseEnd_7463476 < baseStart_7463476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463489 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7463489 : Nat := 118140960795 + 7463489 * 2 ^ 59
def prefixEnd_7463489 : Nat := 4983230072969 + 3 ^ 40 * 7463489 * 2
def baseEnd_7463489 : Nat := 3832357216544454798663545

theorem tailTrace_7463489 : CollatzResearch.WordTrace tailWord_7463489 prefixEnd_7463489 3832357216544454798663545 := by
  unfold tailWord_7463489
  simp only [CollatzResearch.WordTrace]
  refine ⟨272215807258061490285249521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181477204838707660190166347 272215807258061490285249521)
  ·
    refine ⟨204161855443546117713937141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272215807258061490285249521 204161855443546117713937141)
    ·
      refine ⟨19140173947832448535681607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204161855443546117713937141 19140173947832448535681607)
      ·
        refine ⟨28710260921748672803522411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19140173947832448535681607 28710260921748672803522411)
        ·
          refine ⟨43065391382623009205283617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28710260921748672803522411 43065391382623009205283617)
          ·
            refine ⟨32299043536967256903962713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43065391382623009205283617 32299043536967256903962713)
            ·
              refine ⟨24224282652725442677972035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32299043536967256903962713 24224282652725442677972035)
              ·
                refine ⟨36336423979088164016958053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24224282652725442677972035 36336423979088164016958053)
                ·
                  refine ⟨6813079496079030753179635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36336423979088164016958053 6813079496079030753179635)
                  ·
                    refine ⟨10219619244118546129769453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6813079496079030753179635 10219619244118546129769453)
                    ·
                      refine ⟨3832357216544454798663545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219619244118546129769453 3832357216544454798663545)
                      ·
                        rfl

theorem cell23_7463489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7463489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463489 prefixEnd_7463489 := by exact prefixLift 7463489
  have htrace : WordTrace (prefixWord ++ tailWord_7463489) baseStart_7463489 baseEnd_7463489 := by
    simpa [prefixWord, tailWord_7463489, baseEnd_7463489] using wordTrace_append hprefix tailTrace_7463489
  have hstable : (prefixWord ++ tailWord_7463489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463489).length < 2 ^ (prefixWord ++ tailWord_7463489).sum := by decide
  have hdescent : baseEnd_7463489 < baseStart_7463489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463516 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7463516 : Nat := 118140960795 + 7463516 * 2 ^ 59
def prefixEnd_7463516 : Nat := 4983230072969 + 3 ^ 40 * 7463516 * 2
def baseEnd_7463516 : Nat := 3832371080522126193025921

theorem tailTrace_7463516 : CollatzResearch.WordTrace tailWord_7463516 prefixEnd_7463516 3832371080522126193025921 := by
  unfold tailWord_7463516
  simp only [CollatzResearch.WordTrace]
  refine ⟨136108396014481836948241201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181477861352642449264321601 136108396014481836948241201)
  ·
    refine ⟨102081297010861377711180901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136108396014481836948241201 102081297010861377711180901)
    ·
      refine ⟨19140243189536508320846419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102081297010861377711180901 19140243189536508320846419)
      ·
        refine ⟨28710364784304762481269629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19140243189536508320846419 28710364784304762481269629)
        ·
          refine ⟨10766386794114285930476111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28710364784304762481269629 10766386794114285930476111)
          ·
            refine ⟨16149580191171428895714167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766386794114285930476111 16149580191171428895714167)
            ·
              refine ⟨24224370286757143343571251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16149580191171428895714167 24224370286757143343571251)
              ·
                refine ⟨36336555430135715015356877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24224370286757143343571251 36336555430135715015356877)
                ·
                  refine ⟨13626208286300893130758829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36336555430135715015356877 13626208286300893130758829)
                  ·
                    refine ⟨5109828107362834924034561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13626208286300893130758829 5109828107362834924034561)
                    ·
                      refine ⟨3832371080522126193025921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109828107362834924034561 3832371080522126193025921)
                      ·
                        rfl

theorem cell23_7463516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7463516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463516 prefixEnd_7463516 := by exact prefixLift 7463516
  have htrace : WordTrace (prefixWord ++ tailWord_7463516) baseStart_7463516 baseEnd_7463516 := by
    simpa [prefixWord, tailWord_7463516, baseEnd_7463516] using wordTrace_append hprefix tailTrace_7463516
  have hstable : (prefixWord ++ tailWord_7463516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463516).length < 2 ^ (prefixWord ++ tailWord_7463516).sum := by decide
  have hdescent : baseEnd_7463516 < baseStart_7463516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463533 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7463533 : Nat := 118140960795 + 7463533 * 2 ^ 59
def prefixEnd_7463533 : Nat := 4983230072969 + 3 ^ 40 * 7463533 * 2
def baseEnd_7463533 : Nat := 3832379809693252626513343

theorem tailTrace_7463533 : CollatzResearch.WordTrace tailWord_7463533 prefixEnd_7463533 3832379809693252626513343 := by
  unfold tailWord_7463533
  simp only [CollatzResearch.WordTrace]
  refine ⟨272217412069902085799851253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181478274713268057199900835 272217412069902085799851253)
  ·
    refine ⟨25520382381553320543736055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272217412069902085799851253 25520382381553320543736055)
    ·
      refine ⟨38280573572329980815604083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25520382381553320543736055 38280573572329980815604083)
      ·
        refine ⟨57420860358494971223406125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38280573572329980815604083 57420860358494971223406125)
        ·
          refine ⟨21532822634435614208777297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57420860358494971223406125 21532822634435614208777297)
          ·
            refine ⟨16149616975826710656582973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21532822634435614208777297 16149616975826710656582973)
            ·
              refine ⟨6056106365935016496218615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16149616975826710656582973 6056106365935016496218615)
              ·
                refine ⟨9084159548902524744327923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056106365935016496218615 9084159548902524744327923)
                ·
                  refine ⟨13626239323353787116491885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084159548902524744327923 13626239323353787116491885)
                  ·
                    refine ⟨5109839746257670168684457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13626239323353787116491885 5109839746257670168684457)
                    ·
                      refine ⟨3832379809693252626513343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109839746257670168684457 3832379809693252626513343)
                      ·
                        rfl

theorem cell23_7463533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7463533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463533 prefixEnd_7463533 := by exact prefixLift 7463533
  have htrace : WordTrace (prefixWord ++ tailWord_7463533) baseStart_7463533 baseEnd_7463533 := by
    simpa [prefixWord, tailWord_7463533, baseEnd_7463533] using wordTrace_append hprefix tailTrace_7463533
  have hstable : (prefixWord ++ tailWord_7463533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463533).length < 2 ^ (prefixWord ++ tailWord_7463533).sum := by decide
  have hdescent : baseEnd_7463533 < baseStart_7463533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463602 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_7463602 : Nat := 118140960795 + 7463602 * 2 ^ 59
def prefixEnd_7463602 : Nat := 4983230072969 + 3 ^ 40 * 7463602 * 2
def baseEnd_7463602 : Nat := 3832415239858412856550525

theorem tailTrace_7463602 : CollatzResearch.WordTrace tailWord_7463602 prefixEnd_7463602 3832415239858412856550525 := by
  unfold tailWord_7463602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68054982176663027646028265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181479952471101407056075373 68054982176663027646028265)
  ·
    refine ⟨51041236632497270734521199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68054982176663027646028265 51041236632497270734521199)
    ·
      refine ⟨76561854948745906101781799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51041236632497270734521199 76561854948745906101781799)
      ·
        refine ⟨114842782423118859152672699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76561854948745906101781799 114842782423118859152672699)
        ·
          refine ⟨172264173634678288729009049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114842782423118859152672699 172264173634678288729009049)
          ·
            refine ⟨129198130226008716546756787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172264173634678288729009049 129198130226008716546756787)
            ·
              refine ⟨193797195339013074820135181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129198130226008716546756787 193797195339013074820135181)
              ·
                refine ⟨72673948252129903057550693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193797195339013074820135181 72673948252129903057550693)
                ·
                  refine ⟨13626365297274356823290755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72673948252129903057550693 13626365297274356823290755)
                  ·
                    refine ⟨20439547945911535234936133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13626365297274356823290755 20439547945911535234936133)
                    ·
                      refine ⟨3832415239858412856550525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20439547945911535234936133 3832415239858412856550525)
                      ·
                        rfl

theorem cell23_7463602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_7463602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463602 prefixEnd_7463602 := by exact prefixLift 7463602
  have htrace : WordTrace (prefixWord ++ tailWord_7463602) baseStart_7463602 baseEnd_7463602 := by
    simpa [prefixWord, tailWord_7463602, baseEnd_7463602] using wordTrace_append hprefix tailTrace_7463602
  have hstable : (prefixWord ++ tailWord_7463602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463602).length < 2 ^ (prefixWord ++ tailWord_7463602).sum := by decide
  have hdescent : baseEnd_7463602 < baseStart_7463602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463656 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7463656 : Nat := 118140960795 + 7463656 * 2 ^ 59
def prefixEnd_7463656 : Nat := 4983230072969 + 3 ^ 40 * 7463656 * 2
def baseEnd_7463656 : Nat := 3832442967813755645275277

theorem tailTrace_7463656 : CollatzResearch.WordTrace tailWord_7463656 prefixEnd_7463656 3832442967813755645275277 := by
  unfold tailWord_7463656
  simp only [CollatzResearch.WordTrace]
  refine ⟨136110949124228238903289411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181481265498970985204385881 136110949124228238903289411)
  ·
    refine ⟨204166423686342358354934117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136110949124228238903289411 204166423686342358354934117)
    ·
      refine ⟨38281204441189192191550147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204166423686342358354934117 38281204441189192191550147)
      ·
        refine ⟨57421806661783788287325221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38281204441189192191550147 57421806661783788287325221)
        ·
          refine ⟨10766588749084460303873479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57421806661783788287325221 10766588749084460303873479)
          ·
            refine ⟨16149883123626690455810219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10766588749084460303873479 16149883123626690455810219)
            ·
              refine ⟨24224824685440035683715329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16149883123626690455810219 24224824685440035683715329)
              ·
                refine ⟨18168618514080026762786497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24224824685440035683715329 18168618514080026762786497)
                ·
                  refine ⟨13626463885560020072089873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18168618514080026762786497 13626463885560020072089873)
                  ·
                    refine ⟨10219847914170015054067405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13626463885560020072089873 10219847914170015054067405)
                    ·
                      refine ⟨3832442967813755645275277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219847914170015054067405 3832442967813755645275277)
                      ·
                        rfl

theorem cell23_7463656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7463656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463656 prefixEnd_7463656 := by exact prefixLift 7463656
  have htrace : WordTrace (prefixWord ++ tailWord_7463656) baseStart_7463656 baseEnd_7463656 := by
    simpa [prefixWord, tailWord_7463656, baseEnd_7463656] using wordTrace_append hprefix tailTrace_7463656
  have hstable : (prefixWord ++ tailWord_7463656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463656).length < 2 ^ (prefixWord ++ tailWord_7463656).sum := by decide
  have hdescent : baseEnd_7463656 < baseStart_7463656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463663 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 1, 4]
def baseStart_7463663 : Nat := 118140960795 + 7463663 * 2 ^ 59
def prefixEnd_7463663 : Nat := 4983230072969 + 3 ^ 40 * 7463663 * 2
def baseEnd_7463663 : Nat := 1277482187392779039295915

theorem tailTrace_7463663 : CollatzResearch.WordTrace tailWord_7463663 prefixEnd_7463663 1277482187392779039295915 := by
  unfold tailWord_7463663
  simp only [CollatzResearch.WordTrace]
  refine ⟨272222153559431118002083643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181481435706287412001389095 272222153559431118002083643)
  ·
    refine ⟨408333230339146677003125465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272222153559431118002083643 408333230339146677003125465)
    ·
      refine ⟨306249922754360007752344099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408333230339146677003125465 306249922754360007752344099)
      ·
        refine ⟨459374884131540011628516149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306249922754360007752344099 459374884131540011628516149)
        ·
          refine ⟨43066395387331876090173389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 459374884131540011628516149 43066395387331876090173389)
          ·
            refine ⟨16149898270249453533815021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43066395387331876090173389 16149898270249453533815021)
            ·
              refine ⟨6056211851343545075180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16149898270249453533815021 6056211851343545075180633)
              ·
                refine ⟨4542158888507658806385475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056211851343545075180633 4542158888507658806385475)
                ·
                  refine ⟨6813238332761488209578213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542158888507658806385475 6813238332761488209578213)
                  ·
                    refine ⟨1277482187392779039295915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813238332761488209578213 1277482187392779039295915)
                    ·
                      rfl

theorem cell23_7463663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_7463663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463663 prefixEnd_7463663 := by exact prefixLift 7463663
  have htrace : WordTrace (prefixWord ++ tailWord_7463663) baseStart_7463663 baseEnd_7463663 := by
    simpa [prefixWord, tailWord_7463663, baseEnd_7463663] using wordTrace_append hprefix tailTrace_7463663
  have hstable : (prefixWord ++ tailWord_7463663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463663).length < 2 ^ (prefixWord ++ tailWord_7463663).sum := by decide
  have hdescent : baseEnd_7463663 < baseStart_7463663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463672 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_7463672 : Nat := 118140960795 + 7463672 * 2 ^ 59
def prefixEnd_7463672 : Nat := 4983230072969 + 3 ^ 40 * 7463672 * 2
def baseEnd_7463672 : Nat := 1277483727834742527558401

theorem tailTrace_7463672 : CollatzResearch.WordTrace tailWord_7463672 prefixEnd_7463672 1277483727834742527558401 := by
  unfold tailWord_7463672
  simp only [CollatzResearch.WordTrace]
  refine ⟨136111240908199256269580635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181481654544265675026107513 136111240908199256269580635)
  ·
    refine ⟨204166861362298884404370953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136111240908199256269580635 204166861362298884404370953)
    ·
      refine ⟨153125146021724163303278215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204166861362298884404370953 153125146021724163303278215)
      ·
        refine ⟨229687719032586244954917323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153125146021724163303278215 229687719032586244954917323)
        ·
          refine ⟨344531578548879367432375985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229687719032586244954917323 344531578548879367432375985)
          ·
            refine ⟨258398683911659525574281989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344531578548879367432375985 258398683911659525574281989)
            ·
              refine ⟨48449753233436161045177873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258398683911659525574281989 48449753233436161045177873)
              ·
                refine ⟨36337314925077120783883405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48449753233436161045177873 36337314925077120783883405)
                ·
                  refine ⟨13626493096903920293956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36337314925077120783883405 13626493096903920293956277)
                  ·
                    refine ⟨1277483727834742527558401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13626493096903920293956277 1277483727834742527558401)
                    ·
                      rfl

theorem cell23_7463672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_7463672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463672 prefixEnd_7463672 := by exact prefixLift 7463672
  have htrace : WordTrace (prefixWord ++ tailWord_7463672) baseStart_7463672 baseEnd_7463672 := by
    simpa [prefixWord, tailWord_7463672, baseEnd_7463672] using wordTrace_append hprefix tailTrace_7463672
  have hstable : (prefixWord ++ tailWord_7463672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463672).length < 2 ^ (prefixWord ++ tailWord_7463672).sum := by decide
  have hdescent : baseEnd_7463672 < baseStart_7463672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463676 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 6]
def baseStart_7463676 : Nat := 118140960795 + 7463676 * 2 ^ 59
def prefixEnd_7463676 : Nat := 4983230072969 + 3 ^ 40 * 7463676 * 2
def baseEnd_7463676 : Nat := 425828137491871729669465

theorem tailTrace_7463676 : CollatzResearch.WordTrace tailWord_7463676 prefixEnd_7463676 425828137491871729669465 := by
  unfold tailWord_7463676
  simp only [CollatzResearch.WordTrace]
  refine ⟨136111313854192010611153441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181481751805589347481537921 136111313854192010611153441)
  ·
    refine ⟨102083485390644007958365081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136111313854192010611153441 102083485390644007958365081)
    ·
      refine ⟨76562614042983005968773811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102083485390644007958365081 76562614042983005968773811)
      ·
        refine ⟨114843921064474508953160717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76562614042983005968773811 114843921064474508953160717)
        ·
          refine ⟨43066470399177940857435269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114843921064474508953160717 43066470399177940857435269)
          ·
            refine ⟨8074963199845863910769113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43066470399177940857435269 8074963199845863910769113)
            ·
              refine ⟨6056222399884397933076835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8074963199845863910769113 6056222399884397933076835)
              ·
                refine ⟨9084333599826596899615253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056222399884397933076835 9084333599826596899615253)
                ·
                  refine ⟨425828137491871729669465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9084333599826596899615253 425828137491871729669465)
                  ·
                    rfl

theorem cell23_7463676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_7463676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463676 prefixEnd_7463676 := by exact prefixLift 7463676
  have htrace : WordTrace (prefixWord ++ tailWord_7463676) baseStart_7463676 baseEnd_7463676 := by
    simpa [prefixWord, tailWord_7463676, baseEnd_7463676] using wordTrace_append hprefix tailTrace_7463676
  have hstable : (prefixWord ++ tailWord_7463676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463676).length < 2 ^ (prefixWord ++ tailWord_7463676).sum := by decide
  have hdescent : baseEnd_7463676 < baseStart_7463676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463679 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 6, 3, 2]
def baseStart_7463679 : Nat := 118140960795 + 7463679 * 2 ^ 59
def prefixEnd_7463679 : Nat := 4983230072969 + 3 ^ 40 * 7463679 * 2
def baseEnd_7463679 : Nat := 3832454777868809055287671

theorem tailTrace_7463679 : CollatzResearch.WordTrace tailWord_7463679 prefixEnd_7463679 3832454777868809055287671 := by
  unfold tailWord_7463679
  simp only [CollatzResearch.WordTrace]
  refine ⟨272222737127373152734666091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181481824751582101823110727 272222737127373152734666091)
  ·
    refine ⟨408334105691059729101999137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272222737127373152734666091 408334105691059729101999137)
    ·
      refine ⟨306250579268294796826499353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408334105691059729101999137 306250579268294796826499353)
      ·
        refine ⟨229687934451221097619874515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306250579268294796826499353 229687934451221097619874515)
        ·
          refine ⟨344531901676831646429811773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229687934451221097619874515 344531901676831646429811773)
          ·
            refine ⟨129199463128811867411179415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344531901676831646429811773 129199463128811867411179415)
            ·
              refine ⟨193799194693217801116769123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129199463128811867411179415 193799194693217801116769123)
              ·
                refine ⟨290698792039826701675153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193799194693217801116769123 290698792039826701675153685)
                ·
                  refine ⟨13626505876866876641022829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290698792039826701675153685 13626505876866876641022829)
                  ·
                    refine ⟨5109939703825078740383561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13626505876866876641022829 5109939703825078740383561)
                    ·
                      refine ⟨3832454777868809055287671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109939703825078740383561 3832454777868809055287671)
                      ·
                        rfl

theorem cell23_7463679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_7463679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463679 prefixEnd_7463679 := by exact prefixLift 7463679
  have htrace : WordTrace (prefixWord ++ tailWord_7463679) baseStart_7463679 baseEnd_7463679 := by
    simpa [prefixWord, tailWord_7463679, baseEnd_7463679] using wordTrace_append hprefix tailTrace_7463679
  have hstable : (prefixWord ++ tailWord_7463679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463679).length < 2 ^ (prefixWord ++ tailWord_7463679).sum := by decide
  have hdescent : baseEnd_7463679 < baseStart_7463679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463689 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_7463689 : Nat := 118140960795 + 7463689 * 2 ^ 59
def prefixEnd_7463689 : Nat := 4983230072969 + 3 ^ 40 * 7463689 * 2
def baseEnd_7463689 : Nat := 1277486637558451338720875

theorem tailTrace_7463689 : CollatzResearch.WordTrace tailWord_7463689 prefixEnd_7463689 1277486637558451338720875 := by
  unfold tailWord_7463689
  simp only [CollatzResearch.WordTrace]
  refine ⟨272223101857336924442530121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181482067904891282961686747 272223101857336924442530121)
  ·
    refine ⟨204167326393002693331897591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272223101857336924442530121 204167326393002693331897591)
    ·
      refine ⟨306250989589504039997846387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204167326393002693331897591 306250989589504039997846387)
      ·
        refine ⟨459376484384256059996769581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306250989589504039997846387 459376484384256059996769581)
        ·
          refine ⟨172266181644096022498788593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459376484384256059996769581 172266181644096022498788593)
          ·
            refine ⟨129199636233072016874091445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172266181644096022498788593 129199636233072016874091445)
            ·
              refine ⟨12112465896850501581946073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129199636233072016874091445 12112465896850501581946073)
              ·
                refine ⟨9084349422637876186459555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12112465896850501581946073 9084349422637876186459555)
                ·
                  refine ⟨13626524133956814279689333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084349422637876186459555 13626524133956814279689333)
                  ·
                    refine ⟨1277486637558451338720875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13626524133956814279689333 1277486637558451338720875)
                    ·
                      rfl

theorem cell23_7463689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_7463689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463689 prefixEnd_7463689 := by exact prefixLift 7463689
  have htrace : WordTrace (prefixWord ++ tailWord_7463689) baseStart_7463689 baseEnd_7463689 := by
    simpa [prefixWord, tailWord_7463689, baseEnd_7463689] using wordTrace_append hprefix tailTrace_7463689
  have hstable : (prefixWord ++ tailWord_7463689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463689).length < 2 ^ (prefixWord ++ tailWord_7463689).sum := by decide
  have hdescent : baseEnd_7463689 < baseStart_7463689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463706 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_7463706 : Nat := 118140960795 + 7463706 * 2 ^ 59
def prefixEnd_7463706 : Nat := 4983230072969 + 3 ^ 40 * 7463706 * 2
def baseEnd_7463706 : Nat := 1277489547282160149883349

theorem tailTrace_7463706 : CollatzResearch.WordTrace tailWord_7463706 prefixEnd_7463706 1277489547282160149883349 := by
  unfold tailWord_7463706
  simp only [CollatzResearch.WordTrace]
  refine ⟨68055930474568834086474743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181482481265516890897265981 68055930474568834086474743)
  ·
    refine ⟨102083895711853251129712115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68055930474568834086474743 102083895711853251129712115)
    ·
      refine ⟨153125843567779876694568173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102083895711853251129712115 153125843567779876694568173)
      ·
        refine ⟨57422191337917453760463065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153125843567779876694568173 57422191337917453760463065)
        ·
          refine ⟨43066643503438090320347299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57422191337917453760463065 43066643503438090320347299)
          ·
            refine ⟨64599965255157135480520949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43066643503438090320347299 64599965255157135480520949)
            ·
              refine ⟨6056246742670981451298839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64599965255157135480520949 6056246742670981451298839)
              ·
                refine ⟨9084370114006472176948259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056246742670981451298839 9084370114006472176948259)
                ·
                  refine ⟨13626555171009708265422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084370114006472176948259 13626555171009708265422389)
                  ·
                    refine ⟨1277489547282160149883349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13626555171009708265422389 1277489547282160149883349)
                    ·
                      rfl

theorem cell23_7463706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_7463706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463706 prefixEnd_7463706 := by exact prefixLift 7463706
  have htrace : WordTrace (prefixWord ++ tailWord_7463706) baseStart_7463706 baseEnd_7463706 := by
    simpa [prefixWord, tailWord_7463706, baseEnd_7463706] using wordTrace_append hprefix tailTrace_7463706
  have hstable : (prefixWord ++ tailWord_7463706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463706).length < 2 ^ (prefixWord ++ tailWord_7463706).sum := by decide
  have hdescent : baseEnd_7463706 < baseStart_7463706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463726 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7463726 : Nat := 118140960795 + 7463726 * 2 ^ 59
def prefixEnd_7463726 : Nat := 4983230072969 + 3 ^ 40 * 7463726 * 2
def baseEnd_7463726 : Nat := 3832478911459570371399955

theorem tailTrace_7463726 : CollatzResearch.WordTrace tailWord_7463726 prefixEnd_7463726 3832478911459570371399955 := by
  unfold tailWord_7463726
  simp only [CollatzResearch.WordTrace]
  refine ⟨34028056419775359970203379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181482967572135253174418021 34028056419775359970203379)
  ·
    refine ⟨51042084629663039955305069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34028056419775359970203379 51042084629663039955305069)
    ·
      refine ⟨19140781736123639983239401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51042084629663039955305069 19140781736123639983239401)
      ·
        refine ⟨14355586302092729987429551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19140781736123639983239401 14355586302092729987429551)
        ·
          refine ⟨21533379453139094981144327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355586302092729987429551 21533379453139094981144327)
          ·
            refine ⟨32300069179708642471716491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21533379453139094981144327 32300069179708642471716491)
            ·
              refine ⟨48450103769562963707574737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32300069179708642471716491 48450103769562963707574737)
              ·
                refine ⟨36337577827172222780681053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48450103769562963707574737 36337577827172222780681053)
                ·
                  refine ⟨13626591685189583542755395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36337577827172222780681053 13626591685189583542755395)
                  ·
                    refine ⟨20439887527784375314133093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13626591685189583542755395 20439887527784375314133093)
                    ·
                      refine ⟨3832478911459570371399955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20439887527784375314133093 3832478911459570371399955)
                      ·
                        rfl

theorem cell23_7463726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7463726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463726 prefixEnd_7463726 := by exact prefixLift 7463726
  have htrace : WordTrace (prefixWord ++ tailWord_7463726) baseStart_7463726 baseEnd_7463726 := by
    simpa [prefixWord, tailWord_7463726, baseEnd_7463726] using wordTrace_append hprefix tailTrace_7463726
  have hstable : (prefixWord ++ tailWord_7463726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463726).length < 2 ^ (prefixWord ++ tailWord_7463726).sum := by decide
  have hdescent : baseEnd_7463726 < baseStart_7463726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463729 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_7463729 : Nat := 118140960795 + 7463729 * 2 ^ 59
def prefixEnd_7463729 : Nat := 4983230072969 + 3 ^ 40 * 7463729 * 2
def baseEnd_7463729 : Nat := 3832480451901533859662441

theorem tailTrace_7463729 : CollatzResearch.WordTrace tailWord_7463729 prefixEnd_7463729 3832480451901533859662441 := by
  unfold tailWord_7463729
  simp only [CollatzResearch.WordTrace]
  refine ⟨272224560777192011273986241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181483040518128007515990827 272224560777192011273986241)
  ·
    refine ⟨204168420582894008455489681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272224560777192011273986241 204168420582894008455489681)
    ·
      refine ⟨153126315437170506341617261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204168420582894008455489681 153126315437170506341617261)
      ·
        refine ⟨57422368288938939878106473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153126315437170506341617261 57422368288938939878106473)
        ·
          refine ⟨43066776216704204908579855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57422368288938939878106473 43066776216704204908579855)
          ·
            refine ⟨64600164325056307362869783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43066776216704204908579855 64600164325056307362869783)
            ·
              refine ⟨96900246487584461044304675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64600164325056307362869783 96900246487584461044304675)
              ·
                refine ⟨145350369731376691566457013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96900246487584461044304675 145350369731376691566457013)
                ·
                  refine ⟨13626597162316564834355345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145350369731376691566457013 13626597162316564834355345)
                  ·
                    refine ⟨10219947871737423625766509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13626597162316564834355345 10219947871737423625766509)
                    ·
                      refine ⟨3832480451901533859662441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10219947871737423625766509 3832480451901533859662441)
                      ·
                        rfl

theorem cell23_7463729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_7463729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463729 prefixEnd_7463729 := by exact prefixLift 7463729
  have htrace : WordTrace (prefixWord ++ tailWord_7463729) baseStart_7463729 baseEnd_7463729 := by
    simpa [prefixWord, tailWord_7463729, baseEnd_7463729] using wordTrace_append hprefix tailTrace_7463729
  have hstable : (prefixWord ++ tailWord_7463729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463729).length < 2 ^ (prefixWord ++ tailWord_7463729).sum := by decide
  have hdescent : baseEnd_7463729 < baseStart_7463729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463743 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 3, 2, 2]
def baseStart_7463743 : Nat := 118140960795 + 7463743 * 2 ^ 59
def prefixEnd_7463743 : Nat := 4983230072969 + 3 ^ 40 * 7463743 * 2
def baseEnd_7463743 : Nat := 3832487640630696804887377

theorem tailTrace_7463743 : CollatzResearch.WordTrace tailWord_7463743 prefixEnd_7463743 3832487640630696804887377 := by
  unfold tailWord_7463743
  simp only [CollatzResearch.WordTrace]
  refine ⟨272225071399141291664995883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181483380932760861109997255 272225071399141291664995883)
  ·
    refine ⟨408337607098711937497493825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272225071399141291664995883 408337607098711937497493825)
    ·
      refine ⟨306253205324033953123120369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408337607098711937497493825 306253205324033953123120369)
      ·
        refine ⟨229689903993025464842340277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306253205324033953123120369 229689903993025464842340277)
        ·
          refine ⟨21533428499346137328969401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229689903993025464842340277 21533428499346137328969401)
          ·
            refine ⟨16150071374509602996727051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21533428499346137328969401 16150071374509602996727051)
            ·
              refine ⟨24225107061764404495090577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150071374509602996727051 24225107061764404495090577)
              ·
                refine ⟨18168830296323303371317933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24225107061764404495090577 18168830296323303371317933)
                ·
                  refine ⟨6813311361121238764244225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18168830296323303371317933 6813311361121238764244225)
                  ·
                    refine ⟨5109983520840929073183169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813311361121238764244225 5109983520840929073183169)
                    ·
                      refine ⟨3832487640630696804887377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5109983520840929073183169 3832487640630696804887377)
                      ·
                        rfl

theorem cell23_7463743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_7463743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463743 prefixEnd_7463743 := by exact prefixLift 7463743
  have htrace : WordTrace (prefixWord ++ tailWord_7463743) baseStart_7463743 baseEnd_7463743 := by
    simpa [prefixWord, tailWord_7463743, baseEnd_7463743] using wordTrace_append hprefix tailTrace_7463743
  have hstable : (prefixWord ++ tailWord_7463743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463743).length < 2 ^ (prefixWord ++ tailWord_7463743).sum := by decide
  have hdescent : baseEnd_7463743 < baseStart_7463743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463757 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7463757 : Nat := 118140960795 + 7463757 * 2 ^ 59
def prefixEnd_7463757 : Nat := 4983230072969 + 3 ^ 40 * 7463757 * 2
def baseEnd_7463757 : Nat := 1277498276453286583370771

theorem tailTrace_7463757 : CollatzResearch.WordTrace tailWord_7463757 prefixEnd_7463757 1277498276453286583370771 := by
  unfold tailWord_7463757
  simp only [CollatzResearch.WordTrace]
  refine ⟨272225582021090572056005525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181483721347393714704003683 272225582021090572056005525)
  ·
    refine ⟨12760574157238620565125259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272225582021090572056005525 12760574157238620565125259)
    ·
      refine ⟨19140861235857930847687889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12760574157238620565125259 19140861235857930847687889)
      ·
        refine ⟨14355645926893448135765917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19140861235857930847687889 14355645926893448135765917)
        ·
          refine ⟨5383367222585043050912219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14355645926893448135765917 5383367222585043050912219)
          ·
            refine ⟨8075050833877564576368329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383367222585043050912219 8075050833877564576368329)
            ·
              refine ⟨6056288125408173432276247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8075050833877564576368329 6056288125408173432276247)
              ·
                refine ⟨9084432188112260148414371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056288125408173432276247 9084432188112260148414371)
                ·
                  refine ⟨13626648282168390222621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084432188112260148414371 13626648282168390222621557)
                  ·
                    refine ⟨1277498276453286583370771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13626648282168390222621557 1277498276453286583370771)
                    ·
                      rfl

theorem cell23_7463757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7463757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463757 prefixEnd_7463757 := by exact prefixLift 7463757
  have htrace : WordTrace (prefixWord ++ tailWord_7463757) baseStart_7463757 baseEnd_7463757 := by
    simpa [prefixWord, tailWord_7463757, baseEnd_7463757] using wordTrace_append hprefix tailTrace_7463757
  have hstable : (prefixWord ++ tailWord_7463757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463757).length < 2 ^ (prefixWord ++ tailWord_7463757).sum := by decide
  have hdescent : baseEnd_7463757 < baseStart_7463757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463776 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_7463776 : Nat := 118140960795 + 7463776 * 2 ^ 59
def prefixEnd_7463776 : Nat := 4983230072969 + 3 ^ 40 * 7463776 * 2
def baseEnd_7463776 : Nat := 3832504585492295175774725

theorem tailTrace_7463776 : CollatzResearch.WordTrace tailWord_7463776 prefixEnd_7463776 3832504585492295175774725 := by
  unfold tailWord_7463776
  simp only [CollatzResearch.WordTrace]
  refine ⟨136113137504010869150473591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181484183338681158867298121 136113137504010869150473591)
  ·
    refine ⟨204169706256016303725710387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136113137504010869150473591 204169706256016303725710387)
    ·
      refine ⟨306254559384024455588565581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204169706256016303725710387 306254559384024455588565581)
      ·
        refine ⟨114845459769009170845712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306254559384024455588565581 114845459769009170845712093)
        ·
          refine ⟨43067047413378439067142035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114845459769009170845712093 43067047413378439067142035)
          ·
            refine ⟨64600571120067658600713053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43067047413378439067142035 64600571120067658600713053)
            ·
              refine ⟨24225214170025371975267395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64600571120067658600713053 24225214170025371975267395)
              ·
                refine ⟨36337821255038057962901093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24225214170025371975267395 36337821255038057962901093)
                ·
                  refine ⟨6813341485319635868043955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36337821255038057962901093 6813341485319635868043955)
                  ·
                    refine ⟨10220012227979453802065933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6813341485319635868043955 10220012227979453802065933)
                    ·
                      refine ⟨3832504585492295175774725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10220012227979453802065933 3832504585492295175774725)
                      ·
                        rfl

theorem cell23_7463776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_7463776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463776 prefixEnd_7463776 := by exact prefixLift 7463776
  have htrace : WordTrace (prefixWord ++ tailWord_7463776) baseStart_7463776 baseEnd_7463776 := by
    simpa [prefixWord, tailWord_7463776, baseEnd_7463776] using wordTrace_append hprefix tailTrace_7463776
  have hstable : (prefixWord ++ tailWord_7463776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463776).length < 2 ^ (prefixWord ++ tailWord_7463776).sum := by decide
  have hdescent : baseEnd_7463776 < baseStart_7463776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463790 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7463790 : Nat := 118140960795 + 7463790 * 2 ^ 59
def prefixEnd_7463790 : Nat := 4983230072969 + 3 ^ 40 * 7463790 * 2
def baseEnd_7463790 : Nat := 3832511774221458120999661

theorem tailTrace_7463790 : CollatzResearch.WordTrace tailWord_7463790 prefixEnd_7463790 3832511774221458120999661 := by
  unfold tailWord_7463790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34028348203746377336494603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181484523753314012461304549 34028348203746377336494603)
  ·
    refine ⟨51042522305619566004741905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34028348203746377336494603 51042522305619566004741905)
    ·
      refine ⟨38281891729214674503556429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51042522305619566004741905 38281891729214674503556429)
      ·
        refine ⟨14355709398455502938833661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38281891729214674503556429 14355709398455502938833661)
        ·
          refine ⟨5383391024420813602062623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14355709398455502938833661 5383391024420813602062623)
          ·
            refine ⟨8075086536631220403093935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383391024420813602062623 8075086536631220403093935)
            ·
              refine ⟨12112629804946830604640903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075086536631220403093935 12112629804946830604640903)
              ·
                refine ⟨18168944707420245906961355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12112629804946830604640903 18168944707420245906961355)
                ·
                  refine ⟨27253417061130368860442033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18168944707420245906961355 27253417061130368860442033)
                  ·
                    refine ⟨20440062795847776645331525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27253417061130368860442033 20440062795847776645331525)
                    ·
                      refine ⟨3832511774221458120999661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20440062795847776645331525 3832511774221458120999661)
                      ·
                        rfl

theorem cell23_7463790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7463790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463790 prefixEnd_7463790 := by exact prefixLift 7463790
  have htrace : WordTrace (prefixWord ++ tailWord_7463790) baseStart_7463790 baseEnd_7463790 := by
    simpa [prefixWord, tailWord_7463790, baseEnd_7463790] using wordTrace_append hprefix tailTrace_7463790
  have hstable : (prefixWord ++ tailWord_7463790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463790).length < 2 ^ (prefixWord ++ tailWord_7463790).sum := by decide
  have hdescent : baseEnd_7463790 < baseStart_7463790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463833 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 2, 2, 2]
def baseStart_7463833 : Nat := 118140960795 + 7463833 * 2 ^ 59
def prefixEnd_7463833 : Nat := 4983230072969 + 3 ^ 40 * 7463833 * 2
def baseEnd_7463833 : Nat := 3832533853889601452761963

theorem tailTrace_7463833 : CollatzResearch.WordTrace tailWord_7463833 prefixEnd_7463833 3832533853889601452761963 := by
  unfold tailWord_7463833
  simp only [CollatzResearch.WordTrace]
  refine ⟨272228353968815237035772153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181485569312543491357181435 272228353968815237035772153)
  ·
    refine ⟨204171265476611427776829115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272228353968815237035772153 204171265476611427776829115)
    ·
      refine ⟨306256898214917141665243673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204171265476611427776829115 306256898214917141665243673)
      ·
        refine ⟨229692673661187856248932755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306256898214917141665243673 229692673661187856248932755)
        ·
          refine ⟨344539010491781784373399133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229692673661187856248932755 344539010491781784373399133)
          ·
            refine ⟨129202128934418169140024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344539010491781784373399133 129202128934418169140024675)
            ·
              refine ⟨193803193401627253710037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129202128934418169140024675 193803193401627253710037013)
              ·
                refine ⟨9084524690701277517657985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193803193401627253710037013 9084524690701277517657985)
                ·
                  refine ⟨6813393518025958138243489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9084524690701277517657985 6813393518025958138243489)
                  ·
                    refine ⟨5110045138519468603682617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813393518025958138243489 5110045138519468603682617)
                    ·
                      refine ⟨3832533853889601452761963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110045138519468603682617 3832533853889601452761963)
                      ·
                        rfl

theorem cell23_7463833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_7463833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463833 prefixEnd_7463833 := by exact prefixLift 7463833
  have htrace : WordTrace (prefixWord ++ tailWord_7463833) baseStart_7463833 baseEnd_7463833 := by
    simpa [prefixWord, tailWord_7463833, baseEnd_7463833] using wordTrace_append hprefix tailTrace_7463833
  have hstable : (prefixWord ++ tailWord_7463833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463833).length < 2 ^ (prefixWord ++ tailWord_7463833).sum := by decide
  have hdescent : baseEnd_7463833 < baseStart_7463833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463849 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_7463849 : Nat := 118140960795 + 7463849 * 2 ^ 59
def prefixEnd_7463849 : Nat := 4983230072969 + 3 ^ 40 * 7463849 * 2
def baseEnd_7463849 : Nat := 3832542069580073390161889

theorem tailTrace_7463849 : CollatzResearch.WordTrace tailWord_7463849 prefixEnd_7463849 3832542069580073390161889 := by
  unfold tailWord_7463849
  simp only [CollatzResearch.WordTrace]
  refine ⟨272228937536757271768354601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181485958357838181178903067 272228937536757271768354601)
  ·
    refine ⟨204171703152567953826265951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272228937536757271768354601 204171703152567953826265951)
    ·
      refine ⟨306257554728851930739398927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204171703152567953826265951 306257554728851930739398927)
      ·
        refine ⟨459386332093277896109098391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306257554728851930739398927 459386332093277896109098391)
        ·
          refine ⟨689079498139916844163647587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459386332093277896109098391 689079498139916844163647587)
          ·
            refine ⟨1033619247209875266245471381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689079498139916844163647587 1033619247209875266245471381)
            ·
              refine ⟨48450902212962903105256471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1033619247209875266245471381 48450902212962903105256471)
              ·
                refine ⟨72676353319444354657884707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48450902212962903105256471 72676353319444354657884707)
                ·
                  refine ⟨109014529979166531986827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72676353319444354657884707 109014529979166531986827061)
                  ·
                    refine ⟨10220112185546862373765037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109014529979166531986827061 10220112185546862373765037)
                    ·
                      refine ⟨3832542069580073390161889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10220112185546862373765037 3832542069580073390161889)
                      ·
                        rfl

theorem cell23_7463849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_7463849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463849 prefixEnd_7463849 := by exact prefixLift 7463849
  have htrace : WordTrace (prefixWord ++ tailWord_7463849) baseStart_7463849 baseEnd_7463849 := by
    simpa [prefixWord, tailWord_7463849, baseEnd_7463849] using wordTrace_append hprefix tailTrace_7463849
  have hstable : (prefixWord ++ tailWord_7463849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463849).length < 2 ^ (prefixWord ++ tailWord_7463849).sum := by decide
  have hdescent : baseEnd_7463849 < baseStart_7463849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463879 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_7463879 : Nat := 118140960795 + 7463879 * 2 ^ 59
def prefixEnd_7463879 : Nat := 4983230072969 + 3 ^ 40 * 7463879 * 2
def baseEnd_7463879 : Nat := 3832557473999708272786751

theorem tailTrace_7463879 : CollatzResearch.WordTrace tailWord_7463879 prefixEnd_7463879 3832557473999708272786751 := by
  unfold tailWord_7463879
  simp only [CollatzResearch.WordTrace]
  refine ⟨272230031726648586891946691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181486687817765724594631127 272230031726648586891946691)
  ·
    refine ⟨408345047589972880337920037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272230031726648586891946691 408345047589972880337920037)
    ·
      refine ⟨76564696423119915063360007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408345047589972880337920037 76564696423119915063360007)
      ·
        refine ⟨114847044634679872595040011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76564696423119915063360007 114847044634679872595040011)
        ·
          refine ⟨172270566952019808892560017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114847044634679872595040011 172270566952019808892560017)
          ·
            refine ⟨129202925214014856669420013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172270566952019808892560017 129202925214014856669420013)
            ·
              refine ⟨48451096955255571251032505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129202925214014856669420013 48451096955255571251032505)
              ·
                refine ⟨36338322716441678438274379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48451096955255571251032505 36338322716441678438274379)
                ·
                  refine ⟨54507484074662517657411569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36338322716441678438274379 54507484074662517657411569)
                  ·
                    refine ⟨40880613055996888243058677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54507484074662517657411569 40880613055996888243058677)
                    ·
                      refine ⟨3832557473999708272786751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40880613055996888243058677 3832557473999708272786751)
                      ·
                        rfl

theorem cell23_7463879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_7463879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463879 prefixEnd_7463879 := by exact prefixLift 7463879
  have htrace : WordTrace (prefixWord ++ tailWord_7463879) baseStart_7463879 baseEnd_7463879 := by
    simpa [prefixWord, tailWord_7463879, baseEnd_7463879] using wordTrace_append hprefix tailTrace_7463879
  have hstable : (prefixWord ++ tailWord_7463879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463879).length < 2 ^ (prefixWord ++ tailWord_7463879).sum := by decide
  have hdescent : baseEnd_7463879 < baseStart_7463879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463886 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_7463886 : Nat := 118140960795 + 7463886 * 2 ^ 59
def prefixEnd_7463886 : Nat := 4983230072969 + 3 ^ 40 * 7463886 * 2
def baseEnd_7463886 : Nat := 1277520356121429915133073

theorem tailTrace_7463886 : CollatzResearch.WordTrace tailWord_7463886 prefixEnd_7463886 1277520356121429915133073 := by
  unfold tailWord_7463886
  simp only [CollatzResearch.WordTrace]
  refine ⟨34028785879702903385931439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181486858025082151391634341 34028785879702903385931439)
  ·
    refine ⟨51043178819554355078897159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34028785879702903385931439 51043178819554355078897159)
    ·
      refine ⟨76564768229331532618345739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51043178819554355078897159 76564768229331532618345739)
      ·
        refine ⟨114847152343997298927518609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76564768229331532618345739 114847152343997298927518609)
        ·
          refine ⟨86135364257997974195638957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114847152343997298927518609 86135364257997974195638957)
          ·
            refine ⟨32300761596749240323364609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86135364257997974195638957 32300761596749240323364609)
            ·
              refine ⟨24225571197561930242523457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32300761596749240323364609 24225571197561930242523457)
              ·
                refine ⟨18169178398171447681892593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24225571197561930242523457 18169178398171447681892593)
                ·
                  refine ⟨13626883798628585761419445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18169178398171447681892593 13626883798628585761419445)
                  ·
                    refine ⟨1277520356121429915133073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13626883798628585761419445 1277520356121429915133073)
                    ·
                      rfl

theorem cell23_7463886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_7463886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463886 prefixEnd_7463886 := by exact prefixLift 7463886
  have htrace : WordTrace (prefixWord ++ tailWord_7463886) baseStart_7463886 baseEnd_7463886 := by
    simpa [prefixWord, tailWord_7463886, baseEnd_7463886] using wordTrace_append hprefix tailTrace_7463886
  have hstable : (prefixWord ++ tailWord_7463886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463886).length < 2 ^ (prefixWord ++ tailWord_7463886).sum := by decide
  have hdescent : baseEnd_7463886 < baseStart_7463886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463890 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_7463890 : Nat := 118140960795 + 7463890 * 2 ^ 59
def prefixEnd_7463890 : Nat := 4983230072969 + 3 ^ 40 * 7463890 * 2
def baseEnd_7463890 : Nat := 425840346920767525527689

theorem tailTrace_7463890 : CollatzResearch.WordTrace tailWord_7463890 prefixEnd_7463890 425840346920767525527689 := by
  unfold tailWord_7463890
  simp only [CollatzResearch.WordTrace]
  refine ⟨68057608232402183942649281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181486955286405823847064749 68057608232402183942649281)
  ·
    refine ⟨51043206174301637956986961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68057608232402183942649281 51043206174301637956986961)
    ·
      refine ⟨38282404630726228467740221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51043206174301637956986961 38282404630726228467740221)
      ·
        refine ⟨14355901736522335675402583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38282404630726228467740221 14355901736522335675402583)
        ·
          refine ⟨21533852604783503513103875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14355901736522335675402583 21533852604783503513103875)
          ·
            refine ⟨32300778907175255269655813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21533852604783503513103875 32300778907175255269655813)
            ·
              refine ⟨6056396045095360363060465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32300778907175255269655813 6056396045095360363060465)
              ·
                refine ⟨4542297033821520272295349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056396045095360363060465 4542297033821520272295349)
                ·
                  refine ⟨425840346920767525527689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4542297033821520272295349 425840346920767525527689)
                  ·
                    rfl

theorem cell23_7463890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_7463890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463890 prefixEnd_7463890 := by exact prefixLift 7463890
  have htrace : WordTrace (prefixWord ++ tailWord_7463890) baseStart_7463890 baseEnd_7463890 := by
    simpa [prefixWord, tailWord_7463890, baseEnd_7463890] using wordTrace_append hprefix tailTrace_7463890
  have hstable : (prefixWord ++ tailWord_7463890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463890).length < 2 ^ (prefixWord ++ tailWord_7463890).sum := by decide
  have hdescent : baseEnd_7463890 < baseStart_7463890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463929 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 8]
def baseStart_7463929 : Nat := 118140960795 + 7463929 * 2 ^ 59
def prefixEnd_7463929 : Nat := 4983230072969 + 3 ^ 40 * 7463929 * 2
def baseEnd_7463929 : Nat := 425842572003603675240169

theorem tailTrace_7463929 : CollatzResearch.WordTrace tailWord_7463929 prefixEnd_7463929 425842572003603675240169 := by
  unfold tailWord_7463929
  simp only [CollatzResearch.WordTrace]
  refine ⟨272231855376467445431266841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181487903584311630287511227 272231855376467445431266841)
  ·
    refine ⟨204173891532350584073450131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272231855376467445431266841 204173891532350584073450131)
    ·
      refine ⟨306260837298525876110175197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204173891532350584073450131 306260837298525876110175197)
      ·
        refine ⟨114847813986947203541315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306260837298525876110175197 114847813986947203541315699)
        ·
          refine ⟨172271720980420805311973549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114847813986947203541315699 172271720980420805311973549)
          ·
            refine ⟨64601895367657801991990081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172271720980420805311973549 64601895367657801991990081)
            ·
              refine ⟨48451421525743351493992561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64601895367657801991990081 48451421525743351493992561)
              ·
                refine ⟨36338566144307513620494421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48451421525743351493992561 36338566144307513620494421)
                ·
                  refine ⟨425842572003603675240169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36338566144307513620494421 425842572003603675240169)
                  ·
                    rfl

theorem cell23_7463929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_7463929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463929 prefixEnd_7463929 := by exact prefixLift 7463929
  have htrace : WordTrace (prefixWord ++ tailWord_7463929) baseStart_7463929 baseEnd_7463929 := by
    simpa [prefixWord, tailWord_7463929, baseEnd_7463929] using wordTrace_append hprefix tailTrace_7463929
  have hstable : (prefixWord ++ tailWord_7463929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463929).length < 2 ^ (prefixWord ++ tailWord_7463929).sum := by decide
  have hdescent : baseEnd_7463929 < baseStart_7463929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463946 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_7463946 : Nat := 118140960795 + 7463946 * 2 ^ 59
def prefixEnd_7463946 : Nat := 4983230072969 + 3 ^ 40 * 7463946 * 2
def baseEnd_7463946 : Nat := 425843541911506612294327

theorem tailTrace_7463946 : CollatzResearch.WordTrace tailWord_7463946 prefixEnd_7463946 425843541911506612294327 := by
  unfold tailWord_7463946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68058118854351464333658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181488316944937238223090461 68058118854351464333658923)
  ·
    refine ⟨102087178281527196500488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68058118854351464333658923 102087178281527196500488385)
    ·
      refine ⟨76565383711145397375366289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102087178281527196500488385 76565383711145397375366289)
      ·
        refine ⟨57424037783359048031524717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76565383711145397375366289 57424037783359048031524717)
        ·
          refine ⟨21534014168759643011821769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57424037783359048031524717 21534014168759643011821769)
          ·
            refine ⟨16150510626569732258866327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21534014168759643011821769 16150510626569732258866327)
            ·
              refine ⟨24225765939854598388299491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150510626569732258866327 24225765939854598388299491)
              ·
                refine ⟨36338648909781897582449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24225765939854598388299491 36338648909781897582449237)
                ·
                  refine ⟨425843541911506612294327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36338648909781897582449237 425843541911506612294327)
                  ·
                    rfl

theorem cell23_7463946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_7463946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463946 prefixEnd_7463946 := by exact prefixLift 7463946
  have htrace : WordTrace (prefixWord ++ tailWord_7463946) baseStart_7463946 baseEnd_7463946 := by
    simpa [prefixWord, tailWord_7463946, baseEnd_7463946] using wordTrace_append hprefix tailTrace_7463946
  have hstable : (prefixWord ++ tailWord_7463946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463946).length < 2 ^ (prefixWord ++ tailWord_7463946).sum := by decide
  have hdescent : baseEnd_7463946 < baseStart_7463946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463950 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7463950 : Nat := 118140960795 + 7463950 * 2 ^ 59
def prefixEnd_7463950 : Nat := 4983230072969 + 3 ^ 40 * 7463950 * 2
def baseEnd_7463950 : Nat := 1277531310375392498332975

theorem tailTrace_7463950 : CollatzResearch.WordTrace tailWord_7463950 prefixEnd_7463950 1277531310375392498332975 := by
  unfold tailWord_7463950
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029077663673920752222663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181488414206260910678520869 34029077663673920752222663)
  ·
    refine ⟨51043616495510881128333995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34029077663673920752222663 51043616495510881128333995)
    ·
      refine ⟨76565424743266321692500993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51043616495510881128333995 76565424743266321692500993)
      ·
        refine ⟨57424068557449741269375745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76565424743266321692500993 57424068557449741269375745)
        ·
          refine ⟨43068051418087305952031809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57424068557449741269375745 43068051418087305952031809)
          ·
            refine ⟨32301038563565479464023857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43068051418087305952031809 32301038563565479464023857)
            ·
              refine ⟨24225778922674109598017893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32301038563565479464023857 24225778922674109598017893)
              ·
                refine ⟨4542333548001395549628355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24225778922674109598017893 4542333548001395549628355)
                ·
                  refine ⟨6813500322002093324442533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542333548001395549628355 6813500322002093324442533)
                  ·
                    refine ⟨1277531310375392498332975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813500322002093324442533 1277531310375392498332975)
                    ·
                      rfl

theorem cell23_7463950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7463950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463950 prefixEnd_7463950 := by exact prefixLift 7463950
  have htrace : WordTrace (prefixWord ++ tailWord_7463950) baseStart_7463950 baseEnd_7463950 := by
    simpa [prefixWord, tailWord_7463950, baseEnd_7463950] using wordTrace_append hprefix tailTrace_7463950
  have hstable : (prefixWord ++ tailWord_7463950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463950).length < 2 ^ (prefixWord ++ tailWord_7463950).sum := by decide
  have hdescent : baseEnd_7463950 < baseStart_7463950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463973 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_7463973 : Nat := 118140960795 + 7463973 * 2 ^ 59
def prefixEnd_7463973 : Nat := 4983230072969 + 3 ^ 40 * 7463973 * 2
def baseEnd_7463973 : Nat := 3832605741181230905011319

theorem tailTrace_7463973 : CollatzResearch.WordTrace tailWord_7463973 prefixEnd_7463973 3832605741181230905011319 := by
  unfold tailWord_7463973
  simp only [CollatzResearch.WordTrace]
  refine ⟨272233460188308040945868573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181488973458872027297245715 272233460188308040945868573)
  ·
    refine ⟨102087547570615515354700715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272233460188308040945868573 102087547570615515354700715)
    ·
      refine ⟨153131321355923273032051073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102087547570615515354700715 153131321355923273032051073)
      ·
        refine ⟨114848491016942454774038305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153131321355923273032051073 114848491016942454774038305)
        ·
          refine ⟨86136368262706841080528729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114848491016942454774038305 86136368262706841080528729)
          ·
            refine ⟨64602276197030130810396547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86136368262706841080528729 64602276197030130810396547)
            ·
              refine ⟨96903414295545196215594821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64602276197030130810396547 96903414295545196215594821)
              ·
                refine ⟨18169390180414724290424029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96903414295545196215594821 18169390180414724290424029)
                ·
                  refine ⟨6813521317655521608909011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18169390180414724290424029 6813521317655521608909011)
                  ·
                    refine ⟨10220281976483282413363517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6813521317655521608909011 10220281976483282413363517)
                    ·
                      refine ⟨3832605741181230905011319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10220281976483282413363517 3832605741181230905011319)
                      ·
                        rfl

theorem cell23_7463973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_7463973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463973 prefixEnd_7463973 := by exact prefixLift 7463973
  have htrace : WordTrace (prefixWord ++ tailWord_7463973) baseStart_7463973 baseEnd_7463973 := by
    simpa [prefixWord, tailWord_7463973, baseEnd_7463973] using wordTrace_append hprefix tailTrace_7463973
  have hstable : (prefixWord ++ tailWord_7463973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463973).length < 2 ^ (prefixWord ++ tailWord_7463973).sum := by decide
  have hdescent : baseEnd_7463973 < baseStart_7463973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7463993 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_7463993 : Nat := 118140960795 + 7463993 * 2 ^ 59
def prefixEnd_7463993 : Nat := 4983230072969 + 3 ^ 40 * 7463993 * 2
def baseEnd_7463993 : Nat := 1277538670264773608920409

theorem tailTrace_7463993 : CollatzResearch.WordTrace tailWord_7463993 prefixEnd_7463993 1277538670264773608920409 := by
  unfold tailWord_7463993
  simp only [CollatzResearch.WordTrace]
  refine ⟨272234189648235584361596633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181489459765490389574397755 272234189648235584361596633)
  ·
    refine ⟨204175642236176688271197475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272234189648235584361596633 204175642236176688271197475)
    ·
      refine ⟨306263463354265032406796213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204175642236176688271197475 306263463354265032406796213)
      ·
        refine ⟨28712199689462346788137145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306263463354265032406796213 28712199689462346788137145)
        ·
          refine ⟨21534149767096760091102859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28712199689462346788137145 21534149767096760091102859)
          ·
            refine ⟨32301224650645140136654289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534149767096760091102859 32301224650645140136654289)
            ·
              refine ⟨24225918487983855102490717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32301224650645140136654289 24225918487983855102490717)
              ·
                refine ⟨9084719432993945663434019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24225918487983855102490717 9084719432993945663434019)
                ·
                  refine ⟨13627079149490918495151029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9084719432993945663434019 13627079149490918495151029)
                  ·
                    refine ⟨1277538670264773608920409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13627079149490918495151029 1277538670264773608920409)
                    ·
                      rfl

theorem cell23_7463993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_7463993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7463993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7463993 prefixEnd_7463993 := by exact prefixLift 7463993
  have htrace : WordTrace (prefixWord ++ tailWord_7463993) baseStart_7463993 baseEnd_7463993 := by
    simpa [prefixWord, tailWord_7463993, baseEnd_7463993] using wordTrace_append hprefix tailTrace_7463993
  have hstable : (prefixWord ++ tailWord_7463993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7463993).length < 2 ^ (prefixWord ++ tailWord_7463993).sum := by decide
  have hdescent : baseEnd_7463993 < baseStart_7463993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7463993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464019 : List Nat := [1, 1, 1, 2, 1, 1, 2, 14]
def baseStart_7464019 : Nat := 118140960795 + 7464019 * 2 ^ 59
def prefixEnd_7464019 : Nat := 4983230072969 + 3 ^ 40 * 7464019 * 2
def baseEnd_7464019 : Nat := 141949235603382878705041

theorem tailTrace_7464019 : CollatzResearch.WordTrace tailWord_7464019 prefixEnd_7464019 141949235603382878705041 := by
  unfold tailWord_7464019
  simp only [CollatzResearch.WordTrace]
  refine ⟨272235137946141390802043111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181490091964094260534695407 272235137946141390802043111)
  ·
    refine ⟨408352706919212086203064667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272235137946141390802043111 408352706919212086203064667)
    ·
      refine ⟨612529060378818129304597001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408352706919212086203064667 612529060378818129304597001)
      ·
        refine ⟨459396795284113596978447751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612529060378818129304597001 459396795284113596978447751)
        ·
          refine ⟨689095192926170395467671627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459396795284113596978447751 689095192926170395467671627)
          ·
            refine ⟨1033642789389255593201507441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689095192926170395467671627 1033642789389255593201507441)
            ·
              refine ⟨775232092041941694901130581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033642789389255593201507441 775232092041941694901130581)
              ·
                refine ⟨141949235603382878705041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 775232092041941694901130581 141949235603382878705041)
                ·
                  rfl

theorem cell23_7464019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 14].length) (baseStart_7464019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464019 prefixEnd_7464019 := by exact prefixLift 7464019
  have htrace : WordTrace (prefixWord ++ tailWord_7464019) baseStart_7464019 baseEnd_7464019 := by
    simpa [prefixWord, tailWord_7464019, baseEnd_7464019] using wordTrace_append hprefix tailTrace_7464019
  have hstable : (prefixWord ++ tailWord_7464019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464019).length < 2 ^ (prefixWord ++ tailWord_7464019).sum := by decide
  have hdescent : baseEnd_7464019 < baseStart_7464019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464040 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_7464040 : Nat := 118140960795 + 7464040 * 2 ^ 59
def prefixEnd_7464040 : Nat := 4983230072969 + 3 ^ 40 * 7464040 * 2
def baseEnd_7464040 : Nat := 1277546714795027380957837

theorem tailTrace_7464040 : CollatzResearch.WordTrace tailWord_7464040 prefixEnd_7464040 1277546714795027380957837 := by
  unfold tailWord_7464040
  simp only [CollatzResearch.WordTrace]
  refine ⟨136117951939532655694278787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181490602586043540925705049 136117951939532655694278787)
  ·
    refine ⟨204176927909298983541418181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136117951939532655694278787 204176927909298983541418181)
    ·
      refine ⟨38283173982993559414015909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204176927909298983541418181 38283173982993559414015909)
      ·
        refine ⟨7178095121811292390127983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38283173982993559414015909 7178095121811292390127983)
        ·
          refine ⟨10767142682716938585191975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178095121811292390127983 10767142682716938585191975)
          ·
            refine ⟨16150714024075407877787963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10767142682716938585191975 16150714024075407877787963)
            ·
              refine ⟨24226071036113111816681945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150714024075407877787963 24226071036113111816681945)
              ·
                refine ⟨18169553277084833862511459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24226071036113111816681945 18169553277084833862511459)
                ·
                  refine ⟨27254329915627250793767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18169553277084833862511459 27254329915627250793767189)
                  ·
                    refine ⟨1277546714795027380957837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27254329915627250793767189 1277546714795027380957837)
                    ·
                      rfl

theorem cell23_7464040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_7464040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464040 prefixEnd_7464040 := by exact prefixLift 7464040
  have htrace : WordTrace (prefixWord ++ tailWord_7464040) baseStart_7464040 baseEnd_7464040 := by
    simpa [prefixWord, tailWord_7464040, baseEnd_7464040] using wordTrace_append hprefix tailTrace_7464040
  have hstable : (prefixWord ++ tailWord_7464040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464040).length < 2 ^ (prefixWord ++ tailWord_7464040).sum := by decide
  have hdescent : baseEnd_7464040 < baseStart_7464040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464047 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 1, 2, 2]
def baseStart_7464047 : Nat := 118140960795 + 7464047 * 2 ^ 59
def prefixEnd_7464047 : Nat := 4983230072969 + 3 ^ 40 * 7464047 * 2
def baseEnd_7464047 : Nat := 3832643738749663615485979

theorem tailTrace_7464047 : CollatzResearch.WordTrace tailWord_7464047 prefixEnd_7464047 3832643738749663615485979 := by
  unfold tailWord_7464047
  simp only [CollatzResearch.WordTrace]
  refine ⟨272236159190039951584062395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181490772793359967722708263 272236159190039951584062395)
  ·
    refine ⟨408354238785059927376093593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272236159190039951584062395 408354238785059927376093593)
    ·
      refine ⟨306265679088794945532070195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408354238785059927376093593 306265679088794945532070195)
      ·
        refine ⟨459398518633192418298105293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306265679088794945532070195 459398518633192418298105293)
        ·
          refine ⟨172274444487447156861789485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459398518633192418298105293 172274444487447156861789485)
          ·
            refine ⟨64602916682792683823171057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172274444487447156861789485 64602916682792683823171057)
            ·
              refine ⟨48452187512094512867378293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64602916682792683823171057 48452187512094512867378293)
              ·
                refine ⟨4542392579258860581316715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48452187512094512867378293 4542392579258860581316715)
                ·
                  refine ⟨6813588868888290871975073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542392579258860581316715 6813588868888290871975073)
                  ·
                    refine ⟨5110191651666218153981305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813588868888290871975073 5110191651666218153981305)
                    ·
                      refine ⟨3832643738749663615485979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110191651666218153981305 3832643738749663615485979)
                      ·
                        rfl

theorem cell23_7464047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 1, 2, 2].length) (baseStart_7464047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464047 prefixEnd_7464047 := by exact prefixLift 7464047
  have htrace : WordTrace (prefixWord ++ tailWord_7464047) baseStart_7464047 baseEnd_7464047 := by
    simpa [prefixWord, tailWord_7464047, baseEnd_7464047] using wordTrace_append hprefix tailTrace_7464047
  have hstable : (prefixWord ++ tailWord_7464047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464047).length < 2 ^ (prefixWord ++ tailWord_7464047).sum := by decide
  have hdescent : baseEnd_7464047 < baseStart_7464047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464053 : List Nat := [1, 3, 4, 3, 1, 11]
def baseStart_7464053 : Nat := 118140960795 + 7464053 * 2 ^ 59
def prefixEnd_7464053 : Nat := 4983230072969 + 3 ^ 40 * 7464053 * 2
def baseEnd_7464053 : Nat := 15772209134294611489757

theorem tailTrace_7464053 : CollatzResearch.WordTrace tailWord_7464053 prefixEnd_7464053 15772209134294611489757 := by
  unfold tailWord_7464053
  simp only [CollatzResearch.WordTrace]
  refine ⟨272236378028018214608780813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181490918685345476405853875 272236378028018214608780813)
  ·
    refine ⟨102088641760506830478292805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272236378028018214608780813 102088641760506830478292805)
    ·
      refine ⟨19141620330095030714679901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102088641760506830478292805 19141620330095030714679901)
      ·
        refine ⟨7178107623785636518004963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19141620330095030714679901 7178107623785636518004963)
        ·
          refine ⟨10767161435678454777007445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178107623785636518004963 10767161435678454777007445)
          ·
            refine ⟨15772209134294611489757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10767161435678454777007445 15772209134294611489757)
            ·
              rfl

theorem cell23_7464053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 11].length) (baseStart_7464053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464053 prefixEnd_7464053 := by exact prefixLift 7464053
  have htrace : WordTrace (prefixWord ++ tailWord_7464053) baseStart_7464053 baseEnd_7464053 := by
    simpa [prefixWord, tailWord_7464053, baseEnd_7464053] using wordTrace_append hprefix tailTrace_7464053
  have hstable : (prefixWord ++ tailWord_7464053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464053).length < 2 ^ (prefixWord ++ tailWord_7464053).sum := by decide
  have hdescent : baseEnd_7464053 < baseStart_7464053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464064 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 1, 2, 2]
def baseStart_7464064 : Nat := 118140960795 + 7464064 * 2 ^ 59
def prefixEnd_7464064 : Nat := 4983230072969 + 3 ^ 40 * 7464064 * 2
def baseEnd_7464064 : Nat := 3832652467920790048973401

theorem tailTrace_7464064 : CollatzResearch.WordTrace tailWord_7464064 prefixEnd_7464064 3832652467920790048973401 := by
  unfold tailWord_7464064
  simp only [CollatzResearch.WordTrace]
  refine ⟨136118389615489181743715623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181491186153985575658287497 136118389615489181743715623)
  ·
    refine ⟨204177584423233772615573435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136118389615489181743715623 204177584423233772615573435)
    ·
      refine ⟨306266376634850658923360153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204177584423233772615573435 306266376634850658923360153)
      ·
        refine ⟨229699782476137994192520115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306266376634850658923360153 229699782476137994192520115)
        ·
          refine ⟨344549673714206991288780173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229699782476137994192520115 344549673714206991288780173)
          ·
            refine ⟨129206127642827621733292565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344549673714206991288780173 129206127642827621733292565)
            ·
              refine ⟨6056537233257544768748089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129206127642827621733292565 6056537233257544768748089)
              ·
                refine ⟨4542402924943158576561067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6056537233257544768748089 4542402924943158576561067)
                ·
                  refine ⟨6813604387414737864841601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542402924943158576561067 6813604387414737864841601)
                  ·
                    refine ⟨5110203290561053398631201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813604387414737864841601 5110203290561053398631201)
                    ·
                      refine ⟨3832652467920790048973401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110203290561053398631201 3832652467920790048973401)
                      ·
                        rfl

theorem cell23_7464064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_7464064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464064 prefixEnd_7464064 := by exact prefixLift 7464064
  have htrace : WordTrace (prefixWord ++ tailWord_7464064) baseStart_7464064 baseEnd_7464064 := by
    simpa [prefixWord, tailWord_7464064, baseEnd_7464064] using wordTrace_append hprefix tailTrace_7464064
  have hstable : (prefixWord ++ tailWord_7464064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464064).length < 2 ^ (prefixWord ++ tailWord_7464064).sum := by decide
  have hdescent : baseEnd_7464064 < baseStart_7464064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464096 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_7464096 : Nat := 118140960795 + 7464096 * 2 ^ 59
def prefixEnd_7464096 : Nat := 4983230072969 + 3 ^ 40 * 7464096 * 2
def baseEnd_7464096 : Nat := 1277556299767244641257751

theorem tailTrace_7464096 : CollatzResearch.WordTrace tailWord_7464096 prefixEnd_7464096 1277556299767244641257751 := by
  unfold tailWord_7464096
  simp only [CollatzResearch.WordTrace]
  refine ⟨136118973183431216476298071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181491964244574955301730761 136118973183431216476298071)
  ·
    refine ⟨204178459775146824714447107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136118973183431216476298071 204178459775146824714447107)
    ·
      refine ⟨306267689662720237071670661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204178459775146824714447107 306267689662720237071670661)
      ·
        refine ⟨57425191811760044450938249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306267689662720237071670661 57425191811760044450938249)
        ·
          refine ⟨43068893858820033338203687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57425191811760044450938249 43068893858820033338203687)
          ·
            refine ⟨64603340788230050007305531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43068893858820033338203687 64603340788230050007305531)
            ·
              refine ⟨96905011182345075010958297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64603340788230050007305531 96905011182345075010958297)
              ·
                refine ⟨72678758386758806258218723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96905011182345075010958297 72678758386758806258218723)
                ·
                  refine ⟨109018137580138209387328085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72678758386758806258218723 109018137580138209387328085)
                  ·
                    refine ⟨1277556299767244641257751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109018137580138209387328085 1277556299767244641257751)
                    ·
                      rfl

theorem cell23_7464096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_7464096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464096 prefixEnd_7464096 := by exact prefixLift 7464096
  have htrace : WordTrace (prefixWord ++ tailWord_7464096) baseStart_7464096 baseEnd_7464096 := by
    simpa [prefixWord, tailWord_7464096, baseEnd_7464096] using wordTrace_append hprefix tailTrace_7464096
  have hstable : (prefixWord ++ tailWord_7464096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464096).length < 2 ^ (prefixWord ++ tailWord_7464096).sum := by decide
  have hdescent : baseEnd_7464096 < baseStart_7464096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464113 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_7464113 : Nat := 118140960795 + 7464113 * 2 ^ 59
def prefixEnd_7464113 : Nat := 4983230072969 + 3 ^ 40 * 7464113 * 2
def baseEnd_7464113 : Nat := 1277559209490953452420225

theorem tailTrace_7464113 : CollatzResearch.WordTrace tailWord_7464113 prefixEnd_7464113 1277559209490953452420225 := by
  unfold tailWord_7464113
  simp only [CollatzResearch.WordTrace]
  refine ⟨272238566407800844855964993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181492377605200563237309995 272238566407800844855964993)
  ·
    refine ⟨204178924805850633641973745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272238566407800844855964993 204178924805850633641973745)
    ·
      refine ⟨153134193604387975231480309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204178924805850633641973745 153134193604387975231480309)
      ·
        refine ⟨14356330650411372677951279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153134193604387975231480309 14356330650411372677951279)
        ·
          refine ⟨21534495975617059016926919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356330650411372677951279 21534495975617059016926919)
          ·
            refine ⟨32301743963425588525390379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534495975617059016926919 32301743963425588525390379)
            ·
              refine ⟨48452615945138382788085569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32301743963425588525390379 48452615945138382788085569)
              ·
                refine ⟨36339461958853787091064177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48452615945138382788085569 36339461958853787091064177)
                ·
                  refine ⟨27254596469140340318298133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36339461958853787091064177 27254596469140340318298133)
                  ·
                    refine ⟨1277559209490953452420225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27254596469140340318298133 1277559209490953452420225)
                    ·
                      rfl

theorem cell23_7464113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_7464113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464113 prefixEnd_7464113 := by exact prefixLift 7464113
  have htrace : WordTrace (prefixWord ++ tailWord_7464113) baseStart_7464113 baseEnd_7464113 := by
    simpa [prefixWord, tailWord_7464113, baseEnd_7464113] using wordTrace_append hprefix tailTrace_7464113
  have hstable : (prefixWord ++ tailWord_7464113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464113).length < 2 ^ (prefixWord ++ tailWord_7464113).sum := by decide
  have hdescent : baseEnd_7464113 < baseStart_7464113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464160 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 5]
def baseStart_7464160 : Nat := 118140960795 + 7464160 * 2 ^ 59
def prefixEnd_7464160 : Nat := 4983230072969 + 3 ^ 40 * 7464160 * 2
def baseEnd_7464160 : Nat := 425855751340402408152551

theorem tailTrace_7464160 : CollatzResearch.WordTrace tailWord_7464160 prefixEnd_7464160 425855751340402408152551 := by
  unfold tailWord_7464160
  simp only [CollatzResearch.WordTrace]
  refine ⟨136120140319315285941462967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181493520425753714588617289 136120140319315285941462967)
  ·
    refine ⟨204180210478972928912194451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136120140319315285941462967 204180210478972928912194451)
    ·
      refine ⟨306270315718459393368291677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204180210478972928912194451 306270315718459393368291677)
      ·
        refine ⟨114851368394422272513109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306270315718459393368291677 114851368394422272513109379)
        ·
          refine ⟨172277052591633408769664069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114851368394422272513109379 172277052591633408769664069)
          ·
            refine ⟨32301947360931264144312013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172277052591633408769664069 32301947360931264144312013)
            ·
              refine ⟨12113230260349224054117005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32301947360931264144312013 12113230260349224054117005)
              ·
                refine ⟨4542461347630959020293877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12113230260349224054117005 4542461347630959020293877)
                ·
                  refine ⟨425855751340402408152551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4542461347630959020293877 425855751340402408152551)
                  ·
                    rfl

theorem cell23_7464160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 5].length) (baseStart_7464160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464160 prefixEnd_7464160 := by exact prefixLift 7464160
  have htrace : WordTrace (prefixWord ++ tailWord_7464160) baseStart_7464160 baseEnd_7464160 := by
    simpa [prefixWord, tailWord_7464160, baseEnd_7464160] using wordTrace_append hprefix tailTrace_7464160
  have hstable : (prefixWord ++ tailWord_7464160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464160).length < 2 ^ (prefixWord ++ tailWord_7464160).sum := by decide
  have hdescent : baseEnd_7464160 < baseStart_7464160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464176 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_7464176 : Nat := 118140960795 + 7464176 * 2 ^ 59
def prefixEnd_7464176 : Nat := 4983230072969 + 3 ^ 40 * 7464176 * 2
def baseEnd_7464176 : Nat := 3832709977754093610772885

theorem tailTrace_7464176 : CollatzResearch.WordTrace tailWord_7464176 prefixEnd_7464176 3832709977754093610772885 := by
  unfold tailWord_7464176
  simp only [CollatzResearch.WordTrace]
  refine ⟨136120432103286303307754191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181493909471048404410338921 136120432103286303307754191)
  ·
    refine ⟨204180648154929454961631287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136120432103286303307754191 204180648154929454961631287)
    ·
      refine ⟨306270972232394182442446931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204180648154929454961631287 306270972232394182442446931)
      ·
        refine ⟨459406458348591273663670397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306270972232394182442446931 459406458348591273663670397)
        ·
          refine ⟨172277421880721727623876399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459406458348591273663670397 172277421880721727623876399)
          ·
            refine ⟨258416132821082591435814599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172277421880721727623876399 258416132821082591435814599)
            ·
              refine ⟨387624199231623887153721899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258416132821082591435814599 387624199231623887153721899)
              ·
                refine ⟨581436298847435830730582849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387624199231623887153721899 581436298847435830730582849)
                ·
                  refine ⟨436077224135576873047937137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 581436298847435830730582849 436077224135576873047937137)
                  ·
                    refine ⟨327057918101682654785952853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 436077224135576873047937137 327057918101682654785952853)
                    ·
                      refine ⟨3832709977754093610772885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327057918101682654785952853 3832709977754093610772885)
                      ·
                        rfl

theorem cell23_7464176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_7464176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464176 prefixEnd_7464176 := by exact prefixLift 7464176
  have htrace : WordTrace (prefixWord ++ tailWord_7464176) baseStart_7464176 baseEnd_7464176 := by
    simpa [prefixWord, tailWord_7464176, baseEnd_7464176] using wordTrace_append hprefix tailTrace_7464176
  have hstable : (prefixWord ++ tailWord_7464176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464176).length < 2 ^ (prefixWord ++ tailWord_7464176).sum := by decide
  have hdescent : baseEnd_7464176 < baseStart_7464176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464188 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_7464188 : Nat := 118140960795 + 7464188 * 2 ^ 59
def prefixEnd_7464188 : Nat := 4983230072969 + 3 ^ 40 * 7464188 * 2
def baseEnd_7464188 : Nat := 3832716139521947563822831

theorem tailTrace_7464188 : CollatzResearch.WordTrace tailWord_7464188 prefixEnd_7464188 3832716139521947563822831 := by
  unfold tailWord_7464188
  simp only [CollatzResearch.WordTrace]
  refine ⟨136120650941264566332472609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181494201255019421776630145 136120650941264566332472609)
  ·
    refine ⟨102090488205948424749354457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136120650941264566332472609 102090488205948424749354457)
    ·
      refine ⟨76567866154461318562015843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102090488205948424749354457 76567866154461318562015843)
      ·
        refine ⟨114851799231691977843023765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76567866154461318562015843 114851799231691977843023765)
        ·
          refine ⟨5383678088985561461391739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114851799231691977843023765 5383678088985561461391739)
          ·
            refine ⟨8075517133478342192087609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383678088985561461391739 8075517133478342192087609)
            ·
              refine ⟨6056637850108756644065707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8075517133478342192087609 6056637850108756644065707)
              ·
                refine ⟨9084956775163134966098561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6056637850108756644065707 9084956775163134966098561)
                ·
                  refine ⟨6813717581372351224573921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9084956775163134966098561 6813717581372351224573921)
                  ·
                    refine ⟨5110288186029263418430441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813717581372351224573921 5110288186029263418430441)
                    ·
                      refine ⟨3832716139521947563822831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110288186029263418430441 3832716139521947563822831)
                      ·
                        rfl

theorem cell23_7464188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_7464188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464188 prefixEnd_7464188 := by exact prefixLift 7464188
  have htrace : WordTrace (prefixWord ++ tailWord_7464188) baseStart_7464188 baseEnd_7464188 := by
    simpa [prefixWord, tailWord_7464188, baseEnd_7464188] using wordTrace_append hprefix tailTrace_7464188
  have hstable : (prefixWord ++ tailWord_7464188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464188).length < 2 ^ (prefixWord ++ tailWord_7464188).sum := by decide
  have hdescent : baseEnd_7464188 < baseStart_7464188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464280 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_7464280 : Nat := 118140960795 + 7464280 * 2 ^ 59
def prefixEnd_7464280 : Nat := 4983230072969 + 3 ^ 40 * 7464280 * 2
def baseEnd_7464280 : Nat := 1277587793247387067957469

theorem tailTrace_7464280 : CollatzResearch.WordTrace tailWord_7464280 prefixEnd_7464280 1277587793247387067957469 := by
  unfold tailWord_7464280
  simp only [CollatzResearch.WordTrace]
  refine ⟨136122328699097916188647147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181496438265463888251529529 136122328699097916188647147)
  ·
    refine ⟨204183493048646874282970721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136122328699097916188647147 204183493048646874282970721)
    ·
      refine ⟨153137619786485155712228041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204183493048646874282970721 153137619786485155712228041)
      ·
        refine ⟨114853214839863866784171031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153137619786485155712228041 114853214839863866784171031)
        ·
          refine ⟨172279822259795800176256547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114853214839863866784171031 172279822259795800176256547)
          ·
            refine ⟨258419733389693700264384821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172279822259795800176256547 258419733389693700264384821)
            ·
              refine ⟨24226850005283784399786077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258419733389693700264384821 24226850005283784399786077)
              ·
                refine ⟨9085068751981419149919779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24226850005283784399786077 9085068751981419149919779)
                ·
                  refine ⟨13627603127972128724879669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085068751981419149919779 13627603127972128724879669)
                  ·
                    refine ⟨1277587793247387067957469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13627603127972128724879669 1277587793247387067957469)
                    ·
                      rfl

theorem cell23_7464280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_7464280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464280 prefixEnd_7464280 := by exact prefixLift 7464280
  have htrace : WordTrace (prefixWord ++ tailWord_7464280) baseStart_7464280 baseEnd_7464280 := by
    simpa [prefixWord, tailWord_7464280, baseEnd_7464280] using wordTrace_append hprefix tailTrace_7464280
  have hstable : (prefixWord ++ tailWord_7464280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464280).length < 2 ^ (prefixWord ++ tailWord_7464280).sum := by decide
  have hdescent : baseEnd_7464280 < baseStart_7464280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464317 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_7464317 : Nat := 118140960795 + 7464317 * 2 ^ 59
def prefixEnd_7464317 : Nat := 4983230072969 + 3 ^ 40 * 7464317 * 2
def baseEnd_7464317 : Nat := 3832782378526377559109737

theorem tailTrace_7464317 : CollatzResearch.WordTrace tailWord_7464317 prefixEnd_7464317 3832782378526377559109737 := by
  unfold tailWord_7464317
  simp only [CollatzResearch.WordTrace]
  refine ⟨272246006899061787696391205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181497337932707858464260803 272246006899061787696391205)
  ·
    refine ⟨51046126293574085193073351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272246006899061787696391205 51046126293574085193073351)
    ·
      refine ⟨76569189440361127789610027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51046126293574085193073351 76569189440361127789610027)
      ·
        refine ⟨114853784160541691684415041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76569189440361127789610027 114853784160541691684415041)
        ·
          refine ⟨86140338120406268763311281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114853784160541691684415041 86140338120406268763311281)
          ·
            refine ⟨64605253590304701572483461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86140338120406268763311281 64605253590304701572483461)
            ·
              refine ⟨12113485048182131544840649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64605253590304701572483461 12113485048182131544840649)
              ·
                refine ⟨9085113786136598658630487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113485048182131544840649 9085113786136598658630487)
                ·
                  refine ⟨13627670679204897987945731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085113786136598658630487 13627670679204897987945731)
                  ·
                    refine ⟨20441506018807346981918597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13627670679204897987945731 20441506018807346981918597)
                    ·
                      refine ⟨3832782378526377559109737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20441506018807346981918597 3832782378526377559109737)
                      ·
                        rfl

theorem cell23_7464317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_7464317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464317 prefixEnd_7464317 := by exact prefixLift 7464317
  have htrace : WordTrace (prefixWord ++ tailWord_7464317) baseStart_7464317 baseEnd_7464317 := by
    simpa [prefixWord, tailWord_7464317, baseEnd_7464317] using wordTrace_append hprefix tailTrace_7464317
  have hstable : (prefixWord ++ tailWord_7464317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464317).length < 2 ^ (prefixWord ++ tailWord_7464317).sum := by decide
  have hdescent : baseEnd_7464317 < baseStart_7464317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464320 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_7464320 : Nat := 118140960795 + 7464320 * 2 ^ 59
def prefixEnd_7464320 : Nat := 4983230072969 + 3 ^ 40 * 7464320 * 2
def baseEnd_7464320 : Nat := 3832783918968341047372223

theorem tailTrace_7464320 : CollatzResearch.WordTrace tailWord_7464320 prefixEnd_7464320 3832783918968341047372223 := by
  unfold tailWord_7464320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136123058159025459604375207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181497410878700612805833609 136123058159025459604375207)
  ·
    refine ⟨204184587238538189406562811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136123058159025459604375207 204184587238538189406562811)
    ·
      refine ⟨306276880857807284109844217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204184587238538189406562811 306276880857807284109844217)
      ·
        refine ⟨229707660643355463082383163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306276880857807284109844217 229707660643355463082383163)
        ·
          refine ⟨344561490965033194623574745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229707660643355463082383163 344561490965033194623574745)
          ·
            refine ⟨258421118223774895967681059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344561490965033194623574745 258421118223774895967681059)
            ·
              refine ⟨387631677335662343951521589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258421118223774895967681059 387631677335662343951521589)
              ·
                refine ⟨36340469750218344745455149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 387631677335662343951521589 36340469750218344745455149)
                ·
                  refine ⟨13627676156331879279545681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36340469750218344745455149 13627676156331879279545681)
                  ·
                    refine ⟨10220757117248909459659261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13627676156331879279545681 10220757117248909459659261)
                    ·
                      refine ⟨3832783918968341047372223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10220757117248909459659261 3832783918968341047372223)
                      ·
                        rfl

theorem cell23_7464320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_7464320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464320 prefixEnd_7464320 := by exact prefixLift 7464320
  have htrace : WordTrace (prefixWord ++ tailWord_7464320) baseStart_7464320 baseEnd_7464320 := by
    simpa [prefixWord, tailWord_7464320, baseEnd_7464320] using wordTrace_append hprefix tailTrace_7464320
  have hstable : (prefixWord ++ tailWord_7464320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464320).length < 2 ^ (prefixWord ++ tailWord_7464320).sum := by decide
  have hdescent : baseEnd_7464320 < baseStart_7464320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464340 : List Nat := [2, 4, 2, 1, 2, 1, 11]
def baseStart_7464340 : Nat := 118140960795 + 7464340 * 2 ^ 59
def prefixEnd_7464340 : Nat := 4983230072969 + 3 ^ 40 * 7464340 * 2
def baseEnd_7464340 : Nat := 47318446772610258878051

theorem tailTrace_7464340 : CollatzResearch.WordTrace tailWord_7464340 prefixEnd_7464340 47318446772610258878051 := by
  unfold tailWord_7464340
  simp only [CollatzResearch.WordTrace]
  refine ⟨136123422888989231312239237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181497897185318975082985649 136123422888989231312239237)
  ·
    refine ⟨25523141791685480871044857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136123422888989231312239237 25523141791685480871044857)
    ·
      refine ⟨19142356343764110653283643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25523141791685480871044857 19142356343764110653283643)
      ·
        refine ⟨28713534515646165979925465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19142356343764110653283643 28713534515646165979925465)
        ·
          refine ⟨21535150886734624484944099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28713534515646165979925465 21535150886734624484944099)
          ·
            refine ⟨32302726330101936727416149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21535150886734624484944099 32302726330101936727416149)
            ·
              refine ⟨47318446772610258878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32302726330101936727416149 47318446772610258878051)
              ·
                rfl

theorem cell23_7464340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 11].length) (baseStart_7464340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464340 prefixEnd_7464340 := by exact prefixLift 7464340
  have htrace : WordTrace (prefixWord ++ tailWord_7464340) baseStart_7464340 baseEnd_7464340 := by
    simpa [prefixWord, tailWord_7464340, baseEnd_7464340] using wordTrace_append hprefix tailTrace_7464340
  have hstable : (prefixWord ++ tailWord_7464340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464340).length < 2 ^ (prefixWord ++ tailWord_7464340).sum := by decide
  have hdescent : baseEnd_7464340 < baseStart_7464340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464351 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7464351 : Nat := 118140960795 + 7464351 * 2 ^ 59
def prefixEnd_7464351 : Nat := 4983230072969 + 3 ^ 40 * 7464351 * 2
def baseEnd_7464351 : Nat := 3832799836868630426084581

theorem tailTrace_7464351 : CollatzResearch.WordTrace tailWord_7464351 prefixEnd_7464351 3832799836868630426084581 := by
  unfold tailWord_7464351
  simp only [CollatzResearch.WordTrace]
  refine ⟨272247246980938611503128907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181498164653959074335419271 272247246980938611503128907)
  ·
    refine ⟨408370870471407917254693361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272247246980938611503128907 408370870471407917254693361)
    ·
      refine ⟨306278152853555937941020021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408370870471407917254693361 306278152853555937941020021)
      ·
        refine ⟨28713576830020869181970627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306278152853555937941020021 28713576830020869181970627)
        ·
          refine ⟨43070365245031303772955941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28713576830020869181970627 43070365245031303772955941)
          ·
            refine ⟨8075693483443369457429239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43070365245031303772955941 8075693483443369457429239)
            ·
              refine ⟨12113540225165054186143859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075693483443369457429239 12113540225165054186143859)
              ·
                refine ⟨18170310337747581279215789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113540225165054186143859 18170310337747581279215789)
                ·
                  refine ⟨6813866376655342979705921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18170310337747581279215789 6813866376655342979705921)
                  ·
                    refine ⟨5110399782491507234779441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813866376655342979705921 5110399782491507234779441)
                    ·
                      refine ⟨3832799836868630426084581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110399782491507234779441 3832799836868630426084581)
                      ·
                        rfl

theorem cell23_7464351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7464351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464351 prefixEnd_7464351 := by exact prefixLift 7464351
  have htrace : WordTrace (prefixWord ++ tailWord_7464351) baseStart_7464351 baseEnd_7464351 := by
    simpa [prefixWord, tailWord_7464351, baseEnd_7464351] using wordTrace_append hprefix tailTrace_7464351
  have hstable : (prefixWord ++ tailWord_7464351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464351).length < 2 ^ (prefixWord ++ tailWord_7464351).sum := by decide
  have hdescent : baseEnd_7464351 < baseStart_7464351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464424 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7464424 : Nat := 118140960795 + 7464424 * 2 ^ 59
def prefixEnd_7464424 : Nat := 4983230072969 + 3 ^ 40 * 7464424 * 2
def baseEnd_7464424 : Nat := 3832837320956408640471745

theorem tailTrace_7464424 : CollatzResearch.WordTrace tailWord_7464424 prefixEnd_7464424 3832837320956408640471745 := by
  unfold tailWord_7464424
  simp only [CollatzResearch.WordTrace]
  refine ⟨136124954754837072485268163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181499939673116096647024217 136124954754837072485268163)
  ·
    refine ⟨204187432132255608727902245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136124954754837072485268163 204187432132255608727902245)
    ·
      refine ⟨38285143524797926636481671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204187432132255608727902245 38285143524797926636481671)
      ·
        refine ⟨57427715287196889954722507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38285143524797926636481671 57427715287196889954722507)
        ·
          refine ⟨86141572930795334932083761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57427715287196889954722507 86141572930795334932083761)
          ·
            refine ⟨64606179698096501199062821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86141572930795334932083761 64606179698096501199062821)
            ·
              refine ⟨12113658693393093974824279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64606179698096501199062821 12113658693393093974824279)
              ·
                refine ⟨18170488040089640962236419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113658693393093974824279 18170488040089640962236419)
                ·
                  refine ⟨27255732060134461443354629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18170488040089640962236419 27255732060134461443354629)
                  ·
                    refine ⟨5110449761275211520628993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27255732060134461443354629 5110449761275211520628993)
                    ·
                      refine ⟨3832837320956408640471745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110449761275211520628993 3832837320956408640471745)
                      ·
                        rfl

theorem cell23_7464424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7464424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464424 prefixEnd_7464424 := by exact prefixLift 7464424
  have htrace : WordTrace (prefixWord ++ tailWord_7464424) baseStart_7464424 baseEnd_7464424 := by
    simpa [prefixWord, tailWord_7464424, baseEnd_7464424] using wordTrace_append hprefix tailTrace_7464424
  have hstable : (prefixWord ++ tailWord_7464424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464424).length < 2 ^ (prefixWord ++ tailWord_7464424).sum := by decide
  have hdescent : baseEnd_7464424 < baseStart_7464424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464458 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_7464458 : Nat := 118140960795 + 7464458 * 2 ^ 59
def prefixEnd_7464458 : Nat := 4983230072969 + 3 ^ 40 * 7464458 * 2
def baseEnd_7464458 : Nat := 3832854779298661507446589

theorem tailTrace_7464458 : CollatzResearch.WordTrace tailWord_7464458 prefixEnd_7464458 3832854779298661507446589 := by
  unfold tailWord_7464458
  simp only [CollatzResearch.WordTrace]
  refine ⟨68062787397887742194318507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181500766394367312518182685 68062787397887742194318507)
  ·
    refine ⟨102094181096831613291477761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68062787397887742194318507 102094181096831613291477761)
    ·
      refine ⟨76570635822623709968608321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102094181096831613291477761 76570635822623709968608321)
      ·
        refine ⟨57427976866967782476456241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76570635822623709968608321 57427976866967782476456241)
        ·
          refine ⟨43070982650225836857342181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57427976866967782476456241 43070982650225836857342181)
          ·
            refine ⟨8075809246917344410751659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43070982650225836857342181 8075809246917344410751659)
            ·
              refine ⟨12113713870376016616127489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075809246917344410751659 12113713870376016616127489)
              ·
                refine ⟨9085285402782012462095617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113713870376016616127489 9085285402782012462095617)
                ·
                  refine ⟨6813964052086509346571713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9085285402782012462095617 6813964052086509346571713)
                  ·
                    refine ⟨5110473039064882009928785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6813964052086509346571713 5110473039064882009928785)
                    ·
                      refine ⟨3832854779298661507446589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110473039064882009928785 3832854779298661507446589)
                      ·
                        rfl

theorem cell23_7464458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_7464458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464458 prefixEnd_7464458 := by exact prefixLift 7464458
  have htrace : WordTrace (prefixWord ++ tailWord_7464458) baseStart_7464458 baseEnd_7464458 := by
    simpa [prefixWord, tailWord_7464458, baseEnd_7464458] using wordTrace_append hprefix tailTrace_7464458
  have hstable : (prefixWord ++ tailWord_7464458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464458).length < 2 ^ (prefixWord ++ tailWord_7464458).sum := by decide
  have hdescent : baseEnd_7464458 < baseStart_7464458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464497 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7464497 : Nat := 118140960795 + 7464497 * 2 ^ 59
def prefixEnd_7464497 : Nat := 4983230072969 + 3 ^ 40 * 7464497 * 2
def baseEnd_7464497 : Nat := 3832874805044186854858909

theorem tailTrace_7464497 : CollatzResearch.WordTrace tailWord_7464497 prefixEnd_7464497 3832874805044186854858909 := by
  unfold tailWord_7464497
  simp only [CollatzResearch.WordTrace]
  refine ⟨272252572038409678437943745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181501714692273118958629163 272252572038409678437943745)
  ·
    refine ⟨204189429028807258828457809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272252572038409678437943745 204189429028807258828457809)
    ·
      refine ⟨153142071771605444121343357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204189429028807258828457809 153142071771605444121343357)
      ·
        refine ⟨57428276914352041545503759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153142071771605444121343357 57428276914352041545503759)
        ·
          refine ⟨86142415371528062318255639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57428276914352041545503759 86142415371528062318255639)
          ·
            refine ⟨129213623057292093477383459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86142415371528062318255639 129213623057292093477383459)
            ·
              refine ⟨193820434585938140216075189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129213623057292093477383459 193820434585938140216075189)
              ·
                refine ⟨18170665742431700645257049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193820434585938140216075189 18170665742431700645257049)
                ·
                  refine ⟨13627999306823775483942787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18170665742431700645257049 13627999306823775483942787)
                  ·
                    refine ⟨20441998960235663225914181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13627999306823775483942787 20441998960235663225914181)
                    ·
                      refine ⟨3832874805044186854858909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20441998960235663225914181 3832874805044186854858909)
                      ·
                        rfl

theorem cell23_7464497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7464497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464497 prefixEnd_7464497 := by exact prefixLift 7464497
  have htrace : WordTrace (prefixWord ++ tailWord_7464497) baseStart_7464497 baseEnd_7464497 := by
    simpa [prefixWord, tailWord_7464497, baseEnd_7464497] using wordTrace_append hprefix tailTrace_7464497
  have hstable : (prefixWord ++ tailWord_7464497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464497).length < 2 ^ (prefixWord ++ tailWord_7464497).sum := by decide
  have hdescent : baseEnd_7464497 < baseStart_7464497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464524 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_7464524 : Nat := 118140960795 + 7464524 * 2 ^ 59
def prefixEnd_7464524 : Nat := 4983230072969 + 3 ^ 40 * 7464524 * 2
def baseEnd_7464524 : Nat := 1277629556340619416407095

theorem tailTrace_7464524 : CollatzResearch.WordTrace tailWord_7464524 prefixEnd_7464524 1277629556340619416407095 := by
  unfold tailWord_7464524
  simp only [CollatzResearch.WordTrace]
  refine ⟨136126778404655931024588313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181502371206207908032784417 136126778404655931024588313)
  ·
    refine ⟨102095083803491948268441235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136126778404655931024588313 102095083803491948268441235)
    ·
      refine ⟨153142625705237922402661853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102095083803491948268441235 153142625705237922402661853)
      ·
        refine ⟨57428484639464220900998195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153142625705237922402661853 57428484639464220900998195)
        ·
          refine ⟨86142726959196331351497293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57428484639464220900998195 86142726959196331351497293)
          ·
            refine ⟨32303522609698624256811485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86142726959196331351497293 32303522609698624256811485)
            ·
              refine ⟨12113820978636984096304307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32303522609698624256811485 12113820978636984096304307)
              ·
                refine ⟨18170731467955476144456461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113820978636984096304307 18170731467955476144456461)
                ·
                  refine ⟨6814024300483303554171173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18170731467955476144456461 6814024300483303554171173)
                  ·
                    refine ⟨1277629556340619416407095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814024300483303554171173 1277629556340619416407095)
                    ·
                      rfl

theorem cell23_7464524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_7464524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464524 prefixEnd_7464524 := by exact prefixLift 7464524
  have htrace : WordTrace (prefixWord ++ tailWord_7464524) baseStart_7464524 baseEnd_7464524 := by
    simpa [prefixWord, tailWord_7464524, baseEnd_7464524] using wordTrace_append hprefix tailTrace_7464524
  have hstable : (prefixWord ++ tailWord_7464524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464524).length < 2 ^ (prefixWord ++ tailWord_7464524).sum := by decide
  have hdescent : baseEnd_7464524 < baseStart_7464524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464587 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4]
def baseStart_7464587 : Nat := 118140960795 + 7464587 * 2 ^ 59
def prefixEnd_7464587 : Nat := 4983230072969 + 3 ^ 40 * 7464587 * 2
def baseEnd_7464587 : Nat := 3832921018303091502733495

theorem tailTrace_7464587 : CollatzResearch.WordTrace tailWord_7464587 prefixEnd_7464587 3832921018303091502733495 := by
  unfold tailWord_7464587
  simp only [CollatzResearch.WordTrace]
  refine ⟨272255854608083623808720015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181503903072055749205813343 272255854608083623808720015)
  ·
    refine ⟨408383781912125435713080023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272255854608083623808720015 408383781912125435713080023)
    ·
      refine ⟨612575672868188153569620035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408383781912125435713080023 612575672868188153569620035)
      ·
        refine ⟨918863509302282230354430053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612575672868188153569620035 918863509302282230354430053)
        ·
          refine ⟨172286907994177918191455635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 918863509302282230354430053 172286907994177918191455635)
          ·
            refine ⟨258430361991266877287183453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172286907994177918191455635 258430361991266877287183453)
            ·
              refine ⟨96911385746725078982693795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258430361991266877287183453 96911385746725078982693795)
              ·
                refine ⟨145367078620087618474040693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96911385746725078982693795 145367078620087618474040693)
                ·
                  refine ⟨13628163620633214231941315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145367078620087618474040693 13628163620633214231941315)
                  ·
                    refine ⟨20442245430949821347911973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13628163620633214231941315 20442245430949821347911973)
                    ·
                      refine ⟨3832921018303091502733495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20442245430949821347911973 3832921018303091502733495)
                      ·
                        rfl

theorem cell23_7464587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_7464587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464587 prefixEnd_7464587 := by exact prefixLift 7464587
  have htrace : WordTrace (prefixWord ++ tailWord_7464587) baseStart_7464587 baseEnd_7464587 := by
    simpa [prefixWord, tailWord_7464587, baseEnd_7464587] using wordTrace_append hprefix tailTrace_7464587
  have hstable : (prefixWord ++ tailWord_7464587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464587).length < 2 ^ (prefixWord ++ tailWord_7464587).sum := by decide
  have hdescent : baseEnd_7464587 < baseStart_7464587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464608 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2]
def baseStart_7464608 : Nat := 118140960795 + 7464608 * 2 ^ 59
def prefixEnd_7464608 : Nat := 4983230072969 + 3 ^ 40 * 7464608 * 2
def baseEnd_7464608 : Nat := 3832931801396835920570899

theorem tailTrace_7464608 : CollatzResearch.WordTrace tailWord_7464608 prefixEnd_7464608 3832931801396835920570899 := by
  unfold tailWord_7464608
  simp only [CollatzResearch.WordTrace]
  refine ⟨136128310270503772197617239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181504413694005029596822985 136128310270503772197617239)
  ·
    refine ⟨204192465405755658296425859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136128310270503772197617239 204192465405755658296425859)
    ·
      refine ⟨306288698108633487444638789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204192465405755658296425859 306288698108633487444638789)
      ·
        refine ⟨57429130895368778895869773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306288698108633487444638789 57429130895368778895869773)
        ·
          refine ⟨21535924085763292085951165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57429130895368778895869773 21535924085763292085951165)
          ·
            refine ⟨8075971532161234532231687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21535924085763292085951165 8075971532161234532231687)
            ·
              refine ⟨12113957298241851798347531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075971532161234532231687 12113957298241851798347531)
              ·
                refine ⟨18170935947362777697521297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12113957298241851798347531 18170935947362777697521297)
                ·
                  refine ⟨13628201960522083273140973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18170935947362777697521297 13628201960522083273140973)
                  ·
                    refine ⟨5110575735195781227427865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13628201960522083273140973 5110575735195781227427865)
                    ·
                      refine ⟨3832931801396835920570899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110575735195781227427865 3832931801396835920570899)
                      ·
                        rfl

theorem cell23_7464608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_7464608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464608 prefixEnd_7464608 := by exact prefixLift 7464608
  have htrace : WordTrace (prefixWord ++ tailWord_7464608) baseStart_7464608 baseEnd_7464608 := by
    simpa [prefixWord, tailWord_7464608, baseEnd_7464608] using wordTrace_append hprefix tailTrace_7464608
  have hstable : (prefixWord ++ tailWord_7464608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464608).length < 2 ^ (prefixWord ++ tailWord_7464608).sum := by decide
  have hdescent : baseEnd_7464608 < baseStart_7464608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464621 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_7464621 : Nat := 118140960795 + 7464621 * 2 ^ 59
def prefixEnd_7464621 : Nat := 4983230072969 + 3 ^ 40 * 7464621 * 2
def baseEnd_7464621 : Nat := 3832938476645344369708339

theorem tailTrace_7464621 : CollatzResearch.WordTrace tailWord_7464621 prefixEnd_7464621 3832938476645344369708339 := by
  unfold tailWord_7464621
  simp only [CollatzResearch.WordTrace]
  refine ⟨272257094689960447615457717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181504729793306965076971811 272257094689960447615457717)
  ·
    refine ⟨25524102627183791963949161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272257094689960447615457717 25524102627183791963949161)
    ·
      refine ⟨19143076970387843972961871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524102627183791963949161 19143076970387843972961871)
      ·
        refine ⟨28714615455581765959442807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143076970387843972961871 28714615455581765959442807)
        ·
          refine ⟨43071923183372648939164211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28714615455581765959442807 43071923183372648939164211)
          ·
            refine ⟨64607884775058973408746317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43071923183372648939164211 64607884775058973408746317)
            ·
              refine ⟨24227956790647115028279869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64607884775058973408746317 24227956790647115028279869)
              ·
                refine ⟨9085483796492668135604951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24227956790647115028279869 9085483796492668135604951)
                ·
                  refine ⟨13628225694739002203407427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085483796492668135604951 13628225694739002203407427)
                  ·
                    refine ⟨20442338542108503305111141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13628225694739002203407427 20442338542108503305111141)
                    ·
                      refine ⟨3832938476645344369708339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20442338542108503305111141 3832938476645344369708339)
                      ·
                        rfl

theorem cell23_7464621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_7464621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464621 prefixEnd_7464621 := by exact prefixLift 7464621
  have htrace : WordTrace (prefixWord ++ tailWord_7464621) baseStart_7464621 baseEnd_7464621 := by
    simpa [prefixWord, tailWord_7464621, baseEnd_7464621] using wordTrace_append hprefix tailTrace_7464621
  have hstable : (prefixWord ++ tailWord_7464621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464621).length < 2 ^ (prefixWord ++ tailWord_7464621).sum := by decide
  have hdescent : baseEnd_7464621 < baseStart_7464621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464631 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 2, 4]
def baseStart_7464631 : Nat := 118140960795 + 7464631 * 2 ^ 59
def prefixEnd_7464631 : Nat := 4983230072969 + 3 ^ 40 * 7464631 * 2
def baseEnd_7464631 : Nat := 1277647870483963110194431

theorem tailTrace_7464631 : CollatzResearch.WordTrace tailWord_7464631 prefixEnd_7464631 1277647870483963110194431 := by
  unfold tailWord_7464631
  simp only [CollatzResearch.WordTrace]
  refine ⟨272257459419924219323321747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181504972946616146215547831 272257459419924219323321747)
  ·
    refine ⟨408386189129886328984982621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272257459419924219323321747 408386189129886328984982621)
    ·
      refine ⟨153144820923707373369368483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408386189129886328984982621 153144820923707373369368483)
      ·
        refine ⟨229717231385561060054052725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153144820923707373369368483 229717231385561060054052725)
        ·
          refine ⟨21535990442396349380067443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 229717231385561060054052725 21535990442396349380067443)
          ·
            refine ⟨32303985663594524070101165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21535990442396349380067443 32303985663594524070101165)
            ·
              refine ⟨12113994623847946526287937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32303985663594524070101165 12113994623847946526287937)
              ·
                refine ⟨9085495967885959894715953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113994623847946526287937 9085495967885959894715953)
                ·
                  refine ⟨6814121975914469921036965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9085495967885959894715953 6814121975914469921036965)
                  ·
                    refine ⟨1277647870483963110194431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814121975914469921036965 1277647870483963110194431)
                    ·
                      rfl

theorem cell23_7464631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_7464631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464631 prefixEnd_7464631 := by exact prefixLift 7464631
  have htrace : WordTrace (prefixWord ++ tailWord_7464631) baseStart_7464631 baseEnd_7464631 := by
    simpa [prefixWord, tailWord_7464631, baseEnd_7464631] using wordTrace_append hprefix tailTrace_7464631
  have hstable : (prefixWord ++ tailWord_7464631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464631).length < 2 ^ (prefixWord ++ tailWord_7464631).sum := by decide
  have hdescent : baseEnd_7464631 < baseStart_7464631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464638 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_7464638 : Nat := 118140960795 + 7464638 * 2 ^ 59
def prefixEnd_7464638 : Nat := 4983230072969 + 3 ^ 40 * 7464638 * 2
def baseEnd_7464638 : Nat := 3832947205816470803195761

theorem tailTrace_7464638 : CollatzResearch.WordTrace tailWord_7464638 prefixEnd_7464638 3832947205816470803195761 := by
  unfold tailWord_7464638
  simp only [CollatzResearch.WordTrace]
  refine ⟨34032214341362357439853321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181505143153932573012551045 34032214341362357439853321)
  ·
    refine ⟨25524160756021768079889991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34032214341362357439853321 25524160756021768079889991)
    ·
      refine ⟨38286241134032652119834987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25524160756021768079889991 38286241134032652119834987)
      ·
        refine ⟨57429361701048978179752481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38286241134032652119834987 57429361701048978179752481)
        ·
          refine ⟨43072021275786733634814361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57429361701048978179752481 43072021275786733634814361)
          ·
            refine ⟨32304015956840050226110771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43072021275786733634814361 32304015956840050226110771)
            ·
              refine ⟨48456023935260075339166157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32304015956840050226110771 48456023935260075339166157)
              ·
                refine ⟨18171008975722528252187309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48456023935260075339166157 18171008975722528252187309)
                ·
                  refine ⟨6814128365895948094570241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18171008975722528252187309 6814128365895948094570241)
                  ·
                    refine ⟨5110596274421961070927681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6814128365895948094570241 5110596274421961070927681)
                    ·
                      refine ⟨3832947205816470803195761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110596274421961070927681 3832947205816470803195761)
                      ·
                        rfl

theorem cell23_7464638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_7464638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464638 prefixEnd_7464638 := by exact prefixLift 7464638
  have htrace : WordTrace (prefixWord ++ tailWord_7464638) baseStart_7464638 baseEnd_7464638 := by
    simpa [prefixWord, tailWord_7464638, baseEnd_7464638] using wordTrace_append hprefix tailTrace_7464638
  have hstable : (prefixWord ++ tailWord_7464638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464638).length < 2 ^ (prefixWord ++ tailWord_7464638).sum := by decide
  have hdescent : baseEnd_7464638 < baseStart_7464638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464658 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7464658 : Nat := 118140960795 + 7464658 * 2 ^ 59
def prefixEnd_7464658 : Nat := 4983230072969 + 3 ^ 40 * 7464658 * 2
def baseEnd_7464658 : Nat := 3832957475429560724945669

theorem tailTrace_7464658 : CollatzResearch.WordTrace tailWord_7464658 prefixEnd_7464658 3832957475429560724945669 := by
  unfold tailWord_7464658
  simp only [CollatzResearch.WordTrace]
  refine ⟨68064611047706600733638657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181505629460550935289703085 68064611047706600733638657)
  ·
    refine ⟨51048458285779950550228993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68064611047706600733638657 51048458285779950550228993)
    ·
      refine ⟨38286343714334962912671745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51048458285779950550228993 38286343714334962912671745)
      ·
        refine ⟨28714757785751222184503809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38286343714334962912671745 28714757785751222184503809)
        ·
          refine ⟨21536068339313416638377857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28714757785751222184503809 21536068339313416638377857)
          ·
            refine ⟨16152051254485062478783393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21536068339313416638377857 16152051254485062478783393)
            ·
              refine ⟨12114038440863796859087545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16152051254485062478783393 12114038440863796859087545)
              ·
                refine ⟨9085528830647847644315659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12114038440863796859087545 9085528830647847644315659)
                ·
                  refine ⟨13628293245971771466473489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085528830647847644315659 13628293245971771466473489)
                  ·
                    refine ⟨10221219934478828599855117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13628293245971771466473489 10221219934478828599855117)
                    ·
                      refine ⟨3832957475429560724945669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10221219934478828599855117 3832957475429560724945669)
                      ·
                        rfl

theorem cell23_7464658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7464658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464658 prefixEnd_7464658 := by exact prefixLift 7464658
  have htrace : WordTrace (prefixWord ++ tailWord_7464658) baseStart_7464658 baseEnd_7464658 := by
    simpa [prefixWord, tailWord_7464658, baseEnd_7464658] using wordTrace_append hprefix tailTrace_7464658
  have hstable : (prefixWord ++ tailWord_7464658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464658).length < 2 ^ (prefixWord ++ tailWord_7464658).sum := by decide
  have hdescent : baseEnd_7464658 < baseStart_7464658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464714 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_7464714 : Nat := 118140960795 + 7464714 * 2 ^ 59
def prefixEnd_7464714 : Nat := 4983230072969 + 3 ^ 40 * 7464714 * 2
def baseEnd_7464714 : Nat := 3832986230346212505845411

theorem tailTrace_7464714 : CollatzResearch.WordTrace tailWord_7464714 prefixEnd_7464714 3832986230346212505845411 := by
  unfold tailWord_7464714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68065121669655881124648299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181506991119082349665728797 68065121669655881124648299)
  ·
    refine ⟨102097682504483821686972449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68065121669655881124648299 102097682504483821686972449)
    ·
      refine ⟨76573261878362866265229337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102097682504483821686972449 76573261878362866265229337)
      ·
        refine ⟨57429946408772149698922003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76573261878362866265229337 57429946408772149698922003)
        ·
          refine ⟨86144919613158224548383005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57429946408772149698922003 86144919613158224548383005)
          ·
            refine ⟨32304344854934334205643627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86144919613158224548383005 32304344854934334205643627)
            ·
              refine ⟨48456517282401501308465441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32304344854934334205643627 48456517282401501308465441)
              ·
                refine ⟨36342387961801125981349081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48456517282401501308465441 36342387961801125981349081)
                ·
                  refine ⟨27256790971350844486011811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36342387961801125981349081 27256790971350844486011811)
                  ·
                    refine ⟨40885186457026266729017717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27256790971350844486011811 40885186457026266729017717)
                    ·
                      refine ⟨3832986230346212505845411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40885186457026266729017717 3832986230346212505845411)
                      ·
                        rfl

theorem cell23_7464714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_7464714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464714 prefixEnd_7464714 := by exact prefixLift 7464714
  have htrace : WordTrace (prefixWord ++ tailWord_7464714) baseStart_7464714 baseEnd_7464714 := by
    simpa [prefixWord, tailWord_7464714, baseEnd_7464714] using wordTrace_append hprefix tailTrace_7464714
  have hstable : (prefixWord ++ tailWord_7464714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464714).length < 2 ^ (prefixWord ++ tailWord_7464714).sum := by decide
  have hdescent : baseEnd_7464714 < baseStart_7464714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464758 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7464758 : Nat := 118140960795 + 7464758 * 2 ^ 59
def prefixEnd_7464758 : Nat := 4983230072969 + 3 ^ 40 * 7464758 * 2
def baseEnd_7464758 : Nat := 3833008823495010333695209

theorem tailTrace_7464758 : CollatzResearch.WordTrace tailWord_7464758 prefixEnd_7464758 3833008823495010333695209 := by
  unfold tailWord_7464758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016380718154007500824683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181508060993642746675463285 17016380718154007500824683)
  ·
    refine ⟨25524571077231011251237025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016380718154007500824683 25524571077231011251237025)
    ·
      refine ⟨19143428307923258438427769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25524571077231011251237025 19143428307923258438427769)
      ·
        refine ⟨14357571230942443828820827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19143428307923258438427769 14357571230942443828820827)
        ·
          refine ⟨21536356846413665743231241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14357571230942443828820827 21536356846413665743231241)
          ·
            refine ⟨16152267634810249307423431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21536356846413665743231241 16152267634810249307423431)
            ·
              refine ⟨24228401452215373961135147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152267634810249307423431 24228401452215373961135147)
              ·
                refine ⟨36342602178323060941702721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24228401452215373961135147 36342602178323060941702721)
                ·
                  refine ⟨27256951633742295706277041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36342602178323060941702721 27256951633742295706277041)
                  ·
                    refine ⟨20442713725306721779707781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27256951633742295706277041 20442713725306721779707781)
                    ·
                      refine ⟨3833008823495010333695209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20442713725306721779707781 3833008823495010333695209)
                      ·
                        rfl

theorem cell23_7464758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7464758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464758 prefixEnd_7464758 := by exact prefixLift 7464758
  have htrace : WordTrace (prefixWord ++ tailWord_7464758) baseStart_7464758 baseEnd_7464758 := by
    simpa [prefixWord, tailWord_7464758, baseEnd_7464758] using wordTrace_append hprefix tailTrace_7464758
  have hstable : (prefixWord ++ tailWord_7464758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464758).length < 2 ^ (prefixWord ++ tailWord_7464758).sum := by decide
  have hdescent : baseEnd_7464758 < baseStart_7464758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464764 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_7464764 : Nat := 118140960795 + 7464764 * 2 ^ 59
def prefixEnd_7464764 : Nat := 4983230072969 + 3 ^ 40 * 7464764 * 2
def baseEnd_7464764 : Nat := 1277670634792979103406727

theorem tailTrace_7464764 : CollatzResearch.WordTrace tailWord_7464764 prefixEnd_7464764 1277670634792979103406727 := by
  unfold tailWord_7464764
  simp only [CollatzResearch.WordTrace]
  refine ⟨136131155164221191518956673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181508206885628255358608897 136131155164221191518956673)
  ·
    refine ⟨102098366373165893639217505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136131155164221191518956673 102098366373165893639217505)
    ·
      refine ⟨76573774779874420229413129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102098366373165893639217505 76573774779874420229413129)
      ·
        refine ⟨57430331084905815172059847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76573774779874420229413129 57430331084905815172059847)
        ·
          refine ⟨86145496627358722758089771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57430331084905815172059847 86145496627358722758089771)
          ·
            refine ⟨129218244941038084137134657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86145496627358722758089771 129218244941038084137134657)
            ·
              refine ⟨96913683705778563102850993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129218244941038084137134657 96913683705778563102850993)
              ·
                refine ⟨72685262779333922327138245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96913683705778563102850993 72685262779333922327138245)
                ·
                  refine ⟨13628486771125110436338421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72685262779333922327138245 13628486771125110436338421)
                  ·
                    refine ⟨1277670634792979103406727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13628486771125110436338421 1277670634792979103406727)
                    ·
                      rfl

theorem cell23_7464764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_7464764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464764 prefixEnd_7464764 := by exact prefixLift 7464764
  have htrace : WordTrace (prefixWord ++ tailWord_7464764) baseStart_7464764 baseEnd_7464764 := by
    simpa [prefixWord, tailWord_7464764, baseEnd_7464764] using wordTrace_append hprefix tailTrace_7464764
  have hstable : (prefixWord ++ tailWord_7464764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464764).length < 2 ^ (prefixWord ++ tailWord_7464764).sum := by decide
  have hdescent : baseEnd_7464764 < baseStart_7464764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464801 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_7464801 : Nat := 118140960795 + 7464801 * 2 ^ 59
def prefixEnd_7464801 : Nat := 4983230072969 + 3 ^ 40 * 7464801 * 2
def baseEnd_7464801 : Nat := 3833030903163153665457511

theorem tailTrace_7464801 : CollatzResearch.WordTrace tailWord_7464801 prefixEnd_7464801 3833030903163153665457511 := by
  unfold tailWord_7464801
  simp only [CollatzResearch.WordTrace]
  refine ⟨272263659829308338357010257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181509106552872225571340171 272263659829308338357010257)
  ·
    refine ⟨204197744871981253767757693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272263659829308338357010257 204197744871981253767757693)
    ·
      refine ⟨76574154326992970162909135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204197744871981253767757693 76574154326992970162909135)
      ·
        refine ⟨114861231490489455244363703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76574154326992970162909135 114861231490489455244363703)
        ·
          refine ⟨172291847235734182866545555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114861231490489455244363703 172291847235734182866545555)
          ·
            refine ⟨258437770853601274299818333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172291847235734182866545555 258437770853601274299818333)
            ·
              refine ⟨96914164070100477862431875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258437770853601274299818333 96914164070100477862431875)
              ·
                refine ⟨145371246105150716793647813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96914164070100477862431875 145371246105150716793647813)
                ·
                  refine ⟨27257108644715759398808965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145371246105150716793647813 27257108644715759398808965)
                  ·
                    refine ⟨5110707870884204887276681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27257108644715759398808965 5110707870884204887276681)
                    ·
                      refine ⟨3833030903163153665457511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110707870884204887276681 3833030903163153665457511)
                      ·
                        rfl

theorem cell23_7464801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_7464801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464801 prefixEnd_7464801 := by exact prefixLift 7464801
  have htrace : WordTrace (prefixWord ++ tailWord_7464801) baseStart_7464801 baseEnd_7464801 := by
    simpa [prefixWord, tailWord_7464801, baseEnd_7464801] using wordTrace_append hprefix tailTrace_7464801
  have hstable : (prefixWord ++ tailWord_7464801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464801).length < 2 ^ (prefixWord ++ tailWord_7464801).sum := by decide
  have hdescent : baseEnd_7464801 < baseStart_7464801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464821 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7464821 : Nat := 118140960795 + 7464821 * 2 ^ 59
def prefixEnd_7464821 : Nat := 4983230072969 + 3 ^ 40 * 7464821 * 2
def baseEnd_7464821 : Nat := 3833041172776243587207419

theorem tailTrace_7464821 : CollatzResearch.WordTrace tailWord_7464821 prefixEnd_7464821 3833041172776243587207419 := by
  unfold tailWord_7464821
  simp only [CollatzResearch.WordTrace]
  refine ⟨272264389289235881772738317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181509592859490587848492211 272264389289235881772738317)
  ·
    refine ⟨102099145983463455664776869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272264389289235881772738317 102099145983463455664776869)
    ·
      refine ⟨19143589871899397937145663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102099145983463455664776869 19143589871899397937145663)
      ·
        refine ⟨28715384807849096905718495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19143589871899397937145663 28715384807849096905718495)
        ·
          refine ⟨43073077211773645358577743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28715384807849096905718495 43073077211773645358577743)
          ·
            refine ⟨64609615817660468037866615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43073077211773645358577743 64609615817660468037866615)
            ·
              refine ⟨96914423726490702056799923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64609615817660468037866615 96914423726490702056799923)
              ·
                refine ⟨145371635589736053085199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96914423726490702056799923 145371635589736053085199885)
                ·
                  refine ⟨54514363346151019906949957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145371635589736053085199885 54514363346151019906949957)
                  ·
                    refine ⟨10221443127403316232553117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54514363346151019906949957 10221443127403316232553117)
                    ·
                      refine ⟨3833041172776243587207419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10221443127403316232553117 3833041172776243587207419)
                      ·
                        rfl

theorem cell23_7464821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7464821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464821 prefixEnd_7464821 := by exact prefixLift 7464821
  have htrace : WordTrace (prefixWord ++ tailWord_7464821) baseStart_7464821 baseEnd_7464821 := by
    simpa [prefixWord, tailWord_7464821, baseEnd_7464821] using wordTrace_append hprefix tailTrace_7464821
  have hstable : (prefixWord ++ tailWord_7464821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464821).length < 2 ^ (prefixWord ++ tailWord_7464821).sum := by decide
  have hdescent : baseEnd_7464821 < baseStart_7464821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464864 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7464864 : Nat := 118140960795 + 7464864 * 2 ^ 59
def prefixEnd_7464864 : Nat := 4983230072969 + 3 ^ 40 * 7464864 * 2
def baseEnd_7464864 : Nat := 3833063252444386918969721

theorem tailTrace_7464864 : CollatzResearch.WordTrace tailWord_7464864 prefixEnd_7464864 3833063252444386918969721 := by
  unfold tailWord_7464864
  simp only [CollatzResearch.WordTrace]
  refine ⟨136132978814040050058276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181510638418720066744369097 136132978814040050058276823)
  ·
    refine ⟨204199468221060075087415235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136132978814040050058276823 204199468221060075087415235)
    ·
      refine ⟨306299202331590112631122853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204199468221060075087415235 306299202331590112631122853)
      ·
        refine ⟨57431100437173146118335535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306299202331590112631122853 57431100437173146118335535)
        ·
          refine ⟨86146650655759719177503303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57431100437173146118335535 86146650655759719177503303)
          ·
            refine ⟨129219975983639578766254955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86146650655759719177503303 129219975983639578766254955)
            ·
              refine ⟨193829963975459368149382433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129219975983639578766254955 193829963975459368149382433)
              ·
                refine ⟨145372472981594526112036825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193829963975459368149382433 145372472981594526112036825)
                ·
                  refine ⟨109029354736195894584027619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145372472981594526112036825 109029354736195894584027619)
                  ·
                    refine ⟨163544032104293841876041429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109029354736195894584027619 163544032104293841876041429)
                    ·
                      refine ⟨3833063252444386918969721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163544032104293841876041429 3833063252444386918969721)
                      ·
                        rfl

theorem cell23_7464864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7464864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464864 prefixEnd_7464864 := by exact prefixLift 7464864
  have htrace : WordTrace (prefixWord ++ tailWord_7464864) baseStart_7464864 baseEnd_7464864 := by
    simpa [prefixWord, tailWord_7464864, baseEnd_7464864] using wordTrace_append hprefix tailTrace_7464864
  have hstable : (prefixWord ++ tailWord_7464864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464864).length < 2 ^ (prefixWord ++ tailWord_7464864).sum := by decide
  have hdescent : baseEnd_7464864 < baseStart_7464864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464891 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 8, 2]
def baseStart_7464891 : Nat := 118140960795 + 7464891 * 2 ^ 59
def prefixEnd_7464891 : Nat := 4983230072969 + 3 ^ 40 * 7464891 * 2
def baseEnd_7464891 : Nat := 3833077116422058313332097

theorem tailTrace_7464891 : CollatzResearch.WordTrace tailWord_7464891 prefixEnd_7464891 3833077116422058313332097 := by
  unfold tailWord_7464891
  simp only [CollatzResearch.WordTrace]
  refine ⟨272266942398982283727786527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181511294932654855818524351 272266942398982283727786527)
  ·
    refine ⟨408400413598473425591679791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272266942398982283727786527 408400413598473425591679791)
    ·
      refine ⟨612600620397710138387519687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408400413598473425591679791 612600620397710138387519687)
      ·
        refine ⟨918900930596565207581279531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612600620397710138387519687 918900930596565207581279531)
        ·
          refine ⟨1378351395894847811371919297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918900930596565207581279531 1378351395894847811371919297)
          ·
            refine ⟨1033763546921135858528939473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378351395894847811371919297 1033763546921135858528939473)
            ·
              refine ⟨775322660190851893896704605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033763546921135858528939473 775322660190851893896704605)
              ·
                refine ⟨290745997571569460211264227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775322660190851893896704605 290745997571569460211264227)
                ·
                  refine ⟨436118996357354190316896341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290745997571569460211264227 436118996357354190316896341)
                  ·
                    refine ⟨5110769488562744417776129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 436118996357354190316896341 5110769488562744417776129)
                    ·
                      refine ⟨3833077116422058313332097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110769488562744417776129 3833077116422058313332097)
                      ·
                        rfl

theorem cell23_7464891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8, 2].length) (baseStart_7464891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464891 prefixEnd_7464891 := by exact prefixLift 7464891
  have htrace : WordTrace (prefixWord ++ tailWord_7464891) baseStart_7464891 baseEnd_7464891 := by
    simpa [prefixWord, tailWord_7464891, baseEnd_7464891] using wordTrace_append hprefix tailTrace_7464891
  have hstable : (prefixWord ++ tailWord_7464891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464891).length < 2 ^ (prefixWord ++ tailWord_7464891).sum := by decide
  have hdescent : baseEnd_7464891 < baseStart_7464891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464901 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_7464901 : Nat := 118140960795 + 7464901 * 2 ^ 59
def prefixEnd_7464901 : Nat := 4983230072969 + 3 ^ 40 * 7464901 * 2
def baseEnd_7464901 : Nat := 1277694083742867758069017

theorem tailTrace_7464901 : CollatzResearch.WordTrace tailWord_7464901 prefixEnd_7464901 1277694083742867758069017 := by
  unfold tailWord_7464901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272267307128946055435650557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181511538085964036957100371 272267307128946055435650557)
  ·
    refine ⟨102100240173354770788368959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272267307128946055435650557 102100240173354770788368959)
    ·
      refine ⟨153150360260032156182553439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102100240173354770788368959 153150360260032156182553439)
      ·
        refine ⟨229725540390048234273830159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153150360260032156182553439 229725540390048234273830159)
        ·
          refine ⟨344588310585072351410745239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229725540390048234273830159 344588310585072351410745239)
          ·
            refine ⟨516882465877608527116117859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344588310585072351410745239 516882465877608527116117859)
            ·
              refine ⟨775323698816412790674176789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516882465877608527116117859 775323698816412790674176789)
              ·
                refine ⟨36343298382019349562852037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 775323698816412790674176789 36343298382019349562852037)
                ·
                  refine ⟨6814368446628628043034757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36343298382019349562852037 6814368446628628043034757)
                  ·
                    refine ⟨1277694083742867758069017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814368446628628043034757 1277694083742867758069017)
                    ·
                      rfl

theorem cell23_7464901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_7464901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464901 prefixEnd_7464901 := by exact prefixLift 7464901
  have htrace : WordTrace (prefixWord ++ tailWord_7464901) baseStart_7464901 baseEnd_7464901 := by
    simpa [prefixWord, tailWord_7464901, baseEnd_7464901] using wordTrace_append hprefix tailTrace_7464901
  have hstable : (prefixWord ++ tailWord_7464901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464901).length < 2 ^ (prefixWord ++ tailWord_7464901).sum := by decide
  have hdescent : baseEnd_7464901 < baseStart_7464901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464931 : List Nat := [1, 1, 1, 6, 1, 2, 3, 8]
def baseStart_7464931 : Nat := 118140960795 + 7464931 * 2 ^ 59
def prefixEnd_7464931 : Nat := 4983230072969 + 3 ^ 40 * 7464931 * 2
def baseEnd_7464931 : Nat := 141966579838823635438219

theorem tailTrace_7464931 : CollatzResearch.WordTrace tailWord_7464931 prefixEnd_7464931 141966579838823635438219 := by
  unfold tailWord_7464931
  simp only [CollatzResearch.WordTrace]
  refine ⟨272268401318837370559242647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181512267545891580372828431 272268401318837370559242647)
  ·
    refine ⟨408402601978256055838863971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272268401318837370559242647 408402601978256055838863971)
    ·
      refine ⟨612603902967384083758295957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408402601978256055838863971 612603902967384083758295957)
      ·
        refine ⟨28715807951596128926170123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 612603902967384083758295957 28715807951596128926170123)
        ·
          refine ⟨43073711927394193389255185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28715807951596128926170123 43073711927394193389255185)
          ·
            refine ⟨32305283945545645041941389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43073711927394193389255185 32305283945545645041941389)
            ·
              refine ⟨12114481479579616890728021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32305283945545645041941389 12114481479579616890728021)
              ·
                refine ⟨141966579838823635438219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12114481479579616890728021 141966579838823635438219)
                ·
                  rfl

theorem cell23_7464931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 8].length) (baseStart_7464931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464931 prefixEnd_7464931 := by exact prefixLift 7464931
  have htrace : WordTrace (prefixWord ++ tailWord_7464931) baseStart_7464931 baseEnd_7464931 := by
    simpa [prefixWord, tailWord_7464931, baseEnd_7464931] using wordTrace_append hprefix tailTrace_7464931
  have hstable : (prefixWord ++ tailWord_7464931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464931).length < 2 ^ (prefixWord ++ tailWord_7464931).sum := by decide
  have hdescent : baseEnd_7464931 < baseStart_7464931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464938 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_7464938 : Nat := 118140960795 + 7464938 * 2 ^ 59
def prefixEnd_7464938 : Nat := 4983230072969 + 3 ^ 40 * 7464938 * 2
def baseEnd_7464938 : Nat := 3833101250012819629444381

theorem tailTrace_7464938 : CollatzResearch.WordTrace tailWord_7464938 prefixEnd_7464938 3833101250012819629444381 := by
  unfold tailWord_7464938
  simp only [CollatzResearch.WordTrace]
  refine ⟨68067164157453002688686867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181512437753208007169831645 68067164157453002688686867)
  ·
    refine ⟨102100746236179504033030301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68067164157453002688686867 102100746236179504033030301)
    ·
      refine ⟨38287779838567314012386363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102100746236179504033030301 38287779838567314012386363)
      ·
        refine ⟨57431669757850971018579545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38287779838567314012386363 57431669757850971018579545)
        ·
          refine ⟨43073752318388228263934659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57431669757850971018579545 43073752318388228263934659)
          ·
            refine ⟨64610628477582342395901989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43073752318388228263934659 64610628477582342395901989)
            ·
              refine ⟨12114492839546689199231623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64610628477582342395901989 12114492839546689199231623)
              ·
                refine ⟨18171739259320033798847435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114492839546689199231623 18171739259320033798847435)
                ·
                  refine ⟨27257608888980050698271153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18171739259320033798847435 27257608888980050698271153)
                  ·
                    refine ⟨20443206666735038023703365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27257608888980050698271153 20443206666735038023703365)
                    ·
                      refine ⟨3833101250012819629444381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20443206666735038023703365 3833101250012819629444381)
                      ·
                        rfl

theorem cell23_7464938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_7464938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464938 prefixEnd_7464938 := by exact prefixLift 7464938
  have htrace : WordTrace (prefixWord ++ tailWord_7464938) baseStart_7464938 baseEnd_7464938 := by
    simpa [prefixWord, tailWord_7464938, baseEnd_7464938] using wordTrace_append hprefix tailTrace_7464938
  have hstable : (prefixWord ++ tailWord_7464938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464938).length < 2 ^ (prefixWord ++ tailWord_7464938).sum := by decide
  have hdescent : baseEnd_7464938 < baseStart_7464938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464942 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_7464942 : Nat := 118140960795 + 7464942 * 2 ^ 59
def prefixEnd_7464942 : Nat := 4983230072969 + 3 ^ 40 * 7464942 * 2
def baseEnd_7464942 : Nat := 3833103303935437613794363

theorem tailTrace_7464942 : CollatzResearch.WordTrace tailWord_7464942 prefixEnd_7464942 3833103303935437613794363 := by
  unfold tailWord_7464942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34033600315224689929736635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181512535014531679625262053 34033600315224689929736635)
  ·
    refine ⟨51050400472837034894604953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34033600315224689929736635 51050400472837034894604953)
    ·
      refine ⟨38287800354627776170953715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51050400472837034894604953 38287800354627776170953715)
      ·
        refine ⟨57431700531941664256430573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38287800354627776170953715 57431700531941664256430573)
        ·
          refine ⟨21536887699478124096161465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57431700531941664256430573 21536887699478124096161465)
          ·
            refine ⟨16152665774608593072121099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21536887699478124096161465 16152665774608593072121099)
            ·
              refine ⟨24228998661912889608181649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16152665774608593072121099 24228998661912889608181649)
              ·
                refine ⟨18171748996434667206136237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24228998661912889608181649 18171748996434667206136237)
                ·
                  refine ⟨6814405873663000202301089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18171748996434667206136237 6814405873663000202301089)
                  ·
                    refine ⟨5110804405247250151725817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6814405873663000202301089 5110804405247250151725817)
                    ·
                      refine ⟨3833103303935437613794363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110804405247250151725817 3833103303935437613794363)
                      ·
                        rfl

theorem cell23_7464942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_7464942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464942 prefixEnd_7464942 := by exact prefixLift 7464942
  have htrace : WordTrace (prefixWord ++ tailWord_7464942) baseStart_7464942 baseEnd_7464942 := by
    simpa [prefixWord, tailWord_7464942, baseEnd_7464942] using wordTrace_append hprefix tailTrace_7464942
  have hstable : (prefixWord ++ tailWord_7464942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464942).length < 2 ^ (prefixWord ++ tailWord_7464942).sum := by decide
  have hdescent : baseEnd_7464942 < baseStart_7464942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7464991 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 6]
def baseStart_7464991 : Nat := 118140960795 + 7464991 * 2 ^ 59
def prefixEnd_7464991 : Nat := 4983230072969 + 3 ^ 40 * 7464991 * 2
def baseEnd_7464991 : Nat := 1277709488162502640693879

theorem tailTrace_7464991 : CollatzResearch.WordTrace tailWord_7464991 prefixEnd_7464991 1277709488162502640693879 := by
  unfold tailWord_7464991
  simp only [CollatzResearch.WordTrace]
  refine ⟨272270589698620000806426827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181513726465746667204284551 272270589698620000806426827)
  ·
    refine ⟨408405884547930001209640241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272270589698620000806426827 408405884547930001209640241)
    ·
      refine ⟨306304413410947500907230181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408405884547930001209640241 306304413410947500907230181)
      ·
        refine ⟨57432077514552656420105659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306304413410947500907230181 57432077514552656420105659)
        ·
          refine ⟨86148116271828984630158489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57432077514552656420105659 86148116271828984630158489)
          ·
            refine ⟨64611087203871738472618867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86148116271828984630158489 64611087203871738472618867)
            ·
              refine ⟨96916630805807607708928301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64611087203871738472618867 96916630805807607708928301)
              ·
                refine ⟨36343736552177852890848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96916630805807607708928301 36343736552177852890848113)
                ·
                  refine ⟨27257802414133389668136085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36343736552177852890848113 27257802414133389668136085)
                  ·
                    refine ⟨1277709488162502640693879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27257802414133389668136085 1277709488162502640693879)
                    ·
                      rfl

theorem cell23_7464991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_7464991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7464991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7464991 prefixEnd_7464991 := by exact prefixLift 7464991
  have htrace : WordTrace (prefixWord ++ tailWord_7464991) baseStart_7464991 baseEnd_7464991 := by
    simpa [prefixWord, tailWord_7464991, baseEnd_7464991] using wordTrace_append hprefix tailTrace_7464991
  have hstable : (prefixWord ++ tailWord_7464991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7464991).length < 2 ^ (prefixWord ++ tailWord_7464991).sum := by decide
  have hdescent : baseEnd_7464991 < baseStart_7464991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7464991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465001 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_7465001 : Nat := 118140960795 + 7465001 * 2 ^ 59
def prefixEnd_7465001 : Nat := 4983230072969 + 3 ^ 40 * 7465001 * 2
def baseEnd_7465001 : Nat := 3833133599294052882956591

theorem tailTrace_7465001 : CollatzResearch.WordTrace tailWord_7465001 prefixEnd_7465001 3833133599294052882956591 := by
  unfold tailWord_7465001
  simp only [CollatzResearch.WordTrace]
  refine ⟨272270954428583772514290857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181513969619055848342860571 272270954428583772514290857)
  ·
    refine ⟨204203215821437829385718143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272270954428583772514290857 204203215821437829385718143)
    ·
      refine ⟨306304823732156744078577215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204203215821437829385718143 306304823732156744078577215)
      ·
        refine ⟨459457235598235116117865823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306304823732156744078577215 459457235598235116117865823)
        ·
          refine ⟨689185853397352674176798735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459457235598235116117865823 689185853397352674176798735)
          ·
            refine ⟨1033778780096029011265198103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689185853397352674176798735 1033778780096029011265198103)
            ·
              refine ⟨1550668170144043516897797155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033778780096029011265198103 1550668170144043516897797155)
              ·
                refine ⟨2326002255216065275346695733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550668170144043516897797155 2326002255216065275346695733)
                ·
                  refine ⟨218062711426506119563752725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326002255216065275346695733 218062711426506119563752725)
                  ·
                    refine ⟨10221689598117474354550909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218062711426506119563752725 10221689598117474354550909)
                    ·
                      refine ⟨3833133599294052882956591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10221689598117474354550909 3833133599294052882956591)
                      ·
                        rfl

theorem cell23_7465001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_7465001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465001 prefixEnd_7465001 := by exact prefixLift 7465001
  have htrace : WordTrace (prefixWord ++ tailWord_7465001) baseStart_7465001 baseEnd_7465001 := by
    simpa [prefixWord, tailWord_7465001, baseEnd_7465001] using wordTrace_append hprefix tailTrace_7465001
  have hstable : (prefixWord ++ tailWord_7465001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465001).length < 2 ^ (prefixWord ++ tailWord_7465001).sum := by decide
  have hdescent : baseEnd_7465001 < baseStart_7465001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465002 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7465002 : Nat := 118140960795 + 7465002 * 2 ^ 59
def prefixEnd_7465002 : Nat := 4983230072969 + 3 ^ 40 * 7465002 * 2
def baseEnd_7465002 : Nat := 3833134112774707379044087

theorem tailTrace_7465002 : CollatzResearch.WordTrace tailWord_7465002 prefixEnd_7465002 3833134112774707379044087 := by
  unfold tailWord_7465002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68067747725395037421269315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181513993934386766456718173 68067747725395037421269315)
  ·
    refine ⟨102101621588092556131903973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68067747725395037421269315 102101621588092556131903973)
    ·
      refine ⟨19144054047767354274731995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102101621588092556131903973 19144054047767354274731995)
      ·
        refine ⟨28716081071651031412097993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19144054047767354274731995 28716081071651031412097993)
        ·
          refine ⟨21537060803738273559073495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28716081071651031412097993 21537060803738273559073495)
          ·
            refine ⟨32305591205607410338610243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21537060803738273559073495 32305591205607410338610243)
            ·
              refine ⟨48458386808411115507915365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32305591205607410338610243 48458386808411115507915365)
              ·
                refine ⟨9085947526577084157734131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48458386808411115507915365 9085947526577084157734131)
                ·
                  refine ⟨13628921289865626236601197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9085947526577084157734131 13628921289865626236601197)
                  ·
                    refine ⟨5110845483699609838725449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13628921289865626236601197 5110845483699609838725449)
                    ·
                      refine ⟨3833134112774707379044087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110845483699609838725449 3833134112774707379044087)
                      ·
                        rfl

theorem cell23_7465002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7465002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465002 prefixEnd_7465002 := by exact prefixLift 7465002
  have htrace : WordTrace (prefixWord ++ tailWord_7465002) baseStart_7465002 baseEnd_7465002 := by
    simpa [prefixWord, tailWord_7465002, baseEnd_7465002] using wordTrace_append hprefix tailTrace_7465002
  have hstable : (prefixWord ++ tailWord_7465002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465002).length < 2 ^ (prefixWord ++ tailWord_7465002).sum := by decide
  have hdescent : baseEnd_7465002 < baseStart_7465002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465011 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_7465011 : Nat := 118140960795 + 7465011 * 2 ^ 59
def prefixEnd_7465011 : Nat := 4983230072969 + 3 ^ 40 * 7465011 * 2
def baseEnd_7465011 : Nat := 3833138734100597843831545

theorem tailTrace_7465011 : CollatzResearch.WordTrace tailWord_7465011 prefixEnd_7465011 3833138734100597843831545 := by
  unfold tailWord_7465011
  simp only [CollatzResearch.WordTrace]
  refine ⟨272271319158547544222154887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181514212772365029481436591 272271319158547544222154887)
  ·
    refine ⟨408406978737821316333232331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272271319158547544222154887 408406978737821316333232331)
    ·
      refine ⟨612610468106731974499848497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408406978737821316333232331 612610468106731974499848497)
      ·
        refine ⟨459457851080048980874886373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612610468106731974499848497 459457851080048980874886373)
        ·
          refine ⟨86148347077509183914041195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459457851080048980874886373 86148347077509183914041195)
          ·
            refine ⟨129222520616263775871061793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86148347077509183914041195 129222520616263775871061793)
            ·
              refine ⟨96916890462197831903296345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129222520616263775871061793 96916890462197831903296345)
              ·
                refine ⟨72687667846648373927472259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96916890462197831903296345 72687667846648373927472259)
                ·
                  refine ⟨109031501769972560891208389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72687667846648373927472259 109031501769972560891208389)
                  ·
                    refine ⟨20443406581869855167101573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109031501769972560891208389 20443406581869855167101573)
                    ·
                      refine ⟨3833138734100597843831545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20443406581869855167101573 3833138734100597843831545)
                      ·
                        rfl

theorem cell23_7465011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_7465011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465011 prefixEnd_7465011 := by exact prefixLift 7465011
  have htrace : WordTrace (prefixWord ++ tailWord_7465011) baseStart_7465011 baseEnd_7465011 := by
    simpa [prefixWord, tailWord_7465011, baseEnd_7465011] using wordTrace_append hprefix tailTrace_7465011
  have hstable : (prefixWord ++ tailWord_7465011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465011).length < 2 ^ (prefixWord ++ tailWord_7465011).sum := by decide
  have hdescent : baseEnd_7465011 < baseStart_7465011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465015 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_7465015 : Nat := 118140960795 + 7465015 * 2 ^ 59
def prefixEnd_7465015 : Nat := 4983230072969 + 3 ^ 40 * 7465015 * 2
def baseEnd_7465015 : Nat := 3833140788023215828181527

theorem tailTrace_7465015 : CollatzResearch.WordTrace tailWord_7465015 prefixEnd_7465015 3833140788023215828181527 := by
  unfold tailWord_7465015
  simp only [CollatzResearch.WordTrace]
  refine ⟨272271465050533052905300499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181514310033688701936866999 272271465050533052905300499)
  ·
    refine ⟨408407197575799579357950749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272271465050533052905300499 408407197575799579357950749)
    ·
      refine ⟨153152699090924842259231531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408407197575799579357950749 153152699090924842259231531)
      ·
        refine ⟨229729048636387263388847297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153152699090924842259231531 229729048636387263388847297)
        ·
          refine ⟨172296786477290447541635473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229729048636387263388847297 172296786477290447541635473)
          ·
            refine ⟨129222589857967835656226605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172296786477290447541635473 129222589857967835656226605)
            ·
              refine ⟨48458471196737938371084977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129222589857967835656226605 48458471196737938371084977)
              ·
                refine ⟨36343853397553453778313733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48458471196737938371084977 36343853397553453778313733)
                ·
                  refine ⟨6814472512041272583433825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36343853397553453778313733 6814472512041272583433825)
                  ·
                    refine ⟨5110854384030954437575369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6814472512041272583433825 5110854384030954437575369)
                    ·
                      refine ⟨3833140788023215828181527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5110854384030954437575369 3833140788023215828181527)
                      ·
                        rfl

theorem cell23_7465015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_7465015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465015 prefixEnd_7465015 := by exact prefixLift 7465015
  have htrace : WordTrace (prefixWord ++ tailWord_7465015) baseStart_7465015 baseEnd_7465015 := by
    simpa [prefixWord, tailWord_7465015, baseEnd_7465015] using wordTrace_append hprefix tailTrace_7465015
  have hstable : (prefixWord ++ tailWord_7465015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465015).length < 2 ^ (prefixWord ++ tailWord_7465015).sum := by decide
  have hdescent : baseEnd_7465015 < baseStart_7465015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465031 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_7465031 : Nat := 118140960795 + 7465031 * 2 ^ 59
def prefixEnd_7465031 : Nat := 4983230072969 + 3 ^ 40 * 7465031 * 2
def baseEnd_7465031 : Nat := 3833149003713687765581453

theorem tailTrace_7465031 : CollatzResearch.WordTrace tailWord_7465031 prefixEnd_7465031 3833149003713687765581453 := by
  unfold tailWord_7465031
  simp only [CollatzResearch.WordTrace]
  refine ⟨272272048618475087637882947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181514699078983391758588631 272272048618475087637882947)
  ·
    refine ⟨408408072927712631456824421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272272048618475087637882947 408408072927712631456824421)
    ·
      refine ⟨76576513673946118398154579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408408072927712631456824421 76576513673946118398154579)
      ·
        refine ⟨114864770510919177597231869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76576513673946118398154579 114864770510919177597231869)
        ·
          refine ⟨43074288941594691598961951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114864770510919177597231869 43074288941594691598961951)
          ·
            refine ⟨64611433412392037398442927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43074288941594691598961951 64611433412392037398442927)
            ·
              refine ⟨96917150118588056097664391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64611433412392037398442927 96917150118588056097664391)
              ·
                refine ⟨145375725177882084146496587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96917150118588056097664391 145375725177882084146496587)
                ·
                  refine ⟨218063587766823126219744881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145375725177882084146496587 218063587766823126219744881)
                  ·
                    refine ⟨163547690825117344664808661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 218063587766823126219744881 163547690825117344664808661)
                    ·
                      refine ⟨3833149003713687765581453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163547690825117344664808661 3833149003713687765581453)
                      ·
                        rfl

theorem cell23_7465031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_7465031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465031 prefixEnd_7465031 := by exact prefixLift 7465031
  have htrace : WordTrace (prefixWord ++ tailWord_7465031) baseStart_7465031 baseEnd_7465031 := by
    simpa [prefixWord, tailWord_7465031, baseEnd_7465031] using wordTrace_append hprefix tailTrace_7465031
  have hstable : (prefixWord ++ tailWord_7465031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465031).length < 2 ^ (prefixWord ++ tailWord_7465031).sum := by decide
  have hdescent : baseEnd_7465031 < baseStart_7465031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465038 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_7465038 : Nat := 118140960795 + 7465038 * 2 ^ 59
def prefixEnd_7465038 : Nat := 4983230072969 + 3 ^ 40 * 7465038 * 2
def baseEnd_7465038 : Nat := 425905844230918804243769

theorem tailTrace_7465038 : CollatzResearch.WordTrace tailWord_7465038 prefixEnd_7465038 425905844230918804243769 := by
  unfold tailWord_7465038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34034037991181215979173471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181514869286299818555591845 34034037991181215979173471)
  ·
    refine ⟨51051056986771823968760207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34034037991181215979173471 51051056986771823968760207)
    ·
      refine ⟨76576585480157735953140311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51051056986771823968760207 76576585480157735953140311)
      ·
        refine ⟨114864878220236603929710467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76576585480157735953140311 114864878220236603929710467)
        ·
          refine ⟨172297317330354905894565701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114864878220236603929710467 172297317330354905894565701)
          ·
            refine ⟨32305746999441544855231069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172297317330354905894565701 32305746999441544855231069)
            ·
              refine ⟨12114655124790579320711651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32305746999441544855231069 12114655124790579320711651)
              ·
                refine ⟨18171982687185868981067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114655124790579320711651 18171982687185868981067477)
                ·
                  refine ⟨425905844230918804243769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18171982687185868981067477 425905844230918804243769)
                  ·
                    rfl

theorem cell23_7465038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_7465038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465038 prefixEnd_7465038 := by exact prefixLift 7465038
  have htrace : WordTrace (prefixWord ++ tailWord_7465038) baseStart_7465038 baseEnd_7465038 := by
    simpa [prefixWord, tailWord_7465038, baseEnd_7465038] using wordTrace_append hprefix tailTrace_7465038
  have hstable : (prefixWord ++ tailWord_7465038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465038).length < 2 ^ (prefixWord ++ tailWord_7465038).sum := by decide
  have hdescent : baseEnd_7465038 < baseStart_7465038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465068 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_7465068 : Nat := 118140960795 + 7465068 * 2 ^ 59
def prefixEnd_7465068 : Nat := 4983230072969 + 3 ^ 40 * 7465068 * 2
def baseEnd_7465068 : Nat := 1277722667499301373606261

theorem tailTrace_7465068 : CollatzResearch.WordTrace tailWord_7465068 prefixEnd_7465068 1277722667499301373606261 := by
  unfold tailWord_7465068
  simp only [CollatzResearch.WordTrace]
  refine ⟨136136699059670521478489929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181515598746227361971319905 136136699059670521478489929)
  ·
    refine ⟨102102524294752891108867447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136136699059670521478489929 102102524294752891108867447)
    ·
      refine ⟨153153786442129336663301171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102102524294752891108867447 153153786442129336663301171)
      ·
        refine ⟨229730679663194004994951757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153153786442129336663301171 229730679663194004994951757)
        ·
          refine ⟨86149004873697751873106909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229730679663194004994951757 86149004873697751873106909)
          ·
            refine ⟨32305876827636656952415091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86149004873697751873106909 32305876827636656952415091)
            ·
              refine ⟨48458815241454985428622637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32305876827636656952415091 48458815241454985428622637)
              ·
                refine ⟨18172055715545619535733489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48458815241454985428622637 18172055715545619535733489)
                ·
                  refine ⟨13629041786659214651800117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18172055715545619535733489 13629041786659214651800117)
                  ·
                    refine ⟨1277722667499301373606261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13629041786659214651800117 1277722667499301373606261)
                    ·
                      rfl

theorem cell23_7465068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_7465068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465068 prefixEnd_7465068 := by exact prefixLift 7465068
  have htrace : WordTrace (prefixWord ++ tailWord_7465068) baseStart_7465068 baseEnd_7465068 := by
    simpa [prefixWord, tailWord_7465068, baseEnd_7465068] using wordTrace_append hprefix tailTrace_7465068
  have hstable : (prefixWord ++ tailWord_7465068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465068).length < 2 ^ (prefixWord ++ tailWord_7465068).sum := by decide
  have hdescent : baseEnd_7465068 < baseStart_7465068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465089 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 5]
def baseStart_7465089 : Nat := 118140960795 + 7465089 * 2 ^ 59
def prefixEnd_7465089 : Nat := 4983230072969 + 3 ^ 40 * 7465089 * 2
def baseEnd_7465089 : Nat := 425908753954627615406243

theorem tailTrace_7465089 : CollatzResearch.WordTrace tailWord_7465089 prefixEnd_7465089 425908753954627615406243 := by
  unfold tailWord_7465089
  simp only [CollatzResearch.WordTrace]
  refine ⟨272274164052264963543494321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181516109368176642362329547 272274164052264963543494321)
  ·
    refine ⟨204205623039198722657620741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272274164052264963543494321 204205623039198722657620741)
    ·
      refine ⟨38288554319849760498303889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204205623039198722657620741 38288554319849760498303889)
      ·
        refine ⟨28716415739887320373727917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38288554319849760498303889 28716415739887320373727917)
        ·
          refine ⟨10768655902457745140147969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28716415739887320373727917 10768655902457745140147969)
          ·
            refine ⟨8076491926843308855110977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768655902457745140147969 8076491926843308855110977)
            ·
              refine ⟨6057368945132481641333233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8076491926843308855110977 6057368945132481641333233)
              ·
                refine ⟨4543026708849361230999925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057368945132481641333233 4543026708849361230999925)
                ·
                  refine ⟨425908753954627615406243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4543026708849361230999925 425908753954627615406243)
                  ·
                    rfl

theorem cell23_7465089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 5].length) (baseStart_7465089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465089 prefixEnd_7465089 := by exact prefixLift 7465089
  have htrace : WordTrace (prefixWord ++ tailWord_7465089) baseStart_7465089 baseEnd_7465089 := by
    simpa [prefixWord, tailWord_7465089, baseEnd_7465089] using wordTrace_append hprefix tailTrace_7465089
  have hstable : (prefixWord ++ tailWord_7465089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465089).length < 2 ^ (prefixWord ++ tailWord_7465089).sum := by decide
  have hdescent : baseEnd_7465089 < baseStart_7465089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465122 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7465122 : Nat := 118140960795 + 7465122 * 2 ^ 59
def prefixEnd_7465122 : Nat := 4983230072969 + 3 ^ 40 * 7465122 * 2
def baseEnd_7465122 : Nat := 3833195730453246909543535

theorem tailTrace_7465122 : CollatzResearch.WordTrace tailWord_7465122 prefixEnd_7465122 3833195730453246909543535 := by
  unfold tailWord_7465122
  simp only [CollatzResearch.WordTrace]
  refine ⟨68068841915286352544861405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181516911774096940119630413 68068841915286352544861405)
  ·
    refine ⟨25525815718232382204323027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68068841915286352544861405 25525815718232382204323027)
    ·
      refine ⟨38288723577348573306484541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25525815718232382204323027 38288723577348573306484541)
      ·
        refine ⟨14358271341505714989931703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38288723577348573306484541 14358271341505714989931703)
        ·
          refine ⟨21537407012258572484897555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14358271341505714989931703 21537407012258572484897555)
          ·
            refine ⟨32306110518387858727346333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21537407012258572484897555 32306110518387858727346333)
            ·
              refine ⟨12114791444395447022754875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32306110518387858727346333 12114791444395447022754875)
              ·
                refine ⟨18172187166593170534132313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12114791444395447022754875 18172187166593170534132313)
                ·
                  refine ⟨13629140374944877900599235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18172187166593170534132313 13629140374944877900599235)
                  ·
                    refine ⟨20443710562417316850898853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13629140374944877900599235 20443710562417316850898853)
                    ·
                      refine ⟨3833195730453246909543535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20443710562417316850898853 3833195730453246909543535)
                      ·
                        rfl

theorem cell23_7465122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7465122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465122 prefixEnd_7465122 := by exact prefixLift 7465122
  have htrace : WordTrace (prefixWord ++ tailWord_7465122) baseStart_7465122 baseEnd_7465122 := by
    simpa [prefixWord, tailWord_7465122, baseEnd_7465122] using wordTrace_append hprefix tailTrace_7465122
  have hstable : (prefixWord ++ tailWord_7465122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465122).length < 2 ^ (prefixWord ++ tailWord_7465122).sum := by decide
  have hdescent : baseEnd_7465122 < baseStart_7465122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465188 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_7465188 : Nat := 118140960795 + 7465188 * 2 ^ 59
def prefixEnd_7465188 : Nat := 4983230072969 + 3 ^ 40 * 7465188 * 2
def baseEnd_7465188 : Nat := 1277743206725481217106077

theorem tailTrace_7465188 : CollatzResearch.WordTrace tailWord_7465188 prefixEnd_7465188 1277743206725481217106077 := by
  unfold tailWord_7465188
  simp only [CollatzResearch.WordTrace]
  refine ⟨136138887439453151725674109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181518516585937535634232145 136138887439453151725674109)
  ·
    refine ⟨51052082789794931897127791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136138887439453151725674109 51052082789794931897127791)
    ·
      refine ⟨76578124184692397845691687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51052082789794931897127791 76578124184692397845691687)
      ·
        refine ⟨114867186277038596768537531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76578124184692397845691687 114867186277038596768537531)
        ·
          refine ⟨172300779415557895152806297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114867186277038596768537531 172300779415557895152806297)
          ·
            refine ⟨129225584561668421364604723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172300779415557895152806297 129225584561668421364604723)
            ·
              refine ⟨193838376842502632046907085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129225584561668421364604723 193838376842502632046907085)
              ·
                refine ⟨72689391315938487017590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193838376842502632046907085 72689391315938487017590157)
                ·
                  refine ⟨27258521743476932631596309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72689391315938487017590157 27258521743476932631596309)
                  ·
                    refine ⟨1277743206725481217106077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27258521743476932631596309 1277743206725481217106077)
                    ·
                      rfl

theorem cell23_7465188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_7465188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465188 prefixEnd_7465188 := by exact prefixLift 7465188
  have htrace : WordTrace (prefixWord ++ tailWord_7465188) baseStart_7465188 baseEnd_7465188 := by
    simpa [prefixWord, tailWord_7465188, baseEnd_7465188] using wordTrace_append hprefix tailTrace_7465188
  have hstable : (prefixWord ++ tailWord_7465188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465188).length < 2 ^ (prefixWord ++ tailWord_7465188).sum := by decide
  have hdescent : baseEnd_7465188 < baseStart_7465188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465195 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 4]
def baseStart_7465195 : Nat := 118140960795 + 7465195 * 2 ^ 59
def prefixEnd_7465195 : Nat := 4983230072969 + 3 ^ 40 * 7465195 * 2
def baseEnd_7465195 : Nat := 3833233214541025123930699

theorem tailTrace_7465195 : CollatzResearch.WordTrace tailWord_7465195 prefixEnd_7465195 3833233214541025123930699 := by
  unfold tailWord_7465195
  simp only [CollatzResearch.WordTrace]
  refine ⟨272278030189880943646853039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181518686793253962431235359 272278030189880943646853039)
  ·
    refine ⟨408417045284821415470279559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272278030189880943646853039 408417045284821415470279559)
    ·
      refine ⟨612625567927232123205419339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408417045284821415470279559 612625567927232123205419339)
      ·
        refine ⟨918938351890848184808129009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612625567927232123205419339 918938351890848184808129009)
        ·
          refine ⟨689203763918136138606096757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918938351890848184808129009 689203763918136138606096757)
          ·
            refine ⟨64612852867325262994321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 689203763918136138606096757 64612852867325262994321571)
            ·
              refine ⟨96919279300987894491482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64612852867325262994321571 96919279300987894491482357)
              ·
                refine ⟨9086182434467615108576471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96919279300987894491482357 9086182434467615108576471)
                ·
                  refine ⟨13629273651701422662864707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9086182434467615108576471 13629273651701422662864707)
                  ·
                    refine ⟨20443910477552133994297061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13629273651701422662864707 20443910477552133994297061)
                    ·
                      refine ⟨3833233214541025123930699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20443910477552133994297061 3833233214541025123930699)
                      ·
                        rfl

theorem cell23_7465195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 4].length) (baseStart_7465195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465195 prefixEnd_7465195 := by exact prefixLift 7465195
  have htrace : WordTrace (prefixWord ++ tailWord_7465195) baseStart_7465195 baseEnd_7465195 := by
    simpa [prefixWord, tailWord_7465195, baseEnd_7465195] using wordTrace_append hprefix tailTrace_7465195
  have hstable : (prefixWord ++ tailWord_7465195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465195).length < 2 ^ (prefixWord ++ tailWord_7465195).sum := by decide
  have hdescent : baseEnd_7465195 < baseStart_7465195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465215 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_7465215 : Nat := 118140960795 + 7465215 * 2 ^ 59
def prefixEnd_7465215 : Nat := 4983230072969 + 3 ^ 40 * 7465215 * 2
def baseEnd_7465215 : Nat := 3833243484154115045680607

theorem tailTrace_7465215 : CollatzResearch.WordTrace tailWord_7465215 prefixEnd_7465215 3833243484154115045680607 := by
  unfold tailWord_7465215
  simp only [CollatzResearch.WordTrace]
  refine ⟨272278759649808487062581099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181519173099872324708387399 272278759649808487062581099)
  ·
    refine ⟨408418139474712730593871649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272278759649808487062581099 408418139474712730593871649)
    ·
      refine ⟨306313604606034547945403737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408418139474712730593871649 306313604606034547945403737)
      ·
        refine ⟨229735203454525910959052803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306313604606034547945403737 229735203454525910959052803)
        ·
          refine ⟨344602805181788866438579205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229735203454525910959052803 344602805181788866438579205)
          ·
            refine ⟨64613025971585412457233601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344602805181788866438579205 64613025971585412457233601)
            ·
              refine ⟨48459769478689059342925201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64613025971585412457233601 48459769478689059342925201)
              ·
                refine ⟨36344827109016794507193901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48459769478689059342925201 36344827109016794507193901)
                ·
                  refine ⟨13629310165881297940197713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36344827109016794507193901 13629310165881297940197713)
                  ·
                    refine ⟨10221982624410973455148285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13629310165881297940197713 10221982624410973455148285)
                    ·
                      refine ⟨3833243484154115045680607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10221982624410973455148285 3833243484154115045680607)
                      ·
                        rfl

theorem cell23_7465215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_7465215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465215 prefixEnd_7465215 := by exact prefixLift 7465215
  have htrace : WordTrace (prefixWord ++ tailWord_7465215) baseStart_7465215 baseEnd_7465215 := by
    simpa [prefixWord, tailWord_7465215, baseEnd_7465215] using wordTrace_append hprefix tailTrace_7465215
  have hstable : (prefixWord ++ tailWord_7465215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465215).length < 2 ^ (prefixWord ++ tailWord_7465215).sum := by decide
  have hdescent : baseEnd_7465215 < baseStart_7465215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465242 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_7465242 : Nat := 118140960795 + 7465242 * 2 ^ 59
def prefixEnd_7465242 : Nat := 4983230072969 + 3 ^ 40 * 7465242 * 2
def baseEnd_7465242 : Nat := 3833257348131786440042983

theorem tailTrace_7465242 : CollatzResearch.WordTrace tailWord_7465242 prefixEnd_7465242 3833257348131786440042983 := by
  unfold tailWord_7465242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68069936105177667668453495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181519829613807113782542653 68069936105177667668453495)
  ·
    refine ⟨102104904157766501502680243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68069936105177667668453495 102104904157766501502680243)
    ·
      refine ⟨153157356236649752254020365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102104904157766501502680243 153157356236649752254020365)
      ·
        refine ⟨57434008588743657095257637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153157356236649752254020365 57434008588743657095257637)
        ·
          refine ⟨10768876610389435705360807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57434008588743657095257637 10768876610389435705360807)
          ·
            refine ⟨16153314915584153558041211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10768876610389435705360807 16153314915584153558041211)
            ·
              refine ⟨24229972373376230337061817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16153314915584153558041211 24229972373376230337061817)
              ·
                refine ⟨18172479280032172752796363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24229972373376230337061817 18172479280032172752796363)
                ·
                  refine ⟨27258718920048259129194545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18172479280032172752796363 27258718920048259129194545)
                  ·
                    refine ⟨20444039190036194346895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27258718920048259129194545 20444039190036194346895909)
                    ·
                      refine ⟨3833257348131786440042983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20444039190036194346895909 3833257348131786440042983)
                      ·
                        rfl

theorem cell23_7465242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_7465242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465242 prefixEnd_7465242 := by exact prefixLift 7465242
  have htrace : WordTrace (prefixWord ++ tailWord_7465242) baseStart_7465242 baseEnd_7465242 := by
    simpa [prefixWord, tailWord_7465242, baseEnd_7465242] using wordTrace_append hprefix tailTrace_7465242
  have hstable : (prefixWord ++ tailWord_7465242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465242).length < 2 ^ (prefixWord ++ tailWord_7465242).sum := by decide
  have hdescent : baseEnd_7465242 < baseStart_7465242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465272 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2]
def baseStart_7465272 : Nat := 118140960795 + 7465272 * 2 ^ 59
def prefixEnd_7465272 : Nat := 4983230072969 + 3 ^ 40 * 7465272 * 2
def baseEnd_7465272 : Nat := 3833272752551421322667845

theorem tailTrace_7465272 : CollatzResearch.WordTrace tailWord_7465272 prefixEnd_7465272 3833272752551421322667845 := by
  unfold tailWord_7465272
  simp only [CollatzResearch.WordTrace]
  refine ⟨136140419305300992898703035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181520559073734657198270713 136140419305300992898703035)
  ·
    refine ⟨204210628957951489348054553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136140419305300992898703035 204210628957951489348054553)
    ·
      refine ⟨153157971718463617011040915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204210628957951489348054553 153157971718463617011040915)
      ·
        refine ⟨229736957577695425516561373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153157971718463617011040915 229736957577695425516561373)
        ·
          refine ⟨86151359091635784568710515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229736957577695425516561373 86151359091635784568710515)
          ·
            refine ⟨129227038637453676853065773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86151359091635784568710515 129227038637453676853065773)
            ·
              refine ⟨48460139489045128819899665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129227038637453676853065773 48460139489045128819899665)
              ·
                refine ⟨36345104616783846614924749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48460139489045128819899665 36345104616783846614924749)
                ·
                  refine ⟨13629414231293942480596781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36345104616783846614924749 13629414231293942480596781)
                  ·
                    refine ⟨5111030336735228430223793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13629414231293942480596781 5111030336735228430223793)
                    ·
                      refine ⟨3833272752551421322667845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111030336735228430223793 3833272752551421322667845)
                      ·
                        rfl

theorem cell23_7465272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_7465272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465272 prefixEnd_7465272 := by exact prefixLift 7465272
  have htrace : WordTrace (prefixWord ++ tailWord_7465272) baseStart_7465272 baseEnd_7465272 := by
    simpa [prefixWord, tailWord_7465272, baseEnd_7465272] using wordTrace_append hprefix tailTrace_7465272
  have hstable : (prefixWord ++ tailWord_7465272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465272).length < 2 ^ (prefixWord ++ tailWord_7465272).sum := by decide
  have hdescent : baseEnd_7465272 < baseStart_7465272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465315 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7465315 : Nat := 118140960795 + 7465315 * 2 ^ 59
def prefixEnd_7465315 : Nat := 4983230072969 + 3 ^ 40 * 7465315 * 2
def baseEnd_7465315 : Nat := 3833294832219564654430147

theorem tailTrace_7465315 : CollatzResearch.WordTrace tailWord_7465315 prefixEnd_7465315 3833294832219564654430147 := by
  unfold tailWord_7465315
  simp only [CollatzResearch.WordTrace]
  refine ⟨272282406949446204141221399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181521604632964136094147599 272282406949446204141221399)
  ·
    refine ⟨408423610424169306211832099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272282406949446204141221399 408423610424169306211832099)
    ·
      refine ⟨612635415636253959317748149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408423610424169306211832099 612635415636253959317748149)
      ·
        refine ⟨57434570215898808686038889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612635415636253959317748149 57434570215898808686038889)
        ·
          refine ⟨43075927661924106514529167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57434570215898808686038889 43075927661924106514529167)
          ·
            refine ⟨64613891492886159771793751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43075927661924106514529167 64613891492886159771793751)
            ·
              refine ⟨96920837239329239657690627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64613891492886159771793751 96920837239329239657690627)
              ·
                refine ⟨145381255858993859486535941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96920837239329239657690627 145381255858993859486535941)
                ·
                  refine ⟨27258985473561348653725489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145381255858993859486535941 27258985473561348653725489)
                  ·
                    refine ⟨20444239105171011490294117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27258985473561348653725489 20444239105171011490294117)
                    ·
                      refine ⟨3833294832219564654430147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20444239105171011490294117 3833294832219564654430147)
                      ·
                        rfl

theorem cell23_7465315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7465315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465315 prefixEnd_7465315 := by exact prefixLift 7465315
  have htrace : WordTrace (prefixWord ++ tailWord_7465315) baseStart_7465315 baseEnd_7465315 := by
    simpa [prefixWord, tailWord_7465315, baseEnd_7465315] using wordTrace_append hprefix tailTrace_7465315
  have hstable : (prefixWord ++ tailWord_7465315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465315).length < 2 ^ (prefixWord ++ tailWord_7465315).sum := by decide
  have hdescent : baseEnd_7465315 < baseStart_7465315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465335 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_7465335 : Nat := 118140960795 + 7465335 * 2 ^ 59
def prefixEnd_7465335 : Nat := 4983230072969 + 3 ^ 40 * 7465335 * 2
def baseEnd_7465335 : Nat := 3833305101832654576180055

theorem tailTrace_7465335 : CollatzResearch.WordTrace tailWord_7465335 prefixEnd_7465335 3833305101832654576180055 := by
  unfold tailWord_7465335
  simp only [CollatzResearch.WordTrace]
  refine ⟨272283136409373747556949459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181522090939582498371299639 272283136409373747556949459)
  ·
    refine ⟨408424704614060621335424189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272283136409373747556949459 408424704614060621335424189)
    ·
      refine ⟨153159264230272733000784071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408424704614060621335424189 153159264230272733000784071)
      ·
        refine ⟨229738896345409099501176107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153159264230272733000784071 229738896345409099501176107)
        ·
          refine ⟨344608344518113649251764161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229738896345409099501176107 344608344518113649251764161)
          ·
            refine ⟨258456258388585236938823121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344608344518113649251764161 258456258388585236938823121)
            ·
              refine ⟨193842193791438927704117341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258456258388585236938823121 193842193791438927704117341)
              ·
                refine ⟨72690822671789597889044003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193842193791438927704117341 72690822671789597889044003)
                ·
                  refine ⟨109036234007684396833566005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72690822671789597889044003 109036234007684396833566005)
                  ·
                    refine ⟨10222146938220412203146813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109036234007684396833566005 10222146938220412203146813)
                    ·
                      refine ⟨3833305101832654576180055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10222146938220412203146813 3833305101832654576180055)
                      ·
                        rfl

theorem cell23_7465335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_7465335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465335 prefixEnd_7465335 := by exact prefixLift 7465335
  have htrace : WordTrace (prefixWord ++ tailWord_7465335) baseStart_7465335 baseEnd_7465335 := by
    simpa [prefixWord, tailWord_7465335, baseEnd_7465335] using wordTrace_append hprefix tailTrace_7465335
  have hstable : (prefixWord ++ tailWord_7465335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465335).length < 2 ^ (prefixWord ++ tailWord_7465335).sum := by decide
  have hdescent : baseEnd_7465335 < baseStart_7465335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465355 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 7]
def baseStart_7465355 : Nat := 118140960795 + 7465355 * 2 ^ 59
def prefixEnd_7465355 : Nat := 4983230072969 + 3 ^ 40 * 7465355 * 2
def baseEnd_7465355 : Nat := 1277771790481914832643321

theorem tailTrace_7465355 : CollatzResearch.WordTrace tailWord_7465355 prefixEnd_7465355 1277771790481914832643321 := by
  unfold tailWord_7465355
  simp only [CollatzResearch.WordTrace]
  refine ⟨272283865869301290972677519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181522577246200860648451679 272283865869301290972677519)
  ·
    refine ⟨408425798803951936459016279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272283865869301290972677519 408425798803951936459016279)
    ·
      refine ⟨612638698205927904688524419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408425798803951936459016279 612638698205927904688524419)
      ·
        refine ⟨918958047308891857032786629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612638698205927904688524419 918958047308891857032786629)
        ·
          refine ⟨172304633870417223193647493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 918958047308891857032786629 172304633870417223193647493)
          ·
            refine ⟨32307118850703229348808905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172304633870417223193647493 32307118850703229348808905)
            ·
              refine ⟨24230339138027422011606679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32307118850703229348808905 24230339138027422011606679)
              ·
                refine ⟨36345508707041133017410019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24230339138027422011606679 36345508707041133017410019)
                ·
                  refine ⟨54518263060561699526115029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36345508707041133017410019 54518263060561699526115029)
                  ·
                    refine ⟨1277771790481914832643321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54518263060561699526115029 1277771790481914832643321)
                    ·
                      rfl

theorem cell23_7465355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_7465355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465355 prefixEnd_7465355 := by exact prefixLift 7465355
  have htrace : WordTrace (prefixWord ++ tailWord_7465355) baseStart_7465355 baseEnd_7465355 := by
    simpa [prefixWord, tailWord_7465355, baseEnd_7465355] using wordTrace_append hprefix tailTrace_7465355
  have hstable : (prefixWord ++ tailWord_7465355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465355).length < 2 ^ (prefixWord ++ tailWord_7465355).sum := by decide
  have hdescent : baseEnd_7465355 < baseStart_7465355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465365 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_7465365 : Nat := 118140960795 + 7465365 * 2 ^ 59
def prefixEnd_7465365 : Nat := 4983230072969 + 3 ^ 40 * 7465365 * 2
def baseEnd_7465365 : Nat := 3833320506252289458804917

theorem tailTrace_7465365 : CollatzResearch.WordTrace tailWord_7465365 prefixEnd_7465365 3833320506252289458804917 := by
  unfold tailWord_7465365
  simp only [CollatzResearch.WordTrace]
  refine ⟨272284230599265062680541549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181522820399510041787027699 272284230599265062680541549)
  ·
    refine ⟨102106586474724398505203081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272284230599265062680541549 102106586474724398505203081)
    ·
      refine ⟨76579939856043298878902311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102106586474724398505203081 76579939856043298878902311)
      ·
        refine ⟨114869909784064948318353467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76579939856043298878902311 114869909784064948318353467)
        ·
          refine ⟨172304864676097422477530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114869909784064948318353467 172304864676097422477530201)
          ·
            refine ⟨129228648507073066858147651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172304864676097422477530201 129228648507073066858147651)
            ·
              refine ⟨193842972760609600287221477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129228648507073066858147651 193842972760609600287221477)
              ·
                refine ⟨36345557392614300053854027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193842972760609600287221477 36345557392614300053854027)
                ·
                  refine ⟨54518336088921450080781041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36345557392614300053854027 54518336088921450080781041)
                  ·
                    refine ⟨40888752066691087560585781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54518336088921450080781041 40888752066691087560585781)
                    ·
                      refine ⟨3833320506252289458804917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40888752066691087560585781 3833320506252289458804917)
                      ·
                        rfl

theorem cell23_7465365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_7465365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465365 prefixEnd_7465365 := by exact prefixLift 7465365
  have htrace : WordTrace (prefixWord ++ tailWord_7465365) baseStart_7465365 baseEnd_7465365 := by
    simpa [prefixWord, tailWord_7465365, baseEnd_7465365] using wordTrace_append hprefix tailTrace_7465365
  have hstable : (prefixWord ++ tailWord_7465365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465365).length < 2 ^ (prefixWord ++ tailWord_7465365).sum := by decide
  have hdescent : baseEnd_7465365 < baseStart_7465365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465392 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2]
def baseStart_7465392 : Nat := 118140960795 + 7465392 * 2 ^ 59
def prefixEnd_7465392 : Nat := 4983230072969 + 3 ^ 40 * 7465392 * 2
def baseEnd_7465392 : Nat := 3833334370229960853167293

theorem tailTrace_7465392 : CollatzResearch.WordTrace tailWord_7465392 prefixEnd_7465392 3833334370229960853167293 := by
  unfold tailWord_7465392
  simp only [CollatzResearch.WordTrace]
  refine ⟨136142607685083623145887215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181523476913444830861182953 136142607685083623145887215)
  ·
    refine ⟨204213911527625434718830823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136142607685083623145887215 204213911527625434718830823)
    ·
      refine ⟨306320867291438152078246235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204213911527625434718830823 306320867291438152078246235)
      ·
        refine ⟨459481300937157228117369353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306320867291438152078246235 459481300937157228117369353)
        ·
          refine ⟨344610975702867921088027015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459481300937157228117369353 344610975702867921088027015)
          ·
            refine ⟨516916463554301881632040523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344610975702867921088027015 516916463554301881632040523)
            ·
              refine ⟨775374695331452822448060785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516916463554301881632040523 775374695331452822448060785)
              ·
                refine ⟨581531021498589616836045589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775374695331452822448060785 581531021498589616836045589)
                ·
                  refine ⟨27259266632746388289189637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 581531021498589616836045589 27259266632746388289189637)
                  ·
                    refine ⟨5111112493639947804223057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27259266632746388289189637 5111112493639947804223057)
                    ·
                      refine ⟨3833334370229960853167293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111112493639947804223057 3833334370229960853167293)
                      ·
                        rfl

theorem cell23_7465392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 4, 2].length) (baseStart_7465392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465392 prefixEnd_7465392 := by exact prefixLift 7465392
  have htrace : WordTrace (prefixWord ++ tailWord_7465392) baseStart_7465392 baseEnd_7465392 := by
    simpa [prefixWord, tailWord_7465392, baseEnd_7465392] using wordTrace_append hprefix tailTrace_7465392
  have hstable : (prefixWord ++ tailWord_7465392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465392).length < 2 ^ (prefixWord ++ tailWord_7465392).sum := by decide
  have hdescent : baseEnd_7465392 < baseStart_7465392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465402 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_7465402 : Nat := 118140960795 + 7465402 * 2 ^ 59
def prefixEnd_7465402 : Nat := 4983230072969 + 3 ^ 40 * 7465402 * 2
def baseEnd_7465402 : Nat := 1277779835012168604680749

theorem tailTrace_7465402 : CollatzResearch.WordTrace tailWord_7465402 prefixEnd_7465402 1277779835012168604680749 := by
  unfold tailWord_7465402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68071395025032754499909615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181523720066754011999758973 68071395025032754499909615)
  ·
    refine ⟨102107092537549131749864423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68071395025032754499909615 102107092537549131749864423)
    ·
      refine ⟨153160638806323697624796635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102107092537549131749864423 153160638806323697624796635)
      ·
        refine ⟨229740958209485546437194953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153160638806323697624796635 229740958209485546437194953)
        ·
          refine ⟨172305718657114159827896215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229740958209485546437194953 172305718657114159827896215)
          ·
            refine ⟨258458577985671239741844323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172305718657114159827896215 258458577985671239741844323)
            ·
              refine ⟨387687866978506859612766485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258458577985671239741844323 387687866978506859612766485)
              ·
                refine ⟨18172868764617509044348429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 387687866978506859612766485 18172868764617509044348429)
                ·
                  refine ⟨6814825786731565891630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18172868764617509044348429 6814825786731565891630661)
                  ·
                    refine ⟨1277779835012168604680749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814825786731565891630661 1277779835012168604680749)
                    ·
                      rfl

theorem cell23_7465402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_7465402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465402 prefixEnd_7465402 := by exact prefixLift 7465402
  have htrace : WordTrace (prefixWord ++ tailWord_7465402) baseStart_7465402 baseEnd_7465402 := by
    simpa [prefixWord, tailWord_7465402, baseEnd_7465402] using wordTrace_append hprefix tailTrace_7465402
  have hstable : (prefixWord ++ tailWord_7465402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465402).length < 2 ^ (prefixWord ++ tailWord_7465402).sum := by decide
  have hdescent : baseEnd_7465402 < baseStart_7465402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465419 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 1, 4]
def baseStart_7465419 : Nat := 118140960795 + 7465419 * 2 ^ 59
def prefixEnd_7465419 : Nat := 4983230072969 + 3 ^ 40 * 7465419 * 2
def baseEnd_7465419 : Nat := 1277782744735877415843223

theorem tailTrace_7465419 : CollatzResearch.WordTrace tailWord_7465419 prefixEnd_7465419 1277782744735877415843223 := by
  unfold tailWord_7465419
  simp only [CollatzResearch.WordTrace]
  refine ⟨272286200141069429903007311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181524133427379619935338207 272286200141069429903007311)
  ·
    refine ⟨408429300211604144854510967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272286200141069429903007311 408429300211604144854510967)
    ·
      refine ⟨612643950317406217281766451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408429300211604144854510967 612643950317406217281766451)
      ·
        refine ⟨918965925476109325922649677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612643950317406217281766451 918965925476109325922649677)
        ·
          refine ⟨344612222053540997220993629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 918965925476109325922649677 344612222053540997220993629)
          ·
            refine ⟨129229583270077873957872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344612222053540997220993629 129229583270077873957872611)
            ·
              refine ⟨193844374905116810936808917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129229583270077873957872611 193844374905116810936808917)
              ·
                refine ⟨4543227536838675256331459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193844374905116810936808917 4543227536838675256331459)
                ·
                  refine ⟨6814841305258012884497189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543227536838675256331459 6814841305258012884497189)
                  ·
                    refine ⟨1277782744735877415843223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814841305258012884497189 1277782744735877415843223)
                    ·
                      rfl

theorem cell23_7465419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 4].length) (baseStart_7465419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465419 prefixEnd_7465419 := by exact prefixLift 7465419
  have htrace : WordTrace (prefixWord ++ tailWord_7465419) baseStart_7465419 baseEnd_7465419 := by
    simpa [prefixWord, tailWord_7465419, baseEnd_7465419] using wordTrace_append hprefix tailTrace_7465419
  have hstable : (prefixWord ++ tailWord_7465419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465419).length < 2 ^ (prefixWord ++ tailWord_7465419).sum := by decide
  have hdescent : baseEnd_7465419 < baseStart_7465419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465429 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7465429 : Nat := 118140960795 + 7465429 * 2 ^ 59
def prefixEnd_7465429 : Nat := 4983230072969 + 3 ^ 40 * 7465429 * 2
def baseEnd_7465429 : Nat := 3833353369014177208404623

theorem tailTrace_7465429 : CollatzResearch.WordTrace tailWord_7465429 prefixEnd_7465429 3833353369014177208404623 := by
  unfold tailWord_7465429
  simp only [CollatzResearch.WordTrace]
  refine ⟨272286564871033201610871341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181524376580688801073914227 272286564871033201610871341)
  ·
    refine ⟨102107461826637450604076753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272286564871033201610871341 102107461826637450604076753)
    ·
      refine ⟨76580596369978087953057565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102107461826637450604076753 76580596369978087953057565)
      ·
        refine ⟨28717723638741782982396587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76580596369978087953057565 28717723638741782982396587)
        ·
          refine ⟨43076585458112674473594881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28717723638741782982396587 43076585458112674473594881)
          ·
            refine ⟨32307439093584505855196161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43076585458112674473594881 32307439093584505855196161)
            ·
              refine ⟨24230579320188379391397121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32307439093584505855196161 24230579320188379391397121)
              ·
                refine ⟨18172934490141284543547841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24230579320188379391397121 18172934490141284543547841)
                ·
                  refine ⟨13629700867605963407660881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18172934490141284543547841 13629700867605963407660881)
                  ·
                    refine ⟨10222275650704472555745661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13629700867605963407660881 10222275650704472555745661)
                    ·
                      refine ⟨3833353369014177208404623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10222275650704472555745661 3833353369014177208404623)
                      ·
                        rfl

theorem cell23_7465429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7465429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465429 prefixEnd_7465429 := by exact prefixLift 7465429
  have htrace : WordTrace (prefixWord ++ tailWord_7465429) baseStart_7465429 baseEnd_7465429 := by
    simpa [prefixWord, tailWord_7465429, baseEnd_7465429] using wordTrace_append hprefix tailTrace_7465429
  have hstable : (prefixWord ++ tailWord_7465429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465429).length < 2 ^ (prefixWord ++ tailWord_7465429).sum := by decide
  have hdescent : baseEnd_7465429 < baseStart_7465429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465455 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_7465455 : Nat := 118140960795 + 7465455 * 2 ^ 59
def prefixEnd_7465455 : Nat := 4983230072969 + 3 ^ 40 * 7465455 * 2
def baseEnd_7465455 : Nat := 3833366719511194106679503

theorem tailTrace_7465455 : CollatzResearch.WordTrace tailWord_7465455 prefixEnd_7465455 3833366719511194106679503 := by
  unfold tailWord_7465455
  simp only [CollatzResearch.WordTrace]
  refine ⟨272287513168939008051317819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181525008779292672034211879 272287513168939008051317819)
  ·
    refine ⟨408431269753408512076976729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272287513168939008051317819 408431269753408512076976729)
    ·
      refine ⟨306323452315056384057732547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408431269753408512076976729 306323452315056384057732547)
      ·
        refine ⟨459485178472584576086598821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306323452315056384057732547 459485178472584576086598821)
        ·
          refine ⟨86153470963609608016237279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459485178472584576086598821 86153470963609608016237279)
          ·
            refine ⟨129230206445414412024355919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86153470963609608016237279 129230206445414412024355919)
            ·
              refine ⟨193845309668121618036533879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129230206445414412024355919 193845309668121618036533879)
              ·
                refine ⟨290767964502182427054800819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193845309668121618036533879 290767964502182427054800819)
                ·
                  refine ⟨436151946753273640582201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290767964502182427054800819 436151946753273640582201229)
                  ·
                    refine ⟨163556980032477615218325461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 436151946753273640582201229 163556980032477615218325461)
                    ·
                      refine ⟨3833366719511194106679503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163556980032477615218325461 3833366719511194106679503)
                      ·
                        rfl

theorem cell23_7465455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_7465455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465455 prefixEnd_7465455 := by exact prefixLift 7465455
  have htrace : WordTrace (prefixWord ++ tailWord_7465455) baseStart_7465455 baseEnd_7465455 := by
    simpa [prefixWord, tailWord_7465455, baseEnd_7465455] using wordTrace_append hprefix tailTrace_7465455
  have hstable : (prefixWord ++ tailWord_7465455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465455).length < 2 ^ (prefixWord ++ tailWord_7465455).sum := by decide
  have hdescent : baseEnd_7465455 < baseStart_7465455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465459 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 3]
def baseStart_7465459 : Nat := 118140960795 + 7465459 * 2 ^ 59
def prefixEnd_7465459 : Nat := 4983230072969 + 3 ^ 40 * 7465459 * 2
def baseEnd_7465459 : Nat := 3833368773433812091029485

theorem tailTrace_7465459 : CollatzResearch.WordTrace tailWord_7465459 prefixEnd_7465459 3833368773433812091029485 := by
  unfold tailWord_7465459
  simp only [CollatzResearch.WordTrace]
  refine ⟨272287659060924516734463431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181525106040616344489642287 272287659060924516734463431)
  ·
    refine ⟨408431488591386775101695147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272287659060924516734463431 408431488591386775101695147)
    ·
      refine ⟨612647232887080162652542721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408431488591386775101695147 612647232887080162652542721)
      ·
        refine ⟨459485424665310121989407041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612647232887080162652542721 459485424665310121989407041)
        ·
          refine ⟨344614068498982591492055281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459485424665310121989407041 344614068498982591492055281)
          ·
            refine ⟨258460551374236943619041461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344614068498982591492055281 258460551374236943619041461)
            ·
              refine ⟨24230676691334713464285137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258460551374236943619041461 24230676691334713464285137)
              ·
                refine ⟨18173007518501035098213853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24230676691334713464285137 18173007518501035098213853)
                ·
                  refine ⟨6814877819437888161830195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18173007518501035098213853 6814877819437888161830195)
                  ·
                    refine ⟨10222316729156832242745293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6814877819437888161830195 10222316729156832242745293)
                    ·
                      refine ⟨3833368773433812091029485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10222316729156832242745293 3833368773433812091029485)
                      ·
                        rfl

theorem cell23_7465459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_7465459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465459 prefixEnd_7465459 := by exact prefixLift 7465459
  have htrace : WordTrace (prefixWord ++ tailWord_7465459) baseStart_7465459 baseEnd_7465459 := by
    simpa [prefixWord, tailWord_7465459, baseEnd_7465459] using wordTrace_append hprefix tailTrace_7465459
  have hstable : (prefixWord ++ tailWord_7465459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465459).length < 2 ^ (prefixWord ++ tailWord_7465459).sum := by decide
  have hdescent : baseEnd_7465459 < baseStart_7465459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465469 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_7465469 : Nat := 118140960795 + 7465469 * 2 ^ 59
def prefixEnd_7465469 : Nat := 4983230072969 + 3 ^ 40 * 7465469 * 2
def baseEnd_7465469 : Nat := 3833373908240357051904439

theorem tailTrace_7465469 : CollatzResearch.WordTrace tailWord_7465469 prefixEnd_7465469 3833373908240357051904439 := by
  unfold tailWord_7465469
  simp only [CollatzResearch.WordTrace]
  refine ⟨272288023790888288442327461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181525349193925525628218307 272288023790888288442327461)
  ·
    refine ⟨51054004460791554082936399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272288023790888288442327461 51054004460791554082936399)
    ·
      refine ⟨76581006691187331124404599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51054004460791554082936399 76581006691187331124404599)
      ·
        refine ⟨114871510036780996686606899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76581006691187331124404599 114871510036780996686606899)
        ·
          refine ⟨172307265055171495029910349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114871510036780996686606899 172307265055171495029910349)
          ·
            refine ⟨64615224395689310636216381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172307265055171495029910349 64615224395689310636216381)
            ·
              refine ⟨24230709148383491488581143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64615224395689310636216381 24230709148383491488581143)
              ·
                refine ⟨36346063722575237232871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24230709148383491488581143 36346063722575237232871715)
                ·
                  refine ⟨54519095583862855849307573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36346063722575237232871715 54519095583862855849307573)
                  ·
                    refine ⟨5111165210987142735872585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54519095583862855849307573 5111165210987142735872585)
                    ·
                      refine ⟨3833373908240357051904439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111165210987142735872585 3833373908240357051904439)
                      ·
                        rfl

theorem cell23_7465469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_7465469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465469 prefixEnd_7465469 := by exact prefixLift 7465469
  have htrace : WordTrace (prefixWord ++ tailWord_7465469) baseStart_7465469 baseEnd_7465469 := by
    simpa [prefixWord, tailWord_7465469, baseEnd_7465469] using wordTrace_append hprefix tailTrace_7465469
  have hstable : (prefixWord ++ tailWord_7465469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465469).length < 2 ^ (prefixWord ++ tailWord_7465469).sum := by decide
  have hdescent : baseEnd_7465469 < baseStart_7465469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465509 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_7465509 : Nat := 118140960795 + 7465509 * 2 ^ 59
def prefixEnd_7465509 : Nat := 4983230072969 + 3 ^ 40 * 7465509 * 2
def baseEnd_7465509 : Nat := 1277798149155512298468085

theorem tailTrace_7465509 : CollatzResearch.WordTrace tailWord_7465509 prefixEnd_7465509 1277798149155512298468085 := by
  unfold tailWord_7465509
  simp only [CollatzResearch.WordTrace]
  refine ⟨272289482710743375273783581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181526321807162250182522387 272289482710743375273783581)
  ·
    refine ⟨102108556016528765727668843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272289482710743375273783581 102108556016528765727668843)
    ·
      refine ⟨153162834024793148591503265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102108556016528765727668843 153162834024793148591503265)
      ·
        refine ⟨114872125518594861443627449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153162834024793148591503265 114872125518594861443627449)
        ·
          refine ⟨86154094138946146082720587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114872125518594861443627449 86154094138946146082720587)
          ·
            refine ⟨129231141208419219124080881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86154094138946146082720587 129231141208419219124080881)
            ·
              refine ⟨96923355906314414343060661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129231141208419219124080881 96923355906314414343060661)
              ·
                refine ⟨9086564616216976344661937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96923355906314414343060661 9086564616216976344661937)
                ·
                  refine ⟨6814923462162732258496453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9086564616216976344661937 6814923462162732258496453)
                  ·
                    refine ⟨1277798149155512298468085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814923462162732258496453 1277798149155512298468085)
                    ·
                      rfl

theorem cell23_7465509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_7465509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465509 prefixEnd_7465509 := by exact prefixLift 7465509
  have htrace : WordTrace (prefixWord ++ tailWord_7465509) baseStart_7465509 baseEnd_7465509 := by
    simpa [prefixWord, tailWord_7465509, baseEnd_7465509] using wordTrace_append hprefix tailTrace_7465509
  have hstable : (prefixWord ++ tailWord_7465509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465509).length < 2 ^ (prefixWord ++ tailWord_7465509).sum := by decide
  have hdescent : baseEnd_7465509 < baseStart_7465509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465526 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7465526 : Nat := 118140960795 + 7465526 * 2 ^ 59
def prefixEnd_7465526 : Nat := 4983230072969 + 3 ^ 40 * 7465526 * 2
def baseEnd_7465526 : Nat := 1277801058879221109630559

theorem tailTrace_7465526 : CollatzResearch.WordTrace tailWord_7465526 prefixEnd_7465526 1277801058879221109630559 := by
  unfold tailWord_7465526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018131421980111698572027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181526735167787858118101621 17018131421980111698572027)
  ·
    refine ⟨25527197132970167547858041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17018131421980111698572027 25527197132970167547858041)
    ·
      refine ⟨19145397849727625660893531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25527197132970167547858041 19145397849727625660893531)
      ·
        refine ⟨28718096774591438491340297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19145397849727625660893531 28718096774591438491340297)
        ·
          refine ⟨21538572580943578868505223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28718096774591438491340297 21538572580943578868505223)
          ·
            refine ⟨32307858871415368302757835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21538572580943578868505223 32307858871415368302757835)
            ·
              refine ⟨48461788307123052454136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32307858871415368302757835 48461788307123052454136753)
              ·
                refine ⟨36346341230342289340602565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48461788307123052454136753 36346341230342289340602565)
                ·
                  refine ⟨6814938980689179251362981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36346341230342289340602565 6814938980689179251362981)
                  ·
                    refine ⟨1277801058879221109630559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6814938980689179251362981 1277801058879221109630559)
                    ·
                      rfl

theorem cell23_7465526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7465526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465526 prefixEnd_7465526 := by exact prefixLift 7465526
  have htrace : WordTrace (prefixWord ++ tailWord_7465526) baseStart_7465526 baseEnd_7465526 := by
    simpa [prefixWord, tailWord_7465526, baseEnd_7465526] using wordTrace_append hprefix tailTrace_7465526
  have hstable : (prefixWord ++ tailWord_7465526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465526).length < 2 ^ (prefixWord ++ tailWord_7465526).sum := by decide
  have hdescent : baseEnd_7465526 < baseStart_7465526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465623 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_7465623 : Nat := 118140960795 + 7465623 * 2 ^ 59
def prefixEnd_7465623 : Nat := 4983230072969 + 3 ^ 40 * 7465623 * 2
def baseEnd_7465623 : Nat := 3833452984261149449378731

theorem tailTrace_7465623 : CollatzResearch.WordTrace tailWord_7465623 prefixEnd_7465623 3833452984261149449378731 := by
  unfold tailWord_7465623
  simp only [CollatzResearch.WordTrace]
  refine ⟨272293640632330372743433523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181529093754886915162289015 272293640632330372743433523)
  ·
    refine ⟨408440460948495559115150285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272293640632330372743433523 408440460948495559115150285)
    ·
      refine ⟨153165172855685834668181357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408440460948495559115150285 153165172855685834668181357)
      ·
        refine ⟨57436939820882188000568009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153165172855685834668181357 57436939820882188000568009)
        ·
          refine ⟨43077704865661641000426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57436939820882188000568009 43077704865661641000426007)
          ·
            refine ⟨64616557298492461500639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43077704865661641000426007 64616557298492461500639011)
            ·
              refine ⟨96924835947738692250958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64616557298492461500639011 96924835947738692250958517)
              ·
                refine ⟨9086703370100502398527361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96924835947738692250958517 9086703370100502398527361)
                ·
                  refine ⟨6815027527575376798895521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9086703370100502398527361 6815027527575376798895521)
                  ·
                    refine ⟨5111270645681532599171641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6815027527575376798895521 5111270645681532599171641)
                    ·
                      refine ⟨3833452984261149449378731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111270645681532599171641 3833452984261149449378731)
                      ·
                        rfl

theorem cell23_7465623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_7465623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465623 prefixEnd_7465623 := by exact prefixLift 7465623
  have htrace : WordTrace (prefixWord ++ tailWord_7465623) baseStart_7465623 baseEnd_7465623 := by
    simpa [prefixWord, tailWord_7465623, baseEnd_7465623] using wordTrace_append hprefix tailTrace_7465623
  have hstable : (prefixWord ++ tailWord_7465623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465623).length < 2 ^ (prefixWord ++ tailWord_7465623).sum := by decide
  have hdescent : baseEnd_7465623 < baseStart_7465623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465719 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 6]
def baseStart_7465719 : Nat := 118140960795 + 7465719 * 2 ^ 59
def prefixEnd_7465719 : Nat := 4983230072969 + 3 ^ 40 * 7465719 * 2
def baseEnd_7465719 : Nat := 425944697600442341530921

theorem tailTrace_7465719 : CollatzResearch.WordTrace tailWord_7465719 prefixEnd_7465719 425944697600442341530921 := by
  unfold tailWord_7465719
  simp only [CollatzResearch.WordTrace]
  refine ⟨272297142039982581138928211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181531428026655054092618807 272297142039982581138928211)
  ·
    refine ⟨408445713059973871708392317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272297142039982581138928211 408445713059973871708392317)
    ·
      refine ⟨153167142397490201890647119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408445713059973871708392317 153167142397490201890647119)
      ·
        refine ⟨229750713596235302835970679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153167142397490201890647119 229750713596235302835970679)
        ·
          refine ⟨344626070394352954253956019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229750713596235302835970679 344626070394352954253956019)
          ·
            refine ⟨516939105591529431380934029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344626070394352954253956019 516939105591529431380934029)
            ·
              refine ⟨193852164596823536767850261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516939105591529431380934029 193852164596823536767850261)
              ·
                refine ⟨9086820215476103285992981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193852164596823536767850261 9086820215476103285992981)
                ·
                  refine ⟨425944697600442341530921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9086820215476103285992981 425944697600442341530921)
                  ·
                    rfl

theorem cell23_7465719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 6].length) (baseStart_7465719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465719 prefixEnd_7465719 := by exact prefixLift 7465719
  have htrace : WordTrace (prefixWord ++ tailWord_7465719) baseStart_7465719 baseEnd_7465719 := by
    simpa [prefixWord, tailWord_7465719, baseEnd_7465719] using wordTrace_append hprefix tailTrace_7465719
  have hstable : (prefixWord ++ tailWord_7465719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465719).length < 2 ^ (prefixWord ++ tailWord_7465719).sum := by decide
  have hdescent : baseEnd_7465719 < baseStart_7465719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465736 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 6]
def baseStart_7465736 : Nat := 118140960795 + 7465736 * 2 ^ 59
def prefixEnd_7465736 : Nat := 4983230072969 + 3 ^ 40 * 7465736 * 2
def baseEnd_7465736 : Nat := 425945667508345278585079

theorem tailTrace_7465736 : CollatzResearch.WordTrace tailWord_7465736 prefixEnd_7465736 425945667508345278585079 := by
  unfold tailWord_7465736
  simp only [CollatzResearch.WordTrace]
  refine ⟨136148881040460496521148531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181531841387280662028198041 136148881040460496521148531)
  ·
    refine ⟨204223321560690744781722797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136148881040460496521148531 204223321560690744781722797)
    ·
      refine ⟨76583745585259029293146049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204223321560690744781722797 76583745585259029293146049)
      ·
        refine ⟨57437809188944271969859537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76583745585259029293146049 57437809188944271969859537)
        ·
          refine ⟨43078356891708203977394653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57437809188944271969859537 43078356891708203977394653)
          ·
            refine ⟨16154383834390576491522995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43078356891708203977394653 16154383834390576491522995)
            ·
              refine ⟨24231575751585864737284493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16154383834390576491522995 24231575751585864737284493)
              ·
                refine ⟨9086840906844699276481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24231575751585864737284493 9086840906844699276481685)
                ·
                  refine ⟨425945667508345278585079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9086840906844699276481685 425945667508345278585079)
                  ·
                    rfl

theorem cell23_7465736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_7465736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465736 prefixEnd_7465736 := by exact prefixLift 7465736
  have htrace : WordTrace (prefixWord ++ tailWord_7465736) baseStart_7465736 baseEnd_7465736 := by
    simpa [prefixWord, tailWord_7465736, baseEnd_7465736] using wordTrace_append hprefix tailTrace_7465736
  have hstable : (prefixWord ++ tailWord_7465736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465736).length < 2 ^ (prefixWord ++ tailWord_7465736).sum := by decide
  have hdescent : baseEnd_7465736 < baseStart_7465736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465770 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_7465770 : Nat := 118140960795 + 7465770 * 2 ^ 59
def prefixEnd_7465770 : Nat := 4983230072969 + 3 ^ 40 * 7465770 * 2
def baseEnd_7465770 : Nat := 425947607324151152693395

theorem tailTrace_7465770 : CollatzResearch.WordTrace tailWord_7465770 prefixEnd_7465770 425947607324151152693395 := by
  unfold tailWord_7465770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074750540699454212258691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181532668108531877899356509 68074750540699454212258691)
  ·
    refine ⟨102112125811049181318388037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68074750540699454212258691 102112125811049181318388037)
    ·
      refine ⟨19146023589571721497197757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102112125811049181318388037 19146023589571721497197757)
      ·
        refine ⟨7179758846089395561449159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19146023589571721497197757 7179758846089395561449159)
        ·
          refine ⟨10769638269134093342173739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179758846089395561449159 10769638269134093342173739)
          ·
            refine ⟨16154457403701140013260609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769638269134093342173739 16154457403701140013260609)
            ·
              refine ⟨12115843052775855009945457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16154457403701140013260609 12115843052775855009945457)
              ·
                refine ⟨9086882289581891257459093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12115843052775855009945457 9086882289581891257459093)
                ·
                  refine ⟨425947607324151152693395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9086882289581891257459093 425947607324151152693395)
                  ·
                    rfl

theorem cell23_7465770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_7465770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465770 prefixEnd_7465770 := by exact prefixLift 7465770
  have htrace : WordTrace (prefixWord ++ tailWord_7465770) baseStart_7465770 baseEnd_7465770 := by
    simpa [prefixWord, tailWord_7465770, baseEnd_7465770] using wordTrace_append hprefix tailTrace_7465770
  have hstable : (prefixWord ++ tailWord_7465770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465770).length < 2 ^ (prefixWord ++ tailWord_7465770).sum := by decide
  have hdescent : baseEnd_7465770 < baseStart_7465770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465774 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7465774 : Nat := 118140960795 + 7465774 * 2 ^ 59
def prefixEnd_7465774 : Nat := 4983230072969 + 3 ^ 40 * 7465774 * 2
def baseEnd_7465774 : Nat := 1277843506613326119530179

theorem tailTrace_7465774 : CollatzResearch.WordTrace tailWord_7465774 prefixEnd_7465774 1277843506613326119530179 := by
  unfold tailWord_7465774
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037393506847915691522547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181532765369855550354786917 34037393506847915691522547)
  ·
    refine ⟨51056090260271873537283821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34037393506847915691522547 51056090260271873537283821)
    ·
      refine ⟨19146033847601952576481433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51056090260271873537283821 19146033847601952576481433)
      ·
        refine ⟨14359525385701464432361075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19146033847601952576481433 14359525385701464432361075)
        ·
          refine ⟨21539288078552196648541613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359525385701464432361075 21539288078552196648541613)
          ·
            refine ⟨8077233029457073743203105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21539288078552196648541613 8077233029457073743203105)
            ·
              refine ⟨6057924772092805307402329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077233029457073743203105 6057924772092805307402329)
              ·
                refine ⟨4543443579069603980551747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6057924772092805307402329 4543443579069603980551747)
                ·
                  refine ⟨6815165368604405970827621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543443579069603980551747 6815165368604405970827621)
                  ·
                    refine ⟨1277843506613326119530179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815165368604405970827621 1277843506613326119530179)
                    ·
                      rfl

theorem cell23_7465774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7465774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465774 prefixEnd_7465774 := by exact prefixLift 7465774
  have htrace : WordTrace (prefixWord ++ tailWord_7465774) baseStart_7465774 baseEnd_7465774 := by
    simpa [prefixWord, tailWord_7465774, baseEnd_7465774] using wordTrace_append hprefix tailTrace_7465774
  have hstable : (prefixWord ++ tailWord_7465774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465774).length < 2 ^ (prefixWord ++ tailWord_7465774).sum := by decide
  have hdescent : baseEnd_7465774 < baseStart_7465774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465820 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7465820 : Nat := 118140960795 + 7465820 * 2 ^ 59
def prefixEnd_7465820 : Nat := 4983230072969 + 3 ^ 40 * 7465820 * 2
def baseEnd_7465820 : Nat := 3833554139950085178615325

theorem tailTrace_7465820 : CollatzResearch.WordTrace tailWord_7465820 prefixEnd_7465820 3833554139950085178615325 := by
  unfold tailWord_7465820
  simp only [CollatzResearch.WordTrace]
  refine ⟨136150412906308337694177457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181533883875077783592236609 136150412906308337694177457)
  ·
    refine ⟨102112809679731253270633093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136150412906308337694177457 102112809679731253270633093)
    ·
      refine ⟨19146151814949609988243705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102112809679731253270633093 19146151814949609988243705)
      ·
        refine ⟨14359613861212207491182779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19146151814949609988243705 14359613861212207491182779)
        ·
          refine ⟨21539420791818311236774169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359613861212207491182779 21539420791818311236774169)
          ·
            refine ⟨16154565593863733427580627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21539420791818311236774169 16154565593863733427580627)
            ·
              refine ⟨24231848390795600141370941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16154565593863733427580627 24231848390795600141370941)
              ·
                refine ⟨9086943146548350053014103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24231848390795600141370941 9086943146548350053014103)
                ·
                  refine ⟨13630414719822525079521155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9086943146548350053014103 13630414719822525079521155)
                  ·
                    refine ⟨20445622079733787619281733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13630414719822525079521155 20445622079733787619281733)
                    ·
                      refine ⟨3833554139950085178615325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20445622079733787619281733 3833554139950085178615325)
                      ·
                        rfl

theorem cell23_7465820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7465820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465820 prefixEnd_7465820 := by exact prefixLift 7465820
  have htrace : WordTrace (prefixWord ++ tailWord_7465820) baseStart_7465820 baseEnd_7465820 := by
    simpa [prefixWord, tailWord_7465820, baseEnd_7465820] using wordTrace_append hprefix tailTrace_7465820
  have hstable : (prefixWord ++ tailWord_7465820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465820).length < 2 ^ (prefixWord ++ tailWord_7465820).sum := by decide
  have hdescent : baseEnd_7465820 < baseStart_7465820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465823 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_7465823 : Nat := 118140960795 + 7465823 * 2 ^ 59
def prefixEnd_7465823 : Nat := 4983230072969 + 3 ^ 40 * 7465823 * 2
def baseEnd_7465823 : Nat := 3833555680392048666877811

theorem tailTrace_7465823 : CollatzResearch.WordTrace tailWord_7465823 prefixEnd_7465823 3833555680392048666877811 := by
  unfold tailWord_7465823
  simp only [CollatzResearch.WordTrace]
  refine ⟨272300935231605806900714123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181533956821070537933809415 272300935231605806900714123)
  ·
    refine ⟨408451402847408710351071185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272300935231605806900714123 408451402847408710351071185)
    ·
      refine ⟨306338552135556532763303389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408451402847408710351071185 306338552135556532763303389)
      ·
        refine ⟨114876957050833699786238771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306338552135556532763303389 114876957050833699786238771)
        ·
          refine ⟨172315435576250549679358157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114876957050833699786238771 172315435576250549679358157)
          ·
            refine ⟨64618288341093956129759309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172315435576250549679358157 64618288341093956129759309)
            ·
              refine ⟨24231858127910233548659741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64618288341093956129759309 24231858127910233548659741)
              ·
                refine ⟨9086946797966337580747403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24231858127910233548659741 9086946797966337580747403)
                ·
                  refine ⟨13630420196949506371121105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9086946797966337580747403 13630420196949506371121105)
                  ·
                    refine ⟨10222815147712129778340829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13630420196949506371121105 10222815147712129778340829)
                    ·
                      refine ⟨3833555680392048666877811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10222815147712129778340829 3833555680392048666877811)
                      ·
                        rfl

theorem cell23_7465823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_7465823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465823 prefixEnd_7465823 := by exact prefixLift 7465823
  have htrace : WordTrace (prefixWord ++ tailWord_7465823) baseStart_7465823 baseEnd_7465823 := by
    simpa [prefixWord, tailWord_7465823, baseEnd_7465823] using wordTrace_append hprefix tailTrace_7465823
  have hstable : (prefixWord ++ tailWord_7465823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465823).length < 2 ^ (prefixWord ++ tailWord_7465823).sum := by decide
  have hdescent : baseEnd_7465823 < baseStart_7465823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465839 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 9]
def baseStart_7465839 : Nat := 118140960795 + 7465839 * 2 ^ 59
def prefixEnd_7465839 : Nat := 4983230072969 + 3 ^ 40 * 7465839 * 2
def baseEnd_7465839 : Nat := 1277854632027506868092579

theorem tailTrace_7465839 : CollatzResearch.WordTrace tailWord_7465839 prefixEnd_7465839 1277854632027506868092579 := by
  unfold tailWord_7465839
  simp only [CollatzResearch.WordTrace]
  refine ⟨272301518799547841633296571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181534345866365227755531047 272301518799547841633296571)
  ·
    refine ⟨408452278199321762449944857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272301518799547841633296571 408452278199321762449944857)
    ·
      refine ⟨306339208649491321837458643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408452278199321762449944857 306339208649491321837458643)
      ·
        refine ⟨459508812974236982756187965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306339208649491321837458643 459508812974236982756187965)
        ·
          refine ⟨172315804865338868533570487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459508812974236982756187965 172315804865338868533570487)
          ·
            refine ⟨258473707298008302800355731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172315804865338868533570487 258473707298008302800355731)
            ·
              refine ⟨387710560947012454200533597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258473707298008302800355731 387710560947012454200533597)
              ·
                refine ⟨145391460355129670325200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387710560947012454200533597 145391460355129670325200099)
                ·
                  refine ⟨218087190532694505487800149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145391460355129670325200099 218087190532694505487800149)
                  ·
                    refine ⟨1277854632027506868092579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218087190532694505487800149 1277854632027506868092579)
                    ·
                      rfl

theorem cell23_7465839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_7465839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465839 prefixEnd_7465839 := by exact prefixLift 7465839
  have htrace : WordTrace (prefixWord ++ tailWord_7465839) baseStart_7465839 baseEnd_7465839 := by
    simpa [prefixWord, tailWord_7465839, baseEnd_7465839] using wordTrace_append hprefix tailTrace_7465839
  have hstable : (prefixWord ++ tailWord_7465839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465839).length < 2 ^ (prefixWord ++ tailWord_7465839).sum := by decide
  have hdescent : baseEnd_7465839 < baseStart_7465839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465853 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_7465853 : Nat := 118140960795 + 7465853 * 2 ^ 59
def prefixEnd_7465853 : Nat := 4983230072969 + 3 ^ 40 * 7465853 * 2
def baseEnd_7465853 : Nat := 3833571084811683549502673

theorem tailTrace_7465853 : CollatzResearch.WordTrace tailWord_7465853 prefixEnd_7465853 3833571084811683549502673 := by
  unfold tailWord_7465853
  simp only [CollatzResearch.WordTrace]
  refine ⟨272302029421497122024306213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181534686280998081349537475 272302029421497122024306213)
  ·
    refine ⟨51056630516530710379557415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272302029421497122024306213 51056630516530710379557415)
    ·
      refine ⟨76584945774796065569336123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51056630516530710379557415 76584945774796065569336123)
      ·
        refine ⟨114877418662194098354004185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76584945774796065569336123 114877418662194098354004185)
        ·
          refine ⟨86158063996645573765503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114877418662194098354004185 86158063996645573765503139)
          ·
            refine ⟨129237095994968360648254709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86158063996645573765503139 129237095994968360648254709)
            ·
              refine ⟨12115977749528283810773879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129237095994968360648254709 12115977749528283810773879)
              ·
                refine ⟨18173966624292425716160819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12115977749528283810773879 18173966624292425716160819)
                ·
                  refine ⟨27260949936438638574241229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18173966624292425716160819 27260949936438638574241229)
                  ·
                    refine ⟨10222856226164489465340461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27260949936438638574241229 10222856226164489465340461)
                    ·
                      refine ⟨3833571084811683549502673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10222856226164489465340461 3833571084811683549502673)
                      ·
                        rfl

theorem cell23_7465853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_7465853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465853 prefixEnd_7465853 := by exact prefixLift 7465853
  have htrace : WordTrace (prefixWord ++ tailWord_7465853) baseStart_7465853 baseEnd_7465853 := by
    simpa [prefixWord, tailWord_7465853, baseEnd_7465853] using wordTrace_append hprefix tailTrace_7465853
  have hstable : (prefixWord ++ tailWord_7465853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465853).length < 2 ^ (prefixWord ++ tailWord_7465853).sum := by decide
  have hdescent : baseEnd_7465853 < baseStart_7465853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465956 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_7465956 : Nat := 118140960795 + 7465956 * 2 ^ 59
def prefixEnd_7465956 : Nat := 4983230072969 + 3 ^ 40 * 7465956 * 2
def baseEnd_7465956 : Nat := 3833623973319096646514699

theorem tailTrace_7465956 : CollatzResearch.WordTrace tailWord_7465956 prefixEnd_7465956 3833623973319096646514699 := by
  unfold tailWord_7465956
  simp only [CollatzResearch.WordTrace]
  refine ⟨136152893070061985307652861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181537190760082647076870481 136152893070061985307652861)
  ·
    refine ⟨51057334901273244490369823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136152893070061985307652861 51057334901273244490369823)
    ·
      refine ⟨76586002351909866735554735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51057334901273244490369823 76586002351909866735554735)
      ·
        refine ⟨114879003527864800103332103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76586002351909866735554735 114879003527864800103332103)
        ·
          refine ⟨172318505291797200154998155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114879003527864800103332103 172318505291797200154998155)
          ·
            refine ⟨258477757937695800232497233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172318505291797200154998155 258477757937695800232497233)
            ·
              refine ⟨193858318453271850174372925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258477757937695800232497233 193858318453271850174372925)
              ·
                refine ⟨72696869419976943815389847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193858318453271850174372925 72696869419976943815389847)
                ·
                  refine ⟨109045304129965415723084771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72696869419976943815389847 109045304129965415723084771)
                  ·
                    refine ⟨163567956194948123584627157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109045304129965415723084771 163567956194948123584627157)
                    ·
                      refine ⟨3833623973319096646514699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163567956194948123584627157 3833623973319096646514699)
                      ·
                        rfl

theorem cell23_7465956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_7465956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465956 prefixEnd_7465956 := by exact prefixLift 7465956
  have htrace : WordTrace (prefixWord ++ tailWord_7465956) baseStart_7465956 baseEnd_7465956 := by
    simpa [prefixWord, tailWord_7465956, baseEnd_7465956] using wordTrace_append hprefix tailTrace_7465956
  have hstable : (prefixWord ++ tailWord_7465956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465956).length < 2 ^ (prefixWord ++ tailWord_7465956).sum := by decide
  have hdescent : baseEnd_7465956 < baseStart_7465956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7465980 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_7465980 : Nat := 118140960795 + 7465980 * 2 ^ 59
def prefixEnd_7465980 : Nat := 4983230072969 + 3 ^ 40 * 7465980 * 2
def baseEnd_7465980 : Nat := 1277878765618268184204863

theorem tailTrace_7465980 : CollatzResearch.WordTrace tailWord_7465980 prefixEnd_7465980 1277878765618268184204863 := by
  unfold tailWord_7465980
  simp only [CollatzResearch.WordTrace]
  refine ⟨136153330746018511357089697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181537774328024681809452929 136153330746018511357089697)
  ·
    refine ⟨102114998059513883517817273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136153330746018511357089697 102114998059513883517817273)
    ·
      refine ⟨76586248544635412638362955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102114998059513883517817273 76586248544635412638362955)
      ·
        refine ⟨114879372816953118957544433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76586248544635412638362955 114879372816953118957544433)
        ·
          refine ⟨86159529612714839218158325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114879372816953118957544433 86159529612714839218158325)
          ·
            refine ⟨8077455901192016176702343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86159529612714839218158325 8077455901192016176702343)
            ·
              refine ⟨12116183851788024265053515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077455901192016176702343 12116183851788024265053515)
              ·
                refine ⟨18174275777682036397580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12116183851788024265053515 18174275777682036397580273)
                ·
                  refine ⟨13630706833261527298185205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18174275777682036397580273 13630706833261527298185205)
                  ·
                    refine ⟨1277878765618268184204863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13630706833261527298185205 1277878765618268184204863)
                    ·
                      rfl

theorem cell23_7465980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_7465980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7465980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7465980 prefixEnd_7465980 := by exact prefixLift 7465980
  have htrace : WordTrace (prefixWord ++ tailWord_7465980) baseStart_7465980 baseEnd_7465980 := by
    simpa [prefixWord, tailWord_7465980, baseEnd_7465980] using wordTrace_append hprefix tailTrace_7465980
  have hstable : (prefixWord ++ tailWord_7465980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7465980).length < 2 ^ (prefixWord ++ tailWord_7465980).sum := by decide
  have hdescent : baseEnd_7465980 < baseStart_7465980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7465980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466003 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3]
def baseStart_7466003 : Nat := 118140960795 + 7466003 * 2 ^ 59
def prefixEnd_7466003 : Nat := 4983230072969 + 3 ^ 40 * 7466003 * 2
def baseEnd_7466003 : Nat := 3833648106909857962626983

theorem tailTrace_7466003 : CollatzResearch.WordTrace tailWord_7466003 prefixEnd_7466003 3833648106909857962626983 := by
  unfold tailWord_7466003
  simp only [CollatzResearch.WordTrace]
  refine ⟨272307500370953697642266663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181538333580635798428177775 272307500370953697642266663)
  ·
    refine ⟨408461250556430546463399995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272307500370953697642266663 408461250556430546463399995)
    ·
      refine ⟨612691875834645819695099993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408461250556430546463399995 612691875834645819695099993)
      ·
        refine ⟨459518906875984364771324995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612691875834645819695099993 459518906875984364771324995)
        ·
          refine ⟨689278360313976547156987493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459518906875984364771324995 689278360313976547156987493)
          ·
            refine ⟨129239692558870602591935155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689278360313976547156987493 129239692558870602591935155)
            ·
              refine ⟨193859538838305903887902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129239692558870602591935155 193859538838305903887902733)
              ·
                refine ⟨72697327064364713957963525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193859538838305903887902733 72697327064364713957963525)
                ·
                  refine ⟨13630748824568383867118161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72697327064364713957963525 13630748824568383867118161)
                  ·
                    refine ⟨10223061618426287900338621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13630748824568383867118161 10223061618426287900338621)
                    ·
                      refine ⟨3833648106909857962626983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223061618426287900338621 3833648106909857962626983)
                      ·
                        rfl

theorem cell23_7466003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_7466003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466003 prefixEnd_7466003 := by exact prefixLift 7466003
  have htrace : WordTrace (prefixWord ++ tailWord_7466003) baseStart_7466003 baseEnd_7466003 := by
    simpa [prefixWord, tailWord_7466003, baseEnd_7466003] using wordTrace_append hprefix tailTrace_7466003
  have hstable : (prefixWord ++ tailWord_7466003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466003).length < 2 ^ (prefixWord ++ tailWord_7466003).sum := by decide
  have hdescent : baseEnd_7466003 < baseStart_7466003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466010 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_7466010 : Nat := 118140960795 + 7466010 * 2 ^ 59
def prefixEnd_7466010 : Nat := 4983230072969 + 3 ^ 40 * 7466010 * 2
def baseEnd_7466010 : Nat := 1277883900424813145079817

theorem tailTrace_7466010 : CollatzResearch.WordTrace tailWord_7466010 prefixEnd_7466010 1277883900424813145079817 := by
  unfold tailWord_7466010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68076938920482084459442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181538503787952225225180989 68076938920482084459442871)
  ·
    refine ⟨102115408380723126689164307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68076938920482084459442871 102115408380723126689164307)
    ·
      refine ⟨153173112571084690033746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102115408380723126689164307 153173112571084690033746461)
      ·
        refine ⟨57439917214156758762654923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153173112571084690033746461 57439917214156758762654923)
        ·
          refine ⟨86159875821235138143982385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57439917214156758762654923 86159875821235138143982385)
          ·
            refine ⟨64619906865926353607986789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86159875821235138143982385 64619906865926353607986789)
            ·
              refine ⟨12116232537361191301497523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64619906865926353607986789 12116232537361191301497523)
              ·
                refine ⟨18174348806041786952246285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12116232537361191301497523 18174348806041786952246285)
                ·
                  refine ⟨6815380802265670107092357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18174348806041786952246285 6815380802265670107092357)
                  ·
                    refine ⟨1277883900424813145079817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815380802265670107092357 1277883900424813145079817)
                    ·
                      rfl

theorem cell23_7466010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_7466010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466010 prefixEnd_7466010 := by exact prefixLift 7466010
  have htrace : WordTrace (prefixWord ++ tailWord_7466010) baseStart_7466010 baseEnd_7466010 := by
    simpa [prefixWord, tailWord_7466010, baseEnd_7466010] using wordTrace_append hprefix tailTrace_7466010
  have hstable : (prefixWord ++ tailWord_7466010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466010).length < 2 ^ (prefixWord ++ tailWord_7466010).sum := by decide
  have hdescent : baseEnd_7466010 < baseStart_7466010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466020 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7466020 : Nat := 118140960795 + 7466020 * 2 ^ 59
def prefixEnd_7466020 : Nat := 4983230072969 + 3 ^ 40 * 7466020 * 2
def baseEnd_7466020 : Nat := 3833656836080984396114405

theorem tailTrace_7466020 : CollatzResearch.WordTrace tailWord_7466020 prefixEnd_7466020 3833656836080984396114405 := by
  unfold tailWord_7466020
  simp only [CollatzResearch.WordTrace]
  refine ⟨136154060205946054772817757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181538746941261406363757009 136154060205946054772817757)
  ·
    refine ⟨51057772577229770539806659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136154060205946054772817757 51057772577229770539806659)
    ·
      refine ⟨76586658865844655809709989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51057772577229770539806659 76586658865844655809709989)
      ·
        refine ⟨14359998537345872964320623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76586658865844655809709989 14359998537345872964320623)
        ·
          refine ⟨21539997806018809446480935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14359998537345872964320623 21539997806018809446480935)
          ·
            refine ⟨32309996709028214169721403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21539997806018809446480935 32309996709028214169721403)
            ·
              refine ⟨48464995063542321254582105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32309996709028214169721403 48464995063542321254582105)
              ·
                refine ⟨36348746297656740940936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48464995063542321254582105 36348746297656740940936579)
                ·
                  refine ⟨54523119446485111411404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36348746297656740940936579 54523119446485111411404869)
                  ·
                    refine ⟨10223084896215958389638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54523119446485111411404869 10223084896215958389638413)
                    ·
                      refine ⟨3833656836080984396114405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223084896215958389638413 3833656836080984396114405)
                      ·
                        rfl

theorem cell23_7466020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7466020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466020 prefixEnd_7466020 := by exact prefixLift 7466020
  have htrace : WordTrace (prefixWord ++ tailWord_7466020) baseStart_7466020 baseEnd_7466020 := by
    simpa [prefixWord, tailWord_7466020, baseEnd_7466020] using wordTrace_append hprefix tailTrace_7466020
  have hstable : (prefixWord ++ tailWord_7466020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466020).length < 2 ^ (prefixWord ++ tailWord_7466020).sum := by decide
  have hdescent : baseEnd_7466020 < baseStart_7466020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466033 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_7466033 : Nat := 118140960795 + 7466033 * 2 ^ 59
def prefixEnd_7466033 : Nat := 4983230072969 + 3 ^ 40 * 7466033 * 2
def baseEnd_7466033 : Nat := 3833663511329492845251845

theorem tailTrace_7466033 : CollatzResearch.WordTrace tailWord_7466033 prefixEnd_7466033 3833663511329492845251845 := by
  unfold tailWord_7466033
  simp only [CollatzResearch.WordTrace]
  refine ⟨272308594560845012765858753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181539063040563341843905835 272308594560845012765858753)
  ·
    refine ⟨204231445920633759574394065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272308594560845012765858753 204231445920633759574394065)
    ·
      refine ⟨153173584440475319680795549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204231445920633759574394065 153173584440475319680795549)
      ·
        refine ⟨57440094165178244880298331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153173584440475319680795549 57440094165178244880298331)
        ·
          refine ⟨86160141247767367320447497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57440094165178244880298331 86160141247767367320447497)
          ·
            refine ⟨64620105935825525490335623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86160141247767367320447497 64620105935825525490335623)
            ·
              refine ⟨96930158903738288235503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64620105935825525490335623 96930158903738288235503435)
              ·
                refine ⟨145395238355607432353255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96930158903738288235503435 145395238355607432353255153)
                ·
                  refine ⟨109046428766705574264941365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145395238355607432353255153 109046428766705574264941365)
                  ·
                    refine ⟨10223102696878647587338253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109046428766705574264941365 10223102696878647587338253)
                    ·
                      refine ⟨3833663511329492845251845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223102696878647587338253 3833663511329492845251845)
                      ·
                        rfl

theorem cell23_7466033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_7466033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466033 prefixEnd_7466033 := by exact prefixLift 7466033
  have htrace : WordTrace (prefixWord ++ tailWord_7466033) baseStart_7466033 baseEnd_7466033 := by
    simpa [prefixWord, tailWord_7466033, baseEnd_7466033] using wordTrace_append hprefix tailTrace_7466033
  have hstable : (prefixWord ++ tailWord_7466033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466033).length < 2 ^ (prefixWord ++ tailWord_7466033).sum := by decide
  have hdescent : baseEnd_7466033 < baseStart_7466033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466044 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_7466044 : Nat := 118140960795 + 7466044 * 2 ^ 59
def prefixEnd_7466044 : Nat := 4983230072969 + 3 ^ 40 * 7466044 * 2
def baseEnd_7466044 : Nat := 1277889719872230767404765

theorem tailTrace_7466044 : CollatzResearch.WordTrace tailWord_7466044 prefixEnd_7466044 1277889719872230767404765 := by
  unfold tailWord_7466044
  simp only [CollatzResearch.WordTrace]
  refine ⟨136154497881902580822254593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181539330509203441096339457 136154497881902580822254593)
  ·
    refine ⟨102115873411426935616690945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136154497881902580822254593 102115873411426935616690945)
    ·
      refine ⟨76586905058570201712518209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102115873411426935616690945 76586905058570201712518209)
      ·
        refine ⟨57440178793927651284388657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76586905058570201712518209 57440178793927651284388657)
        ·
          refine ⟨43080134095445738463291493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57440178793927651284388657 43080134095445738463291493)
          ·
            refine ⟨8077525142896075961867155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43080134095445738463291493 8077525142896075961867155)
            ·
              refine ⟨12116287714344113942800733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077525142896075961867155 12116287714344113942800733)
              ·
                refine ⟨4543607892879042728550275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12116287714344113942800733 4543607892879042728550275)
                ·
                  refine ⟨6815411839318564092825413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543607892879042728550275 6815411839318564092825413)
                  ·
                    refine ⟨1277889719872230767404765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815411839318564092825413 1277889719872230767404765)
                    ·
                      rfl

theorem cell23_7466044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_7466044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466044 prefixEnd_7466044 := by exact prefixLift 7466044
  have htrace : WordTrace (prefixWord ++ tailWord_7466044) baseStart_7466044 baseEnd_7466044 := by
    simpa [prefixWord, tailWord_7466044, baseEnd_7466044] using wordTrace_append hprefix tailTrace_7466044
  have hstable : (prefixWord ++ tailWord_7466044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466044).length < 2 ^ (prefixWord ++ tailWord_7466044).sum := by decide
  have hdescent : baseEnd_7466044 < baseStart_7466044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466054 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7466054 : Nat := 118140960795 + 7466054 * 2 ^ 59
def prefixEnd_7466054 : Nat := 4983230072969 + 3 ^ 40 * 7466054 * 2
def baseEnd_7466054 : Nat := 3833674294423237263089249

theorem tailTrace_7466054 : CollatzResearch.WordTrace tailWord_7466054 prefixEnd_7466054 3833674294423237263089249 := by
  unfold tailWord_7466054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509667515430279167261663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181539573662512622234915477 8509667515430279167261663)
  ·
    refine ⟨12764501273145418750892495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8509667515430279167261663 12764501273145418750892495)
    ·
      refine ⟨19146751909718128126338743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12764501273145418750892495 19146751909718128126338743)
      ·
        refine ⟨28720127864577192189508115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19146751909718128126338743 28720127864577192189508115)
        ·
          refine ⟨43080191796865788284262173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28720127864577192189508115 43080191796865788284262173)
          ·
            refine ⟨16155071923824670606598315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43080191796865788284262173 16155071923824670606598315)
            ·
              refine ⟨24232607885737005909897473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155071923824670606598315 24232607885737005909897473)
              ·
                refine ⟨18174455914302754432423105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24232607885737005909897473 18174455914302754432423105)
                ·
                  refine ⟨13630841935727065824317329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18174455914302754432423105 13630841935727065824317329)
                  ·
                    refine ⟨10223131451795299368237997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13630841935727065824317329 10223131451795299368237997)
                    ·
                      refine ⟨3833674294423237263089249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223131451795299368237997 3833674294423237263089249)
                      ·
                        rfl

theorem cell23_7466054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7466054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466054 prefixEnd_7466054 := by exact prefixLift 7466054
  have htrace : WordTrace (prefixWord ++ tailWord_7466054) baseStart_7466054 baseEnd_7466054 := by
    simpa [prefixWord, tailWord_7466054, baseEnd_7466054] using wordTrace_append hprefix tailTrace_7466054
  have hstable : (prefixWord ++ tailWord_7466054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466054).length < 2 ^ (prefixWord ++ tailWord_7466054).sum := by decide
  have hdescent : baseEnd_7466054 < baseStart_7466054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466061 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7466061 : Nat := 118140960795 + 7466061 * 2 ^ 59
def prefixEnd_7466061 : Nat := 4983230072969 + 3 ^ 40 * 7466061 * 2
def baseEnd_7466061 : Nat := 1277892629595939578567239

theorem tailTrace_7466061 : CollatzResearch.WordTrace tailWord_7466061 prefixEnd_7466061 1277892629595939578567239 := by
  unfold tailWord_7466061
  simp only [CollatzResearch.WordTrace]
  refine ⟨272309615804743573547878037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181539743869829049031918691 272309615804743573547878037)
  ·
    refine ⟨12764513240847355010056783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 272309615804743573547878037 12764513240847355010056783)
    ·
      refine ⟨19146769861271032515085175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12764513240847355010056783 19146769861271032515085175)
      ·
        refine ⟨28720154791906548772627763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19146769861271032515085175 28720154791906548772627763)
        ·
          refine ⟨43080232187859823158941645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28720154791906548772627763 43080232187859823158941645)
          ·
            refine ⟨16155087070447433684603117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43080232187859823158941645 16155087070447433684603117)
            ·
              refine ⟨6058157651417787631726169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16155087070447433684603117 6058157651417787631726169)
              ·
                refine ⟨4543618238563340723794627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6058157651417787631726169 4543618238563340723794627)
                ·
                  refine ⟨6815427357845011085691941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543618238563340723794627 6815427357845011085691941)
                  ·
                    refine ⟨1277892629595939578567239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815427357845011085691941 1277892629595939578567239)
                    ·
                      rfl

theorem cell23_7466061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7466061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466061 prefixEnd_7466061 := by exact prefixLift 7466061
  have htrace : WordTrace (prefixWord ++ tailWord_7466061) baseStart_7466061 baseEnd_7466061 := by
    simpa [prefixWord, tailWord_7466061, baseEnd_7466061] using wordTrace_append hprefix tailTrace_7466061
  have hstable : (prefixWord ++ tailWord_7466061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466061).length < 2 ^ (prefixWord ++ tailWord_7466061).sum := by decide
  have hdescent : baseEnd_7466061 < baseStart_7466061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466083 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 6]
def baseStart_7466083 : Nat := 118140960795 + 7466083 * 2 ^ 59
def prefixEnd_7466083 : Nat := 4983230072969 + 3 ^ 40 * 7466083 * 2
def baseEnd_7466083 : Nat := 1277896395120739216542205

theorem tailTrace_7466083 : CollatzResearch.WordTrace tailWord_7466083 prefixEnd_7466083 1277896395120739216542205 := by
  unfold tailWord_7466083
  simp only [CollatzResearch.WordTrace]
  refine ⟨272310418210663871305178903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181540278807109247536785935 272310418210663871305178903)
  ·
    refine ⟨408465627315995806957768355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272310418210663871305178903 408465627315995806957768355)
    ·
      refine ⟨612698440973993710436652533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408465627315995806957768355 612698440973993710436652533)
      ·
        refine ⟨57440478841311910353436175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612698440973993710436652533 57440478841311910353436175)
        ·
          refine ⟨86160718261967865530154263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57440478841311910353436175 86160718261967865530154263)
          ·
            refine ⟨129241077392951798295231395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86160718261967865530154263 129241077392951798295231395)
            ·
              refine ⟨193861616089427697442847093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129241077392951798295231395 193861616089427697442847093)
              ·
                refine ⟨18174526508383846635266915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193861616089427697442847093 18174526508383846635266915)
                ·
                  refine ⟨27261789762575769952900373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18174526508383846635266915 27261789762575769952900373)
                  ·
                    refine ⟨1277896395120739216542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27261789762575769952900373 1277896395120739216542205)
                    ·
                      rfl

theorem cell23_7466083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_7466083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466083 prefixEnd_7466083 := by exact prefixLift 7466083
  have htrace : WordTrace (prefixWord ++ tailWord_7466083) baseStart_7466083 baseEnd_7466083 := by
    simpa [prefixWord, tailWord_7466083, baseEnd_7466083] using wordTrace_append hprefix tailTrace_7466083
  have hstable : (prefixWord ++ tailWord_7466083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466083).length < 2 ^ (prefixWord ++ tailWord_7466083).sum := by decide
  have hdescent : baseEnd_7466083 < baseStart_7466083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466087 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 1, 5]
def baseStart_7466087 : Nat := 118140960795 + 7466087 * 2 ^ 59
def prefixEnd_7466087 : Nat := 4983230072969 + 3 ^ 40 * 7466087 * 2
def baseEnd_7466087 : Nat := 1277897079761611877992199

theorem tailTrace_7466087 : CollatzResearch.WordTrace tailWord_7466087 prefixEnd_7466087 1277897079761611877992199 := by
  unfold tailWord_7466087
  simp only [CollatzResearch.WordTrace]
  refine ⟨272310564102649379988324515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181540376068432919992216343 272310564102649379988324515)
  ·
    refine ⟨408465846153974069982486773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272310564102649379988324515 408465846153974069982486773)
    ·
      refine ⟨38293673076935069060858135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408465846153974069982486773 38293673076935069060858135)
      ·
        refine ⟨57440509615402603591287203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38293673076935069060858135 57440509615402603591287203)
        ·
          refine ⟨86160764423103905386930805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57440509615402603591287203 86160764423103905386930805)
          ·
            refine ⟨8077571664665991130024763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86160764423103905386930805 8077571664665991130024763)
            ·
              refine ⟨12116357496998986695037145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077571664665991130024763 12116357496998986695037145)
              ·
                refine ⟨9087268122749240021277859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116357496998986695037145 9087268122749240021277859)
                ·
                  refine ⟨13630902184123860031916789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087268122749240021277859 13630902184123860031916789)
                  ·
                    refine ⟨1277897079761611877992199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13630902184123860031916789 1277897079761611877992199)
                    ·
                      rfl

theorem cell23_7466087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_7466087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466087 prefixEnd_7466087 := by exact prefixLift 7466087
  have htrace : WordTrace (prefixWord ++ tailWord_7466087) baseStart_7466087 baseEnd_7466087 := by
    simpa [prefixWord, tailWord_7466087, baseEnd_7466087] using wordTrace_append hprefix tailTrace_7466087
  have hstable : (prefixWord ++ tailWord_7466087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466087).length < 2 ^ (prefixWord ++ tailWord_7466087).sum := by decide
  have hdescent : baseEnd_7466087 < baseStart_7466087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466094 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7466094 : Nat := 118140960795 + 7466094 * 2 ^ 59
def prefixEnd_7466094 : Nat := 4983230072969 + 3 ^ 40 * 7466094 * 2
def baseEnd_7466094 : Nat := 3833694833649417106589065

theorem tailTrace_7466094 : CollatzResearch.WordTrace tailWord_7466094 prefixEnd_7466094 3833694833649417106589065 := by
  unfold tailWord_7466094
  simp only [CollatzResearch.WordTrace]
  refine ⟨34038852426703002522978667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181540546275749346789219557 34038852426703002522978667)
  ·
    refine ⟨51058278640054503784468001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34038852426703002522978667 51058278640054503784468001)
    ·
      refine ⟨38293708980040877838351001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51058278640054503784468001 38293708980040877838351001)
      ·
        refine ⟨28720281735030658378763251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38293708980040877838351001 28720281735030658378763251)
        ·
          refine ⟨43080422602545987568144877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28720281735030658378763251 43080422602545987568144877)
          ·
            refine ⟨16155158475954745338054329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43080422602545987568144877 16155158475954745338054329)
            ·
              refine ⟨12116368856966059003540747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16155158475954745338054329 12116368856966059003540747)
              ·
                refine ⟨18174553285449088505311121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12116368856966059003540747 18174553285449088505311121)
                ·
                  refine ⟨13630914964086816378983341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18174553285449088505311121 13630914964086816378983341)
                  ·
                    refine ⟨5111593111532556142118753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13630914964086816378983341 5111593111532556142118753)
                    ·
                      refine ⟨3833694833649417106589065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111593111532556142118753 3833694833649417106589065)
                      ·
                        rfl

theorem cell23_7466094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7466094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466094 prefixEnd_7466094 := by exact prefixLift 7466094
  have htrace : WordTrace (prefixWord ++ tailWord_7466094) baseStart_7466094 baseEnd_7466094 := by
    simpa [prefixWord, tailWord_7466094, baseEnd_7466094] using wordTrace_append hprefix tailTrace_7466094
  have hstable : (prefixWord ++ tailWord_7466094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466094).length < 2 ^ (prefixWord ++ tailWord_7466094).sum := by decide
  have hdescent : baseEnd_7466094 < baseStart_7466094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466113 : List Nat := [1, 2, 4, 2, 2, 12]
def baseStart_7466113 : Nat := 118140960795 + 7466113 * 2 ^ 59
def prefixEnd_7466113 : Nat := 4983230072969 + 3 ^ 40 * 7466113 * 2
def baseEnd_7466113 : Nat := 15776562097867705894039

theorem tailTrace_7466113 : CollatzResearch.WordTrace tailWord_7466113 prefixEnd_7466113 15776562097867705894039 := by
  unfold tailWord_7466113
  simp only [CollatzResearch.WordTrace]
  refine ⟨272311512400555186428770993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181541008267036790952513995 272311512400555186428770993)
  ·
    refine ⟨204233634300416389821578245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272311512400555186428770993 204233634300416389821578245)
    ·
      refine ⟨38293806431328073091545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204233634300416389821578245 38293806431328073091545921)
      ·
        refine ⟨28720354823496054818659441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38293806431328073091545921 28720354823496054818659441)
        ·
          refine ⟨21540266117622041113994581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28720354823496054818659441 21540266117622041113994581)
          ·
            refine ⟨15776562097867705894039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21540266117622041113994581 15776562097867705894039)
            ·
              rfl

theorem cell23_7466113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 12].length) (baseStart_7466113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466113 prefixEnd_7466113 := by exact prefixLift 7466113
  have htrace : WordTrace (prefixWord ++ tailWord_7466113) baseStart_7466113 baseEnd_7466113 := by
    simpa [prefixWord, tailWord_7466113, baseEnd_7466113] using wordTrace_append hprefix tailTrace_7466113
  have hstable : (prefixWord ++ tailWord_7466113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466113).length < 2 ^ (prefixWord ++ tailWord_7466113).sum := by decide
  have hdescent : baseEnd_7466113 < baseStart_7466113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466130 : List Nat := [3, 2, 3, 1, 1, 2, 3, 8]
def baseStart_7466130 : Nat := 118140960795 + 7466130 * 2 ^ 59
def prefixEnd_7466130 : Nat := 4983230072969 + 3 ^ 40 * 7466130 * 2
def baseEnd_7466130 : Nat := 141989382183443665397737

theorem tailTrace_7466130 : CollatzResearch.WordTrace tailWord_7466130 prefixEnd_7466130 141989382183443665397737 := by
  unfold tailWord_7466130
  simp only [CollatzResearch.WordTrace]
  refine ⟨68078033110373399583034961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181541421627662398888093229 68078033110373399583034961)
  ·
    refine ⟨51058524832780049687276221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68078033110373399583034961 51058524832780049687276221)
    ·
      refine ⟨19146946812292518632728583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51058524832780049687276221 19146946812292518632728583)
      ·
        refine ⟨28720420218438777949092875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19146946812292518632728583 28720420218438777949092875)
        ·
          refine ⟨43080630327658166923639313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28720420218438777949092875 43080630327658166923639313)
          ·
            refine ⟨32310472745743625192729485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43080630327658166923639313 32310472745743625192729485)
            ·
              refine ⟨12116427279653859447273557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32310472745743625192729485 12116427279653859447273557)
              ·
                refine ⟨141989382183443665397737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12116427279653859447273557 141989382183443665397737)
                ·
                  rfl

theorem cell23_7466130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_7466130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466130 prefixEnd_7466130 := by exact prefixLift 7466130
  have htrace : WordTrace (prefixWord ++ tailWord_7466130) baseStart_7466130 baseEnd_7466130 := by
    simpa [prefixWord, tailWord_7466130, baseEnd_7466130] using wordTrace_append hprefix tailTrace_7466130
  have hstable : (prefixWord ++ tailWord_7466130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466130).length < 2 ^ (prefixWord ++ tailWord_7466130).sum := by decide
  have hdescent : baseEnd_7466130 < baseStart_7466130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466161 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7466161 : Nat := 118140960795 + 7466161 * 2 ^ 59
def prefixEnd_7466161 : Nat := 4983230072969 + 3 ^ 40 * 7466161 * 2
def baseEnd_7466161 : Nat := 3833729236853268344451257

theorem tailTrace_7466161 : CollatzResearch.WordTrace tailWord_7466161 prefixEnd_7466161 3833729236853268344451257 := by
  unfold tailWord_7466161
  simp only [CollatzResearch.WordTrace]
  refine ⟨272313263104381290626518337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181542175402920860417678891 272313263104381290626518337)
  ·
    refine ⟨204234947328285967969888753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272313263104381290626518337 204234947328285967969888753)
    ·
      refine ⟨153176210496214475977416565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204234947328285967969888753 153176210496214475977416565)
      ·
        refine ⟨14360269734020107122882803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153176210496214475977416565 14360269734020107122882803)
        ·
          refine ⟨21540404601030160684324205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14360269734020107122882803 21540404601030160684324205)
          ·
            refine ⟨8077651725386310256621577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21540404601030160684324205 8077651725386310256621577)
            ·
              refine ⟨6058238794039732692466183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077651725386310256621577 6058238794039732692466183)
              ·
                refine ⟨9087358191059599038699275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058238794039732692466183 9087358191059599038699275)
                ·
                  refine ⟨13631037286589398558048913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087358191059599038699275 13631037286589398558048913)
                  ·
                    refine ⟨10223277964942048918536685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13631037286589398558048913 10223277964942048918536685)
                    ·
                      refine ⟨3833729236853268344451257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223277964942048918536685 3833729236853268344451257)
                      ·
                        rfl

theorem cell23_7466161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7466161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466161 prefixEnd_7466161 := by exact prefixLift 7466161
  have htrace : WordTrace (prefixWord ++ tailWord_7466161) baseStart_7466161 baseEnd_7466161 := by
    simpa [prefixWord, tailWord_7466161, baseEnd_7466161] using wordTrace_append hprefix tailTrace_7466161
  have hstable : (prefixWord ++ tailWord_7466161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466161).length < 2 ^ (prefixWord ++ tailWord_7466161).sum := by decide
  have hdescent : baseEnd_7466161 < baseStart_7466161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466174 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_7466174 : Nat := 118140960795 + 7466174 * 2 ^ 59
def prefixEnd_7466174 : Nat := 4983230072969 + 3 ^ 40 * 7466174 * 2
def baseEnd_7466174 : Nat := 3833735912101776793588697

theorem tailTrace_7466174 : CollatzResearch.WordTrace tailWord_7466174 prefixEnd_7466174 3833735912101776793588697 := by
  unfold tailWord_7466174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039217156666774230842697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181542491502222795897827717 34039217156666774230842697)
  ·
    refine ⟨25529412867500080673132023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34039217156666774230842697 25529412867500080673132023)
    ·
      refine ⟨38294119301250121009698035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25529412867500080673132023 38294119301250121009698035)
      ·
        refine ⟨57441178951875181514547053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38294119301250121009698035 57441178951875181514547053)
        ·
          refine ⟨21540442106953193067955145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57441178951875181514547053 21540442106953193067955145)
          ·
            refine ⟨16155331580214894800966359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21540442106953193067955145 16155331580214894800966359)
            ·
              refine ⟨24232997370322342201449539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155331580214894800966359 24232997370322342201449539)
              ·
                refine ⟨36349496055483513302174309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24232997370322342201449539 36349496055483513302174309)
                ·
                  refine ⟨6815530510403158744157683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36349496055483513302174309 6815530510403158744157683)
                  ·
                    refine ⟨10223295765604738116236525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6815530510403158744157683 10223295765604738116236525)
                    ·
                      refine ⟨3833735912101776793588697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223295765604738116236525 3833735912101776793588697)
                      ·
                        rfl

theorem cell23_7466174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_7466174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466174 prefixEnd_7466174 := by exact prefixLift 7466174
  have htrace : WordTrace (prefixWord ++ tailWord_7466174) baseStart_7466174 baseEnd_7466174 := by
    simpa [prefixWord, tailWord_7466174, baseEnd_7466174] using wordTrace_append hprefix tailTrace_7466174
  have hstable : (prefixWord ++ tailWord_7466174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466174).length < 2 ^ (prefixWord ++ tailWord_7466174).sum := by decide
  have hdescent : baseEnd_7466174 < baseStart_7466174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7466230 : Nat := 118140960795 + 7466230 * 2 ^ 59
def prefixEnd_7466230 : Nat := 4983230072969 + 3 ^ 40 * 7466230 * 2
def baseEnd_7466230 : Nat := 3833764667018428574488439

theorem tailTrace_7466230 : CollatzResearch.WordTrace tailWord_7466230 prefixEnd_7466230 3833764667018428574488439 := by
  unfold tailWord_7466230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019736233820707213173759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181543853160754210273853429 17019736233820707213173759)
  ·
    refine ⟨25529604350731060819760639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17019736233820707213173759 25529604350731060819760639)
    ·
      refine ⟨38294406526096591229640959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25529604350731060819760639 38294406526096591229640959)
      ·
        refine ⟨57441609789144886844461439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38294406526096591229640959 57441609789144886844461439)
        ·
          refine ⟨86162414683717330266692159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57441609789144886844461439 86162414683717330266692159)
          ·
            refine ⟨129243622025575995400038239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86162414683717330266692159 129243622025575995400038239)
            ·
              refine ⟨193865433038363993100057359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129243622025575995400038239 193865433038363993100057359)
              ·
                refine ⟨290798149557545989650086039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193865433038363993100057359 290798149557545989650086039)
                ·
                  refine ⟨436197224336318984475129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290798149557545989650086039 436197224336318984475129059)
                  ·
                    refine ⟨654295836504478476712693589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 436197224336318984475129059 654295836504478476712693589)
                    ·
                      refine ⟨3833764667018428574488439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 654295836504478476712693589 3833764667018428574488439)
                      ·
                        rfl

theorem cell23_7466230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7466230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466230 prefixEnd_7466230 := by exact prefixLift 7466230
  have htrace : WordTrace (prefixWord ++ tailWord_7466230) baseStart_7466230 baseEnd_7466230 := by
    simpa [prefixWord, tailWord_7466230, baseEnd_7466230] using wordTrace_append hprefix tailTrace_7466230
  have hstable : (prefixWord ++ tailWord_7466230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466230).length < 2 ^ (prefixWord ++ tailWord_7466230).sum := by decide
  have hdescent : baseEnd_7466230 < baseStart_7466230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466250 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_7466250 : Nat := 118140960795 + 7466250 * 2 ^ 59
def prefixEnd_7466250 : Nat := 4983230072969 + 3 ^ 40 * 7466250 * 2
def baseEnd_7466250 : Nat := 1277924978877172832079449

theorem tailTrace_7466250 : CollatzResearch.WordTrace tailWord_7466250 prefixEnd_7466250 1277924978877172832079449 := by
  unfold tailWord_7466250
  simp only [CollatzResearch.WordTrace]
  refine ⟨68079127300264714706627051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181544339467372572551005469 68079127300264714706627051)
  ·
    refine ⟨102118690950397072059940577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68079127300264714706627051 102118690950397072059940577)
    ·
      refine ⟨76589018212797804044955433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102118690950397072059940577 76589018212797804044955433)
      ·
        refine ⟨57441763659598353033716575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76589018212797804044955433 57441763659598353033716575)
        ·
          refine ⟨86162645489397529550574863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57441763659598353033716575 86162645489397529550574863)
          ·
            refine ⟨129243968234096294325862295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86162645489397529550574863 129243968234096294325862295)
            ·
              refine ⟨193865952351144441488793443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129243968234096294325862295 193865952351144441488793443)
              ·
                refine ⟨290798928526716662233190165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193865952351144441488793443 290798928526716662233190165)
                ·
                  refine ⟨13631199774689843542180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 290798928526716662233190165 13631199774689843542180789)
                  ·
                    refine ⟨1277924978877172832079449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13631199774689843542180789 1277924978877172832079449)
                    ·
                      rfl

theorem cell23_7466250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_7466250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466250 prefixEnd_7466250 := by exact prefixLift 7466250
  have htrace : WordTrace (prefixWord ++ tailWord_7466250) baseStart_7466250 baseEnd_7466250 := by
    simpa [prefixWord, tailWord_7466250, baseEnd_7466250] using wordTrace_append hprefix tailTrace_7466250
  have hstable : (prefixWord ++ tailWord_7466250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466250).length < 2 ^ (prefixWord ++ tailWord_7466250).sum := by decide
  have hdescent : baseEnd_7466250 < baseStart_7466250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466287 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 4, 2]
def baseStart_7466287 : Nat := 118140960795 + 7466287 * 2 ^ 59
def prefixEnd_7466287 : Nat := 4983230072969 + 3 ^ 40 * 7466287 * 2
def baseEnd_7466287 : Nat := 3833793935415734851475677

theorem tailTrace_7466287 : CollatzResearch.WordTrace tailWord_7466287 prefixEnd_7466287 3833793935415734851475677 := by
  unfold tailWord_7466287
  simp only [CollatzResearch.WordTrace]
  refine ⟨272317858701924814145605115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181545239134616542763736743 272317858701924814145605115)
  ·
    refine ⟨408476788052887221218407673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272317858701924814145605115 408476788052887221218407673)
    ·
      refine ⟨306357591039665415913805755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408476788052887221218407673 306357591039665415913805755)
      ·
        refine ⟨459536386559498123870708633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306357591039665415913805755 459536386559498123870708633)
        ·
          refine ⟨344652289919623592903031475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459536386559498123870708633 344652289919623592903031475)
          ·
            refine ⟨516978434879435389354547213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344652289919623592903031475 516978434879435389354547213)
            ·
              refine ⟨193866913079788271007955205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516978434879435389354547213 193866913079788271007955205)
              ·
                refine ⟨36350046202460300813991601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193866913079788271007955205 36350046202460300813991601)
                ·
                  refine ⟨27262534651845225610493701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36350046202460300813991601 27262534651845225610493701)
                  ·
                    refine ⟨5111725247220979801967569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27262534651845225610493701 5111725247220979801967569)
                    ·
                      refine ⟨3833793935415734851475677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111725247220979801967569 3833793935415734851475677)
                      ·
                        rfl

theorem cell23_7466287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4, 2].length) (baseStart_7466287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466287 prefixEnd_7466287 := by exact prefixLift 7466287
  have htrace : WordTrace (prefixWord ++ tailWord_7466287) baseStart_7466287 baseEnd_7466287 := by
    simpa [prefixWord, tailWord_7466287, baseEnd_7466287] using wordTrace_append hprefix tailTrace_7466287
  have hstable : (prefixWord ++ tailWord_7466287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466287).length < 2 ^ (prefixWord ++ tailWord_7466287).sum := by decide
  have hdescent : baseEnd_7466287 < baseStart_7466287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466347 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 5, 2]
def baseStart_7466347 : Nat := 118140960795 + 7466347 * 2 ^ 59
def prefixEnd_7466347 : Nat := 4983230072969 + 3 ^ 40 * 7466347 * 2
def baseEnd_7466347 : Nat := 3833824744255004616725401

theorem tailTrace_7466347 : CollatzResearch.WordTrace tailWord_7466347 prefixEnd_7466347 3833824744255004616725401 := by
  unfold tailWord_7466347
  simp only [CollatzResearch.WordTrace]
  refine ⟨272320047081707444392789295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181546698054471629595192863 272320047081707444392789295)
  ·
    refine ⟨408480070622561166589183943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272320047081707444392789295 408480070622561166589183943)
    ·
      refine ⟨612720105933841749883775915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408480070622561166589183943 612720105933841749883775915)
      ·
        refine ⟨919080158900762624825663873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612720105933841749883775915 919080158900762624825663873)
        ·
          refine ⟨689310119175571968619247905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919080158900762624825663873 689310119175571968619247905)
          ·
            refine ⟨516982589381678976464435929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689310119175571968619247905 516982589381678976464435929)
            ·
              refine ⟨387736942036259232348326947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516982589381678976464435929 387736942036259232348326947)
              ·
                refine ⟨581605413054388848522490421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387736942036259232348326947 581605413054388848522490421)
                ·
                  refine ⟨54525507473848954548983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581605413054388848522490421 54525507473848954548983477)
                  ·
                    refine ⟨5111766325673339488967201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54525507473848954548983477 5111766325673339488967201)
                    ·
                      refine ⟨3833824744255004616725401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111766325673339488967201 3833824744255004616725401)
                      ·
                        rfl

theorem cell23_7466347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5, 2].length) (baseStart_7466347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466347 prefixEnd_7466347 := by exact prefixLift 7466347
  have htrace : WordTrace (prefixWord ++ tailWord_7466347) baseStart_7466347 baseEnd_7466347 := by
    simpa [prefixWord, tailWord_7466347, baseEnd_7466347] using wordTrace_append hprefix tailTrace_7466347
  have hstable : (prefixWord ++ tailWord_7466347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466347).length < 2 ^ (prefixWord ++ tailWord_7466347).sum := by decide
  have hdescent : baseEnd_7466347 < baseStart_7466347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466394 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_7466394 : Nat := 118140960795 + 7466394 * 2 ^ 59
def prefixEnd_7466394 : Nat := 4983230072969 + 3 ^ 40 * 7466394 * 2
def baseEnd_7466394 : Nat := 3833848877845765932837685

theorem tailTrace_7466394 : CollatzResearch.WordTrace tailWord_7466394 prefixEnd_7466394 3833848877845765932837685 := by
  unfold tailWord_7466394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68080440328134292854937559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181547840875024780946500157 68080440328134292854937559)
  ·
    refine ⟨102120660492201439282406339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68080440328134292854937559 102120660492201439282406339)
    ·
      refine ⟨153180990738302158923609509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102120660492201439282406339 153180990738302158923609509)
      ·
        refine ⟨28721435763431654798176783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153180990738302158923609509 28721435763431654798176783)
        ·
          refine ⟨43082153645147482197265175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721435763431654798176783 43082153645147482197265175)
          ·
            refine ⟨64623230467721223295897763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43082153645147482197265175 64623230467721223295897763)
            ·
              refine ⟨96934845701581834943846645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64623230467721223295897763 96934845701581834943846645)
              ·
                refine ⟨9087641784523297025985623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96934845701581834943846645 9087641784523297025985623)
                ·
                  refine ⟨13631462676784945538978435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087641784523297025985623 13631462676784945538978435)
                  ·
                    refine ⟨20447194015177418308467653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13631462676784945538978435 20447194015177418308467653)
                    ·
                      refine ⟨3833848877845765932837685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20447194015177418308467653 3833848877845765932837685)
                      ·
                        rfl

theorem cell23_7466394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_7466394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466394 prefixEnd_7466394 := by exact prefixLift 7466394
  have htrace : WordTrace (prefixWord ++ tailWord_7466394) baseStart_7466394 baseEnd_7466394 := by
    simpa [prefixWord, tailWord_7466394, baseEnd_7466394] using wordTrace_append hprefix tailTrace_7466394
  have hstable : (prefixWord ++ tailWord_7466394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466394).length < 2 ^ (prefixWord ++ tailWord_7466394).sum := by decide
  have hdescent : baseEnd_7466394 < baseStart_7466394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466404 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_7466404 : Nat := 118140960795 + 7466404 * 2 ^ 59
def prefixEnd_7466404 : Nat := 4983230072969 + 3 ^ 40 * 7466404 * 2
def baseEnd_7466404 : Nat := 1277951337550770297904213

theorem tailTrace_7466404 : CollatzResearch.WordTrace tailWord_7466404 prefixEnd_7466404 1277951337550770297904213 := by
  unfold tailWord_7466404
  simp only [CollatzResearch.WordTrace]
  refine ⟨136161063021250471563807133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181548084028333962085076177 136161063021250471563807133)
  ·
    refine ⟨51060398632968926836427675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136161063021250471563807133 51060398632968926836427675)
    ·
      refine ⟨76590597949453390254641513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51060398632968926836427675 76590597949453390254641513)
      ·
        refine ⟨57442948462090042690981135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76590597949453390254641513 57442948462090042690981135)
        ·
          refine ⟨86164422693135064036471703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57442948462090042690981135 86164422693135064036471703)
          ·
            refine ⟨129246634039702596054707555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86164422693135064036471703 129246634039702596054707555)
            ·
              refine ⟨193869951059553894082061333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129246634039702596054707555 193869951059553894082061333)
              ·
                refine ⟨9087653955916588785096625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193869951059553894082061333 9087653955916588785096625)
                ·
                  refine ⟨6815740466937441588822469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087653955916588785096625 6815740466937441588822469)
                  ·
                    refine ⟨1277951337550770297904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815740466937441588822469 1277951337550770297904213)
                    ·
                      rfl

theorem cell23_7466404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_7466404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466404 prefixEnd_7466404 := by exact prefixLift 7466404
  have htrace : WordTrace (prefixWord ++ tailWord_7466404) baseStart_7466404 baseEnd_7466404 := by
    simpa [prefixWord, tailWord_7466404, baseEnd_7466404] using wordTrace_append hprefix tailTrace_7466404
  have hstable : (prefixWord ++ tailWord_7466404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466404).length < 2 ^ (prefixWord ++ tailWord_7466404).sum := by decide
  have hdescent : baseEnd_7466404 < baseStart_7466404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466407 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7466407 : Nat := 118140960795 + 7466407 * 2 ^ 59
def prefixEnd_7466407 : Nat := 4983230072969 + 3 ^ 40 * 7466407 * 2
def baseEnd_7466407 : Nat := 3833855553094274381975125

theorem tailTrace_7466407 : CollatzResearch.WordTrace tailWord_7466407 prefixEnd_7466407 3833855553094274381975125 := by
  unfold tailWord_7466407
  simp only [CollatzResearch.WordTrace]
  refine ⟨272322235461490074639973475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181548156974326716426648983 272322235461490074639973475)
  ·
    refine ⟨408483353192235111959960213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272322235461490074639973475 408483353192235111959960213)
    ·
      refine ⟨19147657180886020873123135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 408483353192235111959960213 19147657180886020873123135)
      ·
        refine ⟨28721485771329031309684703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19147657180886020873123135 28721485771329031309684703)
        ·
          refine ⟨43082228656993546964527055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721485771329031309684703 43082228656993546964527055)
          ·
            refine ⟨64623342985490320446790583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43082228656993546964527055 64623342985490320446790583)
            ·
              refine ⟨96935014478235480670185875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64623342985490320446790583 96935014478235480670185875)
              ·
                refine ⟨145402521717353221005278813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96935014478235480670185875 145402521717353221005278813)
                ·
                  refine ⟨54525945644007457876979555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145402521717353221005278813 54525945644007457876979555)
                  ·
                    refine ⟨81788918466011186815469333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54525945644007457876979555 81788918466011186815469333)
                    ·
                      refine ⟨3833855553094274381975125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81788918466011186815469333 3833855553094274381975125)
                      ·
                        rfl

theorem cell23_7466407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7466407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466407 prefixEnd_7466407 := by exact prefixLift 7466407
  have htrace : WordTrace (prefixWord ++ tailWord_7466407) baseStart_7466407 baseEnd_7466407 := by
    simpa [prefixWord, tailWord_7466407, baseEnd_7466407] using wordTrace_append hprefix tailTrace_7466407
  have hstable : (prefixWord ++ tailWord_7466407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466407).length < 2 ^ (prefixWord ++ tailWord_7466407).sum := by decide
  have hdescent : baseEnd_7466407 < baseStart_7466407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466417 : List Nat := [1, 2, 2, 4, 1, 1, 4, 8]
def baseStart_7466417 : Nat := 118140960795 + 7466417 * 2 ^ 59
def prefixEnd_7466417 : Nat := 4983230072969 + 3 ^ 40 * 7466417 * 2
def baseEnd_7466417 : Nat := 141994840292622938624077

theorem tailTrace_7466417 : CollatzResearch.WordTrace tailWord_7466417 prefixEnd_7466417 141994840292622938624077 := by
  unfold tailWord_7466417
  simp only [CollatzResearch.WordTrace]
  refine ⟨272322600191453846347837505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181548400127635897565225003 272322600191453846347837505)
  ·
    refine ⟨204241950143590384760878129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272322600191453846347837505 204241950143590384760878129)
    ·
      refine ⟨153181462607692788570658597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204241950143590384760878129 153181462607692788570658597)
      ·
        refine ⟨28721524238942397856998487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153181462607692788570658597 28721524238942397856998487)
        ·
          refine ⟨43082286358413596785497731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721524238942397856998487 43082286358413596785497731)
          ·
            refine ⟨64623429537620395178246597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43082286358413596785497731 64623429537620395178246597)
            ·
              refine ⟨12116893038303824095921237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64623429537620395178246597 12116893038303824095921237)
              ·
                refine ⟨141994840292622938624077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12116893038303824095921237 141994840292622938624077)
                ·
                  rfl

theorem cell23_7466417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 8].length) (baseStart_7466417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466417 prefixEnd_7466417 := by exact prefixLift 7466417
  have htrace : WordTrace (prefixWord ++ tailWord_7466417) baseStart_7466417 baseEnd_7466417 := by
    simpa [prefixWord, tailWord_7466417, baseEnd_7466417] using wordTrace_append hprefix tailTrace_7466417
  have hstable : (prefixWord ++ tailWord_7466417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466417).length < 2 ^ (prefixWord ++ tailWord_7466417).sum := by decide
  have hdescent : baseEnd_7466417 < baseStart_7466417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466421 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7466421 : Nat := 118140960795 + 7466421 * 2 ^ 59
def prefixEnd_7466421 : Nat := 4983230072969 + 3 ^ 40 * 7466421 * 2
def baseEnd_7466421 : Nat := 1277954247274479109066687

theorem tailTrace_7466421 : CollatzResearch.WordTrace tailWord_7466421 prefixEnd_7466421 1277954247274479109066687 := by
  unfold tailWord_7466421
  simp only [CollatzResearch.WordTrace]
  refine ⟨272322746083439355030983117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181548497388959570020655411 272322746083439355030983117)
  ·
    refine ⟨102121029781289758136618669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272322746083439355030983117 102121029781289758136618669)
    ·
      refine ⟨38295386167983659301232001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102121029781289758136618669 38295386167983659301232001)
      ·
        refine ⟨28721539625987744475924001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38295386167983659301232001 28721539625987744475924001)
        ·
          refine ⟨21541154719490808356943001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28721539625987744475924001 21541154719490808356943001)
          ·
            refine ⟨16155866039618106267707251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21541154719490808356943001 16155866039618106267707251)
            ·
              refine ⟨24233799059427159401560877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155866039618106267707251 24233799059427159401560877)
              ·
                refine ⟨9087674647285184775585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24233799059427159401560877 9087674647285184775585329)
                ·
                  refine ⟨6815755985463888581688997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9087674647285184775585329 6815755985463888581688997)
                  ·
                    refine ⟨1277954247274479109066687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6815755985463888581688997 1277954247274479109066687)
                    ·
                      rfl

theorem cell23_7466421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7466421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466421 prefixEnd_7466421 := by exact prefixLift 7466421
  have htrace : WordTrace (prefixWord ++ tailWord_7466421) baseStart_7466421 baseEnd_7466421 := by
    simpa [prefixWord, tailWord_7466421, baseEnd_7466421] using wordTrace_append hprefix tailTrace_7466421
  have hstable : (prefixWord ++ tailWord_7466421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466421).length < 2 ^ (prefixWord ++ tailWord_7466421).sum := by decide
  have hdescent : baseEnd_7466421 < baseStart_7466421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466428 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7466428 : Nat := 118140960795 + 7466428 * 2 ^ 59
def prefixEnd_7466428 : Nat := 4983230072969 + 3 ^ 40 * 7466428 * 2
def baseEnd_7466428 : Nat := 3833866336188018799812529

theorem tailTrace_7466428 : CollatzResearch.WordTrace tailWord_7466428 prefixEnd_7466428 3833866336188018799812529 := by
  unfold tailWord_7466428
  simp only [CollatzResearch.WordTrace]
  refine ⟨136161500697206997613243969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181548667596275996817658625 136161500697206997613243969)
  ·
    refine ⟨102121125522905248209932977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136161500697206997613243969 102121125522905248209932977)
    ·
      refine ⟨76590844142178936157449733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102121125522905248209932977 76590844142178936157449733)
      ·
        refine ⟨14360783276658550529521825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76590844142178936157449733 14360783276658550529521825)
        ·
          refine ⟨10770587457493912897141369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14360783276658550529521825 10770587457493912897141369)
          ·
            refine ⟨8077940593120434672856027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10770587457493912897141369 8077940593120434672856027)
            ·
              refine ⟨12116910889680652009284041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077940593120434672856027 12116910889680652009284041)
              ·
                refine ⟨9087683167260489006963031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12116910889680652009284041 9087683167260489006963031)
                ·
                  refine ⟨13631524750890733510444547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9087683167260489006963031 13631524750890733510444547)
                  ·
                    refine ⟨20447287126336100265666821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13631524750890733510444547 20447287126336100265666821)
                    ·
                      refine ⟨3833866336188018799812529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20447287126336100265666821 3833866336188018799812529)
                      ·
                        rfl

theorem cell23_7466428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7466428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466428 prefixEnd_7466428 := by exact prefixLift 7466428
  have htrace : WordTrace (prefixWord ++ tailWord_7466428) baseStart_7466428 baseEnd_7466428 := by
    simpa [prefixWord, tailWord_7466428, baseEnd_7466428] using wordTrace_append hprefix tailTrace_7466428
  have hstable : (prefixWord ++ tailWord_7466428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466428).length < 2 ^ (prefixWord ++ tailWord_7466428).sum := by decide
  have hdescent : baseEnd_7466428 < baseStart_7466428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466444 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7466444 : Nat := 118140960795 + 7466444 * 2 ^ 59
def prefixEnd_7466444 : Nat := 4983230072969 + 3 ^ 40 * 7466444 * 2
def baseEnd_7466444 : Nat := 3833874551878490737212455

theorem tailTrace_7466444 : CollatzResearch.WordTrace tailWord_7466444 prefixEnd_7466444 3833874551878490737212455 := by
  unfold tailWord_7466444
  simp only [CollatzResearch.WordTrace]
  refine ⟨136161792481178014979535193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181549056641570686639380257 136161792481178014979535193)
  ·
    refine ⟨102121344360883511234651395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136161792481178014979535193 102121344360883511234651395)
    ·
      refine ⟨153182016541325266851977093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102121344360883511234651395 153182016541325266851977093)
      ·
        refine ⟨28721628101498487534745705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153182016541325266851977093 28721628101498487534745705)
        ·
          refine ⟨21541221076123865651059279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28721628101498487534745705 21541221076123865651059279)
          ·
            refine ⟨32311831614185798476588919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21541221076123865651059279 32311831614185798476588919)
            ·
              refine ⟨48467747421278697714883379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32311831614185798476588919 48467747421278697714883379)
              ·
                refine ⟨72701621131918046572325069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48467747421278697714883379 72701621131918046572325069)
                ·
                  refine ⟨27263107924469267464621901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72701621131918046572325069 27263107924469267464621901)
                  ·
                    refine ⟨10223665471675975299233213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27263107924469267464621901 10223665471675975299233213)
                    ·
                      refine ⟨3833874551878490737212455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223665471675975299233213 3833874551878490737212455)
                      ·
                        rfl

theorem cell23_7466444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7466444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466444 prefixEnd_7466444 := by exact prefixLift 7466444
  have htrace : WordTrace (prefixWord ++ tailWord_7466444) baseStart_7466444 baseEnd_7466444 := by
    simpa [prefixWord, tailWord_7466444, baseEnd_7466444] using wordTrace_append hprefix tailTrace_7466444
  have hstable : (prefixWord ++ tailWord_7466444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466444).length < 2 ^ (prefixWord ++ tailWord_7466444).sum := by decide
  have hdescent : baseEnd_7466444 < baseStart_7466444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466471 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7466471 : Nat := 118140960795 + 7466471 * 2 ^ 59
def prefixEnd_7466471 : Nat := 4983230072969 + 3 ^ 40 * 7466471 * 2
def baseEnd_7466471 : Nat := 3833888415856162131574831

theorem tailTrace_7466471 : CollatzResearch.WordTrace tailWord_7466471 prefixEnd_7466471 3833888415856162131574831 := by
  unfold tailWord_7466471
  simp only [CollatzResearch.WordTrace]
  refine ⟨272324569733258213570303267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181549713155505475713535511 272324569733258213570303267)
  ·
    refine ⟨408486854599887320355454901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272324569733258213570303267 408486854599887320355454901)
    ·
      refine ⟨38295642618739436283323897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 408486854599887320355454901 38295642618739436283323897)
      ·
        refine ⟨28721731964054577212492923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38295642618739436283323897 28721731964054577212492923)
        ·
          refine ⟨43082597946081865818739385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721731964054577212492923 43082597946081865818739385)
          ·
            refine ⟨32311948459561399364054539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43082597946081865818739385 32311948459561399364054539)
            ·
              refine ⟨48467922689342099046081809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32311948459561399364054539 48467922689342099046081809)
              ·
                refine ⟨36350942017006574284561357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48467922689342099046081809 36350942017006574284561357)
                ·
                  refine ⟨13631603256377465356710509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36350942017006574284561357 13631603256377465356710509)
                  ·
                    refine ⟨5111851221141549508766441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13631603256377465356710509 5111851221141549508766441)
                    ·
                      refine ⟨3833888415856162131574831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111851221141549508766441 3833888415856162131574831)
                      ·
                        rfl

theorem cell23_7466471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7466471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466471 prefixEnd_7466471 := by exact prefixLift 7466471
  have htrace : WordTrace (prefixWord ++ tailWord_7466471) baseStart_7466471 baseEnd_7466471 := by
    simpa [prefixWord, tailWord_7466471, baseEnd_7466471] using wordTrace_append hprefix tailTrace_7466471
  have hstable : (prefixWord ++ tailWord_7466471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466471).length < 2 ^ (prefixWord ++ tailWord_7466471).sum := by decide
  have hdescent : baseEnd_7466471 < baseStart_7466471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466487 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_7466487 : Nat := 118140960795 + 7466487 * 2 ^ 59
def prefixEnd_7466487 : Nat := 4983230072969 + 3 ^ 40 * 7466487 * 2
def baseEnd_7466487 : Nat := 3833896631546634068974757

theorem tailTrace_7466487 : CollatzResearch.WordTrace tailWord_7466487 prefixEnd_7466487 3833896631546634068974757 := by
  unfold tailWord_7466487
  simp only [CollatzResearch.WordTrace]
  refine ⟨272325153301200248302885715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181550102200800165535257143 272325153301200248302885715)
  ·
    refine ⟨408487729951800372454328573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272325153301200248302885715 408487729951800372454328573)
    ·
      refine ⟨153182898731925139670373215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408487729951800372454328573 153182898731925139670373215)
      ·
        refine ⟨229774348097887709505559823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153182898731925139670373215 229774348097887709505559823)
        ·
          refine ⟨344661522146831564258339735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229774348097887709505559823 344661522146831564258339735)
          ·
            refine ⟨516992283220247346387509603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344661522146831564258339735 516992283220247346387509603)
            ·
              refine ⟨775488424830371019581264405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516992283220247346387509603 775488424830371019581264405)
              ·
                refine ⟨36351019913923641542871769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 775488424830371019581264405 36351019913923641542871769)
                ·
                  refine ⟨27263264935442731157153827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36351019913923641542871769 27263264935442731157153827)
                  ·
                    refine ⟨40894897403164096735730741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27263264935442731157153827 40894897403164096735730741)
                    ·
                      refine ⟨3833896631546634068974757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40894897403164096735730741 3833896631546634068974757)
                      ·
                        rfl

theorem cell23_7466487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_7466487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466487 prefixEnd_7466487 := by exact prefixLift 7466487
  have htrace : WordTrace (prefixWord ++ tailWord_7466487) baseStart_7466487 baseEnd_7466487 := by
    simpa [prefixWord, tailWord_7466487, baseEnd_7466487] using wordTrace_append hprefix tailTrace_7466487
  have hstable : (prefixWord ++ tailWord_7466487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466487).length < 2 ^ (prefixWord ++ tailWord_7466487).sum := by decide
  have hdescent : baseEnd_7466487 < baseStart_7466487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466501 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_7466501 : Nat := 118140960795 + 7466501 * 2 ^ 59
def prefixEnd_7466501 : Nat := 4983230072969 + 3 ^ 40 * 7466501 * 2
def baseEnd_7466501 : Nat := 3833903820275797014199693

theorem tailTrace_7466501 : CollatzResearch.WordTrace tailWord_7466501 prefixEnd_7466501 3833903820275797014199693 := by
  unfold tailWord_7466501
  simp only [CollatzResearch.WordTrace]
  refine ⟨272325663923149528693895357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181550442615433019129263571 272325663923149528693895357)
  ·
    refine ⟨102122123971181073260210759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272325663923149528693895357 102122123971181073260210759)
    ·
      refine ⟨153183185956771609890316139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102122123971181073260210759 153183185956771609890316139)
      ·
        refine ⟨229774778935157414835474209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153183185956771609890316139 229774778935157414835474209)
        ·
          refine ⟨172331084201368061126605657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229774778935157414835474209 172331084201368061126605657)
          ·
            refine ⟨129248313151026045844954243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172331084201368061126605657 129248313151026045844954243)
            ·
              refine ⟨193872469726539068767431365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129248313151026045844954243 193872469726539068767431365)
              ·
                refine ⟨36351088073726075393893381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193872469726539068767431365 36351088073726075393893381)
                ·
                  refine ⟨6815829013823639136355009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36351088073726075393893381 6815829013823639136355009)
                  ·
                    refine ⟨5111871760367729352266257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6815829013823639136355009 5111871760367729352266257)
                    ·
                      refine ⟨3833903820275797014199693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5111871760367729352266257 3833903820275797014199693)
                      ·
                        rfl

theorem cell23_7466501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_7466501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466501 prefixEnd_7466501 := by exact prefixLift 7466501
  have htrace : WordTrace (prefixWord ++ tailWord_7466501) baseStart_7466501 baseEnd_7466501 := by
    simpa [prefixWord, tailWord_7466501, baseEnd_7466501] using wordTrace_append hprefix tailTrace_7466501
  have hstable : (prefixWord ++ tailWord_7466501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466501).length < 2 ^ (prefixWord ++ tailWord_7466501).sum := by decide
  have hdescent : baseEnd_7466501 < baseStart_7466501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466524 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 7]
def baseStart_7466524 : Nat := 118140960795 + 7466524 * 2 ^ 59
def prefixEnd_7466524 : Nat := 4983230072969 + 3 ^ 40 * 7466524 * 2
def baseEnd_7466524 : Nat := 425990625592316713801343

theorem tailTrace_7466524 : CollatzResearch.WordTrace tailWord_7466524 prefixEnd_7466524 425990625592316713801343 := by
  unfold tailWord_7466524
  simp only [CollatzResearch.WordTrace]
  refine ⟨136163251401033101810991313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181551001868044135747988417 136163251401033101810991313)
  ·
    refine ⟨102122438550774826358243485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136163251401033101810991313 102122438550774826358243485)
    ·
      refine ⟨38295914456540559884341307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102122438550774826358243485 38295914456540559884341307)
      ·
        refine ⟨57443871684810839826511961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38295914456540559884341307 57443871684810839826511961)
        ·
          refine ⟨43082903763608129869883971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57443871684810839826511961 43082903763608129869883971)
          ·
            refine ⟨64624355645412194804825957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43082903763608129869883971 64624355645412194804825957)
            ·
              refine ⟨12117066683514786525904867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64624355645412194804825957 12117066683514786525904867)
              ·
                refine ⟨18175600025272179788857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117066683514786525904867 18175600025272179788857301)
                ·
                  refine ⟨425990625592316713801343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18175600025272179788857301 425990625592316713801343)
                  ·
                    rfl

theorem cell23_7466524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_7466524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466524 prefixEnd_7466524 := by exact prefixLift 7466524
  have htrace : WordTrace (prefixWord ++ tailWord_7466524) baseStart_7466524 baseEnd_7466524 := by
    simpa [prefixWord, tailWord_7466524, baseEnd_7466524] using wordTrace_append hprefix tailTrace_7466524
  have hstable : (prefixWord ++ tailWord_7466524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466524).length < 2 ^ (prefixWord ++ tailWord_7466524).sum := by decide
  have hdescent : baseEnd_7466524 < baseStart_7466524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466554 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_7466554 : Nat := 118140960795 + 7466554 * 2 ^ 59
def prefixEnd_7466554 : Nat := 4983230072969 + 3 ^ 40 * 7466554 * 2
def baseEnd_7466554 : Nat := 1277977011583495102278983

theorem tailTrace_7466554 : CollatzResearch.WordTrace tailWord_7466554 prefixEnd_7466554 1277977011583495102278983 := by
  unfold tailWord_7466554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68081899247989379686393679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181551731327971679163716477 68081899247989379686393679)
  ·
    refine ⟨102122848871984069529590519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68081899247989379686393679 102122848871984069529590519)
    ·
      refine ⟨153184273307976104294385779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102122848871984069529590519 153184273307976104294385779)
      ·
        refine ⟨229776409961964156441578669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153184273307976104294385779 229776409961964156441578669)
        ·
          refine ⟨86166153735736558665592001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229776409961964156441578669 86166153735736558665592001)
          ·
            refine ⟨64624615301802418999194001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86166153735736558665592001 64624615301802418999194001)
            ·
              refine ⟨48468461476351814249395501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64624615301802418999194001 48468461476351814249395501)
              ·
                refine ⟨18175673053631930343523313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48468461476351814249395501 18175673053631930343523313)
                ·
                  refine ⟨13631754790223947757642485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18175673053631930343523313 13631754790223947757642485)
                  ·
                    refine ⟨1277977011583495102278983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13631754790223947757642485 1277977011583495102278983)
                    ·
                      rfl

theorem cell23_7466554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_7466554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466554 prefixEnd_7466554 := by exact prefixLift 7466554
  have htrace : WordTrace (prefixWord ++ tailWord_7466554) baseStart_7466554 baseEnd_7466554 := by
    simpa [prefixWord, tailWord_7466554, baseEnd_7466554] using wordTrace_append hprefix tailTrace_7466554
  have hstable : (prefixWord ++ tailWord_7466554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466554).length < 2 ^ (prefixWord ++ tailWord_7466554).sum := by decide
  have hdescent : baseEnd_7466554 < baseStart_7466554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466631 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 6]
def baseStart_7466631 : Nat := 118140960795 + 7466631 * 2 ^ 59
def prefixEnd_7466631 : Nat := 4983230072969 + 3 ^ 40 * 7466631 * 2
def baseEnd_7466631 : Nat := 425996730306764611730455

theorem tailTrace_7466631 : CollatzResearch.WordTrace tailWord_7466631 prefixEnd_7466631 425996730306764611730455 := by
  unfold tailWord_7466631
  simp only [CollatzResearch.WordTrace]
  refine ⟨272330405412678560896127747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181553603608452373930751831 272330405412678560896127747)
  ·
    refine ⟨408495608119017841344191621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272330405412678560896127747 408495608119017841344191621)
    ·
      refine ⟨76592926522315845252035929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408495608119017841344191621 76592926522315845252035929)
      ·
        refine ⟨57444694891736883939026947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76592926522315845252035929 57444694891736883939026947)
        ·
          refine ⟨86167042337605325908540421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57444694891736883939026947 86167042337605325908540421)
          ·
            refine ⟨16156320438300998607851329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86167042337605325908540421 16156320438300998607851329)
            ·
              refine ⟨12117240328725748955888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16156320438300998607851329 12117240328725748955888497)
              ·
                refine ⟨9087930246544311716916373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12117240328725748955888497 9087930246544311716916373)
                ·
                  refine ⟨425996730306764611730455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9087930246544311716916373 425996730306764611730455)
                  ·
                    rfl

theorem cell23_7466631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 6].length) (baseStart_7466631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466631 prefixEnd_7466631 := by exact prefixLift 7466631
  have htrace : WordTrace (prefixWord ++ tailWord_7466631) baseStart_7466631 baseEnd_7466631 := by
    simpa [prefixWord, tailWord_7466631, baseEnd_7466631] using wordTrace_append hprefix tailTrace_7466631
  have hstable : (prefixWord ++ tailWord_7466631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466631).length < 2 ^ (prefixWord ++ tailWord_7466631).sum := by decide
  have hdescent : baseEnd_7466631 < baseStart_7466631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466675 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 1, 1, 3]
def baseStart_7466675 : Nat := 118140960795 + 7466675 * 2 ^ 59
def prefixEnd_7466675 : Nat := 4983230072969 + 3 ^ 40 * 7466675 * 2
def baseEnd_7466675 : Nat := 3833993165909679333423893

theorem tailTrace_7466675 : CollatzResearch.WordTrace tailWord_7466675 prefixEnd_7466675 3833993165909679333423893 := by
  unfold tailWord_7466675
  simp only [CollatzResearch.WordTrace]
  refine ⟨272332010224519156410729479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181554673483012770940486319 272332010224519156410729479)
  ·
    refine ⟨408498015336778734616094219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272332010224519156410729479 408498015336778734616094219)
    ·
      refine ⟨612747023005168101924141329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408498015336778734616094219 612747023005168101924141329)
      ·
        refine ⟨459560267253876076443105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612747023005168101924141329 459560267253876076443105997)
        ·
          refine ⟨172335100220203528666164749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459560267253876076443105997 172335100220203528666164749)
          ·
            refine ⟨64625662582576323249811781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172335100220203528666164749 64625662582576323249811781)
            ·
              refine ⟨12117311734233060609339709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64625662582576323249811781 12117311734233060609339709)
              ·
                refine ⟨4543991900337397728502391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12117311734233060609339709 4543991900337397728502391)
                ·
                  refine ⟨6815987850506096592753587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4543991900337397728502391 6815987850506096592753587)
                  ·
                    refine ⟨10223981775759144889130381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6815987850506096592753587 10223981775759144889130381)
                    ·
                      refine ⟨3833993165909679333423893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10223981775759144889130381 3833993165909679333423893)
                      ·
                        rfl

theorem cell23_7466675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 1, 1, 3].length) (baseStart_7466675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466675 prefixEnd_7466675 := by exact prefixLift 7466675
  have htrace : WordTrace (prefixWord ++ tailWord_7466675) baseStart_7466675 baseEnd_7466675 := by
    simpa [prefixWord, tailWord_7466675, baseEnd_7466675] using wordTrace_append hprefix tailTrace_7466675
  have hstable : (prefixWord ++ tailWord_7466675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466675).length < 2 ^ (prefixWord ++ tailWord_7466675).sum := by decide
  have hdescent : baseEnd_7466675 < baseStart_7466675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466708 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_7466708 : Nat := 118140960795 + 7466708 * 2 ^ 59
def prefixEnd_7466708 : Nat := 4983230072969 + 3 ^ 40 * 7466708 * 2
def baseEnd_7466708 : Nat := 1278003370257092568103747

theorem tailTrace_7466708 : CollatzResearch.WordTrace tailWord_7466708 prefixEnd_7466708 1278003370257092568103747 := by
  unfold tailWord_7466708
  simp only [CollatzResearch.WordTrace]
  refine ⟨136166606916699801523340389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181555475888933068697787185 136166606916699801523340389)
  ·
    refine ⟨25531238796881212785626323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136166606916699801523340389 25531238796881212785626323)
    ·
      refine ⟨38296858195321819178439485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25531238796881212785626323 38296858195321819178439485)
      ·
        refine ⟨14361321823245682191914807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38296858195321819178439485 14361321823245682191914807)
        ·
          refine ⟨21541982734868523287872211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14361321823245682191914807 21541982734868523287872211)
          ·
            refine ⟨32312974102302784931808317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21541982734868523287872211 32312974102302784931808317)
            ·
              refine ⟨12117365288363544349428119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32312974102302784931808317 12117365288363544349428119)
              ·
                refine ⟨18176047932545316524142179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117365288363544349428119 18176047932545316524142179)
                ·
                  refine ⟨27264071898817974786213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176047932545316524142179 27264071898817974786213269)
                  ·
                    refine ⟨1278003370257092568103747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27264071898817974786213269 1278003370257092568103747)
                    ·
                      rfl

theorem cell23_7466708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_7466708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466708 prefixEnd_7466708 := by exact prefixLift 7466708
  have htrace : WordTrace (prefixWord ++ tailWord_7466708) baseStart_7466708 baseEnd_7466708 := by
    simpa [prefixWord, tailWord_7466708, baseEnd_7466708] using wordTrace_append hprefix tailTrace_7466708
  have hstable : (prefixWord ++ tailWord_7466708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466708).length < 2 ^ (prefixWord ++ tailWord_7466708).sum := by decide
  have hdescent : baseEnd_7466708 < baseStart_7466708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466721 : List Nat := [1, 2, 3, 1, 5, 1, 1, 9]
def baseStart_7466721 : Nat := 118140960795 + 7466721 * 2 ^ 59
def prefixEnd_7466721 : Nat := 4983230072969 + 3 ^ 40 * 7466721 * 2
def baseEnd_7466721 : Nat := 142000621704436524201803

theorem tailTrace_7466721 : CollatzResearch.WordTrace tailWord_7466721 prefixEnd_7466721 142000621704436524201803 := by
  unfold tailWord_7466721
  simp only [CollatzResearch.WordTrace]
  refine ⟨272333687982352506266904017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181555791988235004177936011 272333687982352506266904017)
  ·
    refine ⟨204250265986764379700178013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272333687982352506266904017 204250265986764379700178013)
    ·
      refine ⟨76593849745036642387566755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204250265986764379700178013 76593849745036642387566755)
      ·
        refine ⟨114890774617554963581350133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76593849745036642387566755 114890774617554963581350133)
        ·
          refine ⟨10771010120395777835751575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114890774617554963581350133 10771010120395777835751575)
          ·
            refine ⟨16156515180593666753627363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771010120395777835751575 16156515180593666753627363)
            ·
              refine ⟨24234772770890500130441045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156515180593666753627363 24234772770890500130441045)
              ·
                refine ⟨142000621704436524201803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24234772770890500130441045 142000621704436524201803)
                ·
                  rfl

theorem cell23_7466721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 9].length) (baseStart_7466721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466721 prefixEnd_7466721 := by exact prefixLift 7466721
  have htrace : WordTrace (prefixWord ++ tailWord_7466721) baseStart_7466721 baseEnd_7466721 := by
    simpa [prefixWord, tailWord_7466721, baseEnd_7466721] using wordTrace_append hprefix tailTrace_7466721
  have hstable : (prefixWord ++ tailWord_7466721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466721).length < 2 ^ (prefixWord ++ tailWord_7466721).sum := by decide
  have hdescent : baseEnd_7466721 < baseStart_7466721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466731 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3]
def baseStart_7466731 : Nat := 118140960795 + 7466731 * 2 ^ 59
def prefixEnd_7466731 : Nat := 4983230072969 + 3 ^ 40 * 7466731 * 2
def baseEnd_7466731 : Nat := 3834021920826331114323635

theorem tailTrace_7466731 : CollatzResearch.WordTrace tailWord_7466731 prefixEnd_7466731 3834021920826331114323635 := by
  unfold tailWord_7466731
  simp only [CollatzResearch.WordTrace]
  refine ⟨272334052712316277974768047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181556035141544185316512031 272334052712316277974768047)
  ·
    refine ⟨408501079068474416962152071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272334052712316277974768047 408501079068474416962152071)
    ·
      refine ⟨612751618602711625443228107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408501079068474416962152071 612751618602711625443228107)
      ·
        refine ⟨919127427904067438164842161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612751618602711625443228107 919127427904067438164842161)
        ·
          refine ⟨689345570928050578623631621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919127427904067438164842161 689345570928050578623631621)
          ·
            refine ⟨129252294549009483491930929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689345570928050578623631621 129252294549009483491930929)
            ·
              refine ⟨96939220911757112618948197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129252294549009483491930929 96939220911757112618948197)
              ·
                refine ⟨18176103920954458616052787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96939220911757112618948197 18176103920954458616052787)
                ·
                  refine ⟨27264155881431687924079181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176103920954458616052787 27264155881431687924079181)
                  ·
                    refine ⟨10224058455536882971529693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27264155881431687924079181 10224058455536882971529693)
                    ·
                      refine ⟨3834021920826331114323635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224058455536882971529693 3834021920826331114323635)
                      ·
                        rfl

theorem cell23_7466731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 3].length) (baseStart_7466731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466731 prefixEnd_7466731 := by exact prefixLift 7466731
  have htrace : WordTrace (prefixWord ++ tailWord_7466731) baseStart_7466731 baseEnd_7466731 := by
    simpa [prefixWord, tailWord_7466731, baseEnd_7466731] using wordTrace_append hprefix tailTrace_7466731
  have hstable : (prefixWord ++ tailWord_7466731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466731).length < 2 ^ (prefixWord ++ tailWord_7466731).sum := by decide
  have hdescent : baseEnd_7466731 < baseStart_7466731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466732 : List Nat := [2, 2, 1, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_7466732 : Nat := 118140960795 + 7466732 * 2 ^ 59
def prefixEnd_7466732 : Nat := 4983230072969 + 3 ^ 40 * 7466732 * 2
def baseEnd_7466732 : Nat := 3834022434306985610411131

theorem tailTrace_7466732 : CollatzResearch.WordTrace tailWord_7466732 prefixEnd_7466732 3834022434306985610411131 := by
  unfold tailWord_7466732
  simp only [CollatzResearch.WordTrace]
  refine ⟨136167044592656327572777225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181556059456875103430369633 136167044592656327572777225)
  ·
    refine ⟨102125283444492245679582919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136167044592656327572777225 102125283444492245679582919)
    ·
      refine ⟨153187925166738368519374379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102125283444492245679582919 153187925166738368519374379)
      ·
        refine ⟨229781887750107552779061569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153187925166738368519374379 229781887750107552779061569)
        ·
          refine ⟨172336415812580664584296177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229781887750107552779061569 172336415812580664584296177)
          ·
            refine ⟨129252311859435498438222133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172336415812580664584296177 129252311859435498438222133)
            ·
              refine ⟨12117404236822077978583325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129252311859435498438222133 12117404236822077978583325)
              ·
                refine ⟨4544026588808279241968747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12117404236822077978583325 4544026588808279241968747)
                ·
                  refine ⟨6816039883212418862953121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544026588808279241968747 6816039883212418862953121)
                  ·
                    refine ⟨5112029912409314147214841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6816039883212418862953121 5112029912409314147214841)
                    ·
                      refine ⟨3834022434306985610411131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112029912409314147214841 3834022434306985610411131)
                      ·
                        rfl

theorem cell23_7466732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_7466732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466732 prefixEnd_7466732 := by exact prefixLift 7466732
  have htrace : WordTrace (prefixWord ++ tailWord_7466732) baseStart_7466732 baseEnd_7466732 := by
    simpa [prefixWord, tailWord_7466732, baseEnd_7466732] using wordTrace_append hprefix tailTrace_7466732
  have hstable : (prefixWord ++ tailWord_7466732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466732).length < 2 ^ (prefixWord ++ tailWord_7466732).sum := by decide
  have hdescent : baseEnd_7466732 < baseStart_7466732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466748 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_7466748 : Nat := 118140960795 + 7466748 * 2 ^ 59
def prefixEnd_7466748 : Nat := 4983230072969 + 3 ^ 40 * 7466748 * 2
def baseEnd_7466748 : Nat := 3834030649997457547811057

theorem tailTrace_7466748 : CollatzResearch.WordTrace tailWord_7466748 prefixEnd_7466748 3834030649997457547811057 := by
  unfold tailWord_7466748
  simp only [CollatzResearch.WordTrace]
  refine ⟨136167336376627344939068449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181556448502169793252091265 136167336376627344939068449)
  ·
    refine ⟨102125502282470508704301337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136167336376627344939068449 102125502282470508704301337)
    ·
      refine ⟨76594126711852881528226003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102125502282470508704301337 76594126711852881528226003)
      ·
        refine ⟨114891190067779322292339005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76594126711852881528226003 114891190067779322292339005)
        ·
          refine ⟨43084196275417245859627127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114891190067779322292339005 43084196275417245859627127)
          ·
            refine ⟨64626294413125868789440691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43084196275417245859627127 64626294413125868789440691)
            ·
              refine ⟨96939441619688803184161037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64626294413125868789440691 96939441619688803184161037)
              ·
                refine ⟨36352290607383301194060389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96939441619688803184161037 36352290607383301194060389)
                ·
                  refine ⟨6816054488884368973886323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36352290607383301194060389 6816054488884368973886323)
                  ·
                    refine ⟨10224081733326553460829485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6816054488884368973886323 10224081733326553460829485)
                    ·
                      refine ⟨3834030649997457547811057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224081733326553460829485 3834030649997457547811057)
                      ·
                        rfl

theorem cell23_7466748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_7466748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466748 prefixEnd_7466748 := by exact prefixLift 7466748
  have htrace : WordTrace (prefixWord ++ tailWord_7466748) baseStart_7466748 baseEnd_7466748 := by
    simpa [prefixWord, tailWord_7466748, baseEnd_7466748] using wordTrace_append hprefix tailTrace_7466748
  have hstable : (prefixWord ++ tailWord_7466748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466748).length < 2 ^ (prefixWord ++ tailWord_7466748).sum := by decide
  have hdescent : baseEnd_7466748 < baseStart_7466748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466759 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 2, 4]
def baseStart_7466759 : Nat := 118140960795 + 7466759 * 2 ^ 59
def prefixEnd_7466759 : Nat := 4983230072969 + 3 ^ 40 * 7466759 * 2
def baseEnd_7466759 : Nat := 1278012099428219001591169

theorem tailTrace_7466759 : CollatzResearch.WordTrace tailWord_7466759 prefixEnd_7466759 1278012099428219001591169 := by
  unfold tailWord_7466759
  simp only [CollatzResearch.WordTrace]
  refine ⟨272335073956214838756787331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181556715970809892504524887 272335073956214838756787331)
  ·
    refine ⟨408502610934322258135180997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272335073956214838756787331 408502610934322258135180997)
    ·
      refine ⟨76594239550185423400346437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408502610934322258135180997 76594239550185423400346437)
      ·
        refine ⟨14361419915659766887564957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76594239550185423400346437 14361419915659766887564957)
        ·
          refine ⟨5385532468372412582836859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14361419915659766887564957 5385532468372412582836859)
          ·
            refine ⟨8078298702558618874255289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385532468372412582836859 8078298702558618874255289)
            ·
              refine ⟨6058724026918964155691467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078298702558618874255289 6058724026918964155691467)
              ·
                refine ⟨9088086040378446233537201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6058724026918964155691467 9088086040378446233537201)
                ·
                  refine ⟨6816064530283834675152901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9088086040378446233537201 6816064530283834675152901)
                  ·
                    refine ⟨1278012099428219001591169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816064530283834675152901 1278012099428219001591169)
                    ·
                      rfl

theorem cell23_7466759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_7466759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466759 prefixEnd_7466759 := by exact prefixLift 7466759
  have htrace : WordTrace (prefixWord ++ tailWord_7466759) baseStart_7466759 baseEnd_7466759 := by
    simpa [prefixWord, tailWord_7466759, baseEnd_7466759] using wordTrace_append hprefix tailTrace_7466759
  have hstable : (prefixWord ++ tailWord_7466759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466759).length < 2 ^ (prefixWord ++ tailWord_7466759).sum := by decide
  have hdescent : baseEnd_7466759 < baseStart_7466759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466775 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7466775 : Nat := 118140960795 + 7466775 * 2 ^ 59
def prefixEnd_7466775 : Nat := 4983230072969 + 3 ^ 40 * 7466775 * 2
def baseEnd_7466775 : Nat := 3834044513975128942173433

theorem tailTrace_7466775 : CollatzResearch.WordTrace tailWord_7466775 prefixEnd_7466775 3834044513975128942173433 := by
  unfold tailWord_7466775
  simp only [CollatzResearch.WordTrace]
  refine ⟨272335657524156873489369779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181557105016104582326246519 272335657524156873489369779)
  ·
    refine ⟨408503486286235310234054669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272335657524156873489369779 408503486286235310234054669)
    ·
      refine ⟨153188807357338241337770501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408503486286235310234054669 153188807357338241337770501)
      ·
        refine ⟨28722901379500920250831969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153188807357338241337770501 28722901379500920250831969)
        ·
          refine ⟨21542176034625690188123977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28722901379500920250831969 21542176034625690188123977)
          ·
            refine ⟨16156632025969267641092983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21542176034625690188123977 16156632025969267641092983)
            ·
              refine ⟨24234948038953901461639475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156632025969267641092983 24234948038953901461639475)
              ·
                refine ⟨36352422058430852192459213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24234948038953901461639475 36352422058430852192459213)
                ·
                  refine ⟨13632158271911569572172205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36352422058430852192459213 13632158271911569572172205)
                  ·
                    refine ⟨5112059351966838589564577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13632158271911569572172205 5112059351966838589564577)
                    ·
                      refine ⟨3834044513975128942173433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112059351966838589564577 3834044513975128942173433)
                      ·
                        rfl

theorem cell23_7466775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7466775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466775 prefixEnd_7466775 := by exact prefixLift 7466775
  have htrace : WordTrace (prefixWord ++ tailWord_7466775) baseStart_7466775 baseEnd_7466775 := by
    simpa [prefixWord, tailWord_7466775, baseEnd_7466775] using wordTrace_append hprefix tailTrace_7466775
  have hstable : (prefixWord ++ tailWord_7466775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466775).length < 2 ^ (prefixWord ++ tailWord_7466775).sum := by decide
  have hdescent : baseEnd_7466775 < baseStart_7466775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466828 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 7]
def baseStart_7466828 : Nat := 118140960795 + 7466828 * 2 ^ 59
def prefixEnd_7466828 : Nat := 4983230072969 + 3 ^ 40 * 7466828 * 2
def baseEnd_7466828 : Nat := 426007969827757470534521

theorem tailTrace_7466828 : CollatzResearch.WordTrace tailWord_7466828 prefixEnd_7466828 426007969827757470534521 := by
  unfold tailWord_7466828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136168795296482431770524569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181558393728643242360699425 136168795296482431770524569)
  ·
    refine ⟨102126596472361823827893427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136168795296482431770524569 102126596472361823827893427)
    ·
      refine ⟨153189894708542735741840141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102126596472361823827893427 153189894708542735741840141)
      ·
        refine ⟨57446210515703525903190053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153189894708542735741840141 57446210515703525903190053)
        ·
          refine ⟨10771164471694411106848135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57446210515703525903190053 10771164471694411106848135)
          ·
            refine ⟨16156746707541616660272203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771164471694411106848135 16156746707541616660272203)
            ·
              refine ⟨24235120061312424990408305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16156746707541616660272203 24235120061312424990408305)
              ·
                refine ⟨18176340045984318742806229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24235120061312424990408305 18176340045984318742806229)
                ·
                  refine ⟨426007969827757470534521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18176340045984318742806229 426007969827757470534521)
                  ·
                    rfl

theorem cell23_7466828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_7466828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466828 prefixEnd_7466828 := by exact prefixLift 7466828
  have htrace : WordTrace (prefixWord ++ tailWord_7466828) baseStart_7466828 baseEnd_7466828 := by
    simpa [prefixWord, tailWord_7466828, baseEnd_7466828] using wordTrace_append hprefix tailTrace_7466828
  have hstable : (prefixWord ++ tailWord_7466828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466828).length < 2 ^ (prefixWord ++ tailWord_7466828).sum := by decide
  have hdescent : baseEnd_7466828 < baseStart_7466828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466841 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_7466841 : Nat := 118140960795 + 7466841 * 2 ^ 59
def prefixEnd_7466841 : Nat := 4983230072969 + 3 ^ 40 * 7466841 * 2
def baseEnd_7466841 : Nat := 1278026134566108561316043

theorem tailTrace_7466841 : CollatzResearch.WordTrace tailWord_7466841 prefixEnd_7466841 1278026134566108561316043 := by
  unfold tailWord_7466841
  simp only [CollatzResearch.WordTrace]
  refine ⟨272338064741917766761272377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181558709827945177840848251 272338064741917766761272377)
  ·
    refine ⟨204253548556438325070954283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272338064741917766761272377 204253548556438325070954283)
    ·
      refine ⟨306380322834657487606431425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204253548556438325070954283 306380322834657487606431425)
      ·
        refine ⟨229785242125993115704823569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306380322834657487606431425 229785242125993115704823569)
        ·
          refine ⟨172338931594494836778617677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229785242125993115704823569 172338931594494836778617677)
          ·
            refine ⟨64627099347935563791981629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172338931594494836778617677 64627099347935563791981629)
            ·
              refine ⟨24235162255475836421993111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64627099347935563791981629 24235162255475836421993111)
              ·
                refine ⟨36352743383213754632989667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24235162255475836421993111 36352743383213754632989667)
                ·
                  refine ⟨54529115074820631949484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36352743383213754632989667 54529115074820631949484501)
                  ·
                    refine ⟨1278026134566108561316043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54529115074820631949484501 1278026134566108561316043)
                    ·
                      rfl

theorem cell23_7466841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_7466841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466841 prefixEnd_7466841 := by exact prefixLift 7466841
  have htrace : WordTrace (prefixWord ++ tailWord_7466841) baseStart_7466841 baseEnd_7466841 := by
    simpa [prefixWord, tailWord_7466841, baseEnd_7466841] using wordTrace_append hprefix tailTrace_7466841
  have hstable : (prefixWord ++ tailWord_7466841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466841).length < 2 ^ (prefixWord ++ tailWord_7466841).sum := by decide
  have hdescent : baseEnd_7466841 < baseStart_7466841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466891 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4]
def baseStart_7466891 : Nat := 118140960795 + 7466891 * 2 ^ 59
def prefixEnd_7466891 : Nat := 4983230072969 + 3 ^ 40 * 7466891 * 2
def baseEnd_7466891 : Nat := 3834104077731050488322899

theorem tailTrace_7466891 : CollatzResearch.WordTrace tailWord_7466891 prefixEnd_7466891 3834104077731050488322899 := by
  unfold tailWord_7466891
  simp only [CollatzResearch.WordTrace]
  refine ⟨272339888391736625300592527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181559925594491083533728351 272339888391736625300592527)
  ·
    refine ⟨408509832587604937950888791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272339888391736625300592527 408509832587604937950888791)
    ·
      refine ⟨612764748881407406926333187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408509832587604937950888791 612764748881407406926333187)
      ·
        refine ⟨919147123322111110389499781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612764748881407406926333187 919147123322111110389499781)
        ·
          refine ⟨172340085622895833198031209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 919147123322111110389499781 172340085622895833198031209)
          ·
            refine ⟨129255064217171874898523407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172340085622895833198031209 129255064217171874898523407)
            ·
              refine ⟨193882596325757812347785111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129255064217171874898523407 193882596325757812347785111)
              ·
                refine ⟨290823894488636718521677667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193882596325757812347785111 290823894488636718521677667)
                ·
                  refine ⟨436235841732955077782516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290823894488636718521677667 436235841732955077782516501)
                  ·
                    refine ⟨20448555081232269271055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 436235841732955077782516501 20448555081232269271055461)
                    ·
                      refine ⟨3834104077731050488322899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20448555081232269271055461 3834104077731050488322899)
                      ·
                        rfl

theorem cell23_7466891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_7466891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466891 prefixEnd_7466891 := by exact prefixLift 7466891
  have htrace : WordTrace (prefixWord ++ tailWord_7466891) baseStart_7466891 baseEnd_7466891 := by
    simpa [prefixWord, tailWord_7466891, baseEnd_7466891] using wordTrace_append hprefix tailTrace_7466891
  have hstable : (prefixWord ++ tailWord_7466891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466891).length < 2 ^ (prefixWord ++ tailWord_7466891).sum := by decide
  have hdescent : baseEnd_7466891 < baseStart_7466891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466901 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 10]
def baseStart_7466901 : Nat := 118140960795 + 7466901 * 2 ^ 59
def prefixEnd_7466901 : Nat := 4983230072969 + 3 ^ 40 * 7466901 * 2
def baseEnd_7466901 : Nat := 426012134726399494355317

theorem tailTrace_7466901 : CollatzResearch.WordTrace tailWord_7466901 prefixEnd_7466901 426012134726399494355317 := by
  unfold tailWord_7466901
  simp only [CollatzResearch.WordTrace]
  refine ⟨272340253121700397008456557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181560168747800264672304371 272340253121700397008456557)
  ·
    refine ⟨102127594920637648878171209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272340253121700397008456557 102127594920637648878171209)
    ·
      refine ⟨76595696190478236658628407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102127594920637648878171209 76595696190478236658628407)
      ·
        refine ⟨114893544285717354987942611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76595696190478236658628407 114893544285717354987942611)
        ·
          refine ⟨172340316428576032481913917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114893544285717354987942611 172340316428576032481913917)
          ·
            refine ⟨64627618660716012180717719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172340316428576032481913917 64627618660716012180717719)
            ·
              refine ⟨96941427991074018271076579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64627618660716012180717719 96941427991074018271076579)
              ·
                refine ⟨145412141986611027406614869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96941427991074018271076579 145412141986611027406614869)
                ·
                  refine ⟨426012134726399494355317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145412141986611027406614869 426012134726399494355317)
                  ·
                    rfl

theorem cell23_7466901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_7466901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466901 prefixEnd_7466901 := by exact prefixLift 7466901
  have htrace : WordTrace (prefixWord ++ tailWord_7466901) baseStart_7466901 baseEnd_7466901 := by
    simpa [prefixWord, tailWord_7466901, baseEnd_7466901] using wordTrace_append hprefix tailTrace_7466901
  have hstable : (prefixWord ++ tailWord_7466901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466901).length < 2 ^ (prefixWord ++ tailWord_7466901).sum := by decide
  have hdescent : baseEnd_7466901 < baseStart_7466901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466921 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_7466921 : Nat := 118140960795 + 7466921 * 2 ^ 59
def prefixEnd_7466921 : Nat := 4983230072969 + 3 ^ 40 * 7466921 * 2
def baseEnd_7466921 : Nat := 3834119482150685370947761

theorem tailTrace_7466921 : CollatzResearch.WordTrace tailWord_7466921 prefixEnd_7466921 3834119482150685370947761 := by
  unfold tailWord_7466921
  simp only [CollatzResearch.WordTrace]
  refine ⟨272340982581627940424184617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181560655054418626949456411 272340982581627940424184617)
  ·
    refine ⟨204255736936220955318138463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272340982581627940424184617 204255736936220955318138463)
    ·
      refine ⟨306383605404331432977207695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204255736936220955318138463 306383605404331432977207695)
      ·
        refine ⟨459575408106497149465811543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306383605404331432977207695 459575408106497149465811543)
        ·
          refine ⟨689363112159745724198717315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459575408106497149465811543 689363112159745724198717315)
          ·
            refine ⟨1034044668239618586298075973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689363112159745724198717315 1034044668239618586298075973)
            ·
              refine ⟨193883375294928484930889245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1034044668239618586298075973 193883375294928484930889245)
              ·
                refine ⟨72706265735598181849083467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193883375294928484930889245 72706265735598181849083467)
                ·
                  refine ⟨109059398603397272773625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72706265735598181849083467 109059398603397272773625201)
                  ·
                    refine ⟨81794548952547954580218901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109059398603397272773625201 81794548952547954580218901)
                    ·
                      refine ⟨3834119482150685370947761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81794548952547954580218901 3834119482150685370947761)
                      ·
                        rfl

theorem cell23_7466921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_7466921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466921 prefixEnd_7466921 := by exact prefixLift 7466921
  have htrace : WordTrace (prefixWord ++ tailWord_7466921) baseStart_7466921 baseEnd_7466921 := by
    simpa [prefixWord, tailWord_7466921, baseEnd_7466921] using wordTrace_append hprefix tailTrace_7466921
  have hstable : (prefixWord ++ tailWord_7466921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466921).length < 2 ^ (prefixWord ++ tailWord_7466921).sum := by decide
  have hdescent : baseEnd_7466921 < baseStart_7466921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466973 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7466973 : Nat := 118140960795 + 7466973 * 2 ^ 59
def prefixEnd_7466973 : Nat := 4983230072969 + 3 ^ 40 * 7466973 * 2
def baseEnd_7466973 : Nat := 1278048727714906389165841

theorem tailTrace_7466973 : CollatzResearch.WordTrace tailWord_7466973 prefixEnd_7466973 1278048727714906389165841 := by
  unfold tailWord_7466973
  simp only [CollatzResearch.WordTrace]
  refine ⟨272342879177439553305077573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181561919451626368870051715 272342879177439553305077573)
  ·
    refine ⟨51064289845769916244702045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272342879177439553305077573 51064289845769916244702045)
    ·
      refine ⟨19149108692163718591763267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51064289845769916244702045 19149108692163718591763267)
      ·
        refine ⟨28723663038245577887644901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19149108692163718591763267 28723663038245577887644901)
        ·
          refine ⟨5385686819671045853933419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28723663038245577887644901 5385686819671045853933419)
          ·
            refine ⟨8078530229506568780900129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385686819671045853933419 8078530229506568780900129)
            ·
              refine ⟨6058897672129926585675097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078530229506568780900129 6058897672129926585675097)
              ·
                refine ⟨4544173254097444939256323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6058897672129926585675097 4544173254097444939256323)
                ·
                  refine ⟨6816259881146167408884485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544173254097444939256323 6816259881146167408884485)
                  ·
                    refine ⟨1278048727714906389165841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816259881146167408884485 1278048727714906389165841)
                    ·
                      rfl

theorem cell23_7466973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7466973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466973 prefixEnd_7466973 := by exact prefixLift 7466973
  have htrace : WordTrace (prefixWord ++ tailWord_7466973) baseStart_7466973 baseEnd_7466973 := by
    simpa [prefixWord, tailWord_7466973, baseEnd_7466973] using wordTrace_append hprefix tailTrace_7466973
  have hstable : (prefixWord ++ tailWord_7466973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466973).length < 2 ^ (prefixWord ++ tailWord_7466973).sum := by decide
  have hdescent : baseEnd_7466973 < baseStart_7466973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466979 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7466979 : Nat := 118140960795 + 7466979 * 2 ^ 59
def prefixEnd_7466979 : Nat := 4983230072969 + 3 ^ 40 * 7466979 * 2
def baseEnd_7466979 : Nat := 3834149264028646144022495

theorem tailTrace_7466979 : CollatzResearch.WordTrace tailWord_7466979 prefixEnd_7466979 3834149264028646144022495 := by
  unfold tailWord_7466979
  simp only [CollatzResearch.WordTrace]
  refine ⟨272343098015417816329795991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181562065343611877553197327 272343098015417816329795991)
  ·
    refine ⟨408514647023126724494693987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272343098015417816329795991 408514647023126724494693987)
    ·
      refine ⟨612771970534690086742040981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408514647023126724494693987 612771970534690086742040981)
      ·
        refine ⟨28723686118813597816033171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 612771970534690086742040981 28723686118813597816033171)
        ·
          refine ⟨43085529178220396724049757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28723686118813597816033171 43085529178220396724049757)
          ·
            refine ⟨16157073441832648771518659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43085529178220396724049757 16157073441832648771518659)
            ·
              refine ⟨24235610162748973157277989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16157073441832648771518659 24235610162748973157277989)
              ·
                refine ⟨4544176905515432466989623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24235610162748973157277989 4544176905515432466989623)
                ·
                  refine ⟨6816265358273148700484435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544176905515432466989623 6816265358273148700484435)
                  ·
                    refine ⟨10224398037409723050726653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6816265358273148700484435 10224398037409723050726653)
                    ·
                      refine ⟨3834149264028646144022495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224398037409723050726653 3834149264028646144022495)
                      ·
                        rfl

theorem cell23_7466979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7466979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466979 prefixEnd_7466979 := by exact prefixLift 7466979
  have htrace : WordTrace (prefixWord ++ tailWord_7466979) baseStart_7466979 baseEnd_7466979 := by
    simpa [prefixWord, tailWord_7466979, baseEnd_7466979] using wordTrace_append hprefix tailTrace_7466979
  have hstable : (prefixWord ++ tailWord_7466979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466979).length < 2 ^ (prefixWord ++ tailWord_7466979).sum := by decide
  have hdescent : baseEnd_7466979 < baseStart_7466979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7466988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_7466988 : Nat := 118140960795 + 7466988 * 2 ^ 59
def prefixEnd_7466988 : Nat := 4983230072969 + 3 ^ 40 * 7466988 * 2
def baseEnd_7466988 : Nat := 3834153885354536608809953

theorem tailTrace_7466988 : CollatzResearch.WordTrace tailWord_7466988 prefixEnd_7466988 3834153885354536608809953 := by
  unfold tailWord_7466988
  simp only [CollatzResearch.WordTrace]
  refine ⟨136171713136192605433436809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181562284181590140577915745 136171713136192605433436809)
  ·
    refine ⟨102128784852144454075077607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136171713136192605433436809 102128784852144454075077607)
    ·
      refine ⟨153193177278216681112616411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102128784852144454075077607 153193177278216681112616411)
      ·
        refine ⟨229789765917325021668924617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153193177278216681112616411 229789765917325021668924617)
        ·
          refine ⟨172342324437993766251693463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229789765917325021668924617 172342324437993766251693463)
          ·
            refine ⟨258513486656990649377540195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172342324437993766251693463 258513486656990649377540195)
            ·
              refine ⟨387770229985485974066310293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258513486656990649377540195 387770229985485974066310293)
              ·
                refine ⟨18176729530569655034358295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 387770229985485974066310293 18176729530569655034358295)
                ·
                  refine ⟨27265094295854482551537443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176729530569655034358295 27265094295854482551537443)
                  ·
                    refine ⟨40897641443781723827306165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27265094295854482551537443 40897641443781723827306165)
                    ·
                      refine ⟨3834153885354536608809953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40897641443781723827306165 3834153885354536608809953)
                      ·
                        rfl

theorem cell23_7466988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_7466988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7466988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7466988 prefixEnd_7466988 := by exact prefixLift 7466988
  have htrace : WordTrace (prefixWord ++ tailWord_7466988) baseStart_7466988 baseEnd_7466988 := by
    simpa [prefixWord, tailWord_7466988, baseEnd_7466988] using wordTrace_append hprefix tailTrace_7466988
  have hstable : (prefixWord ++ tailWord_7466988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7466988).length < 2 ^ (prefixWord ++ tailWord_7466988).sum := by decide
  have hdescent : baseEnd_7466988 < baseStart_7466988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7466988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467005 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_7467005 : Nat := 118140960795 + 7467005 * 2 ^ 59
def prefixEnd_7467005 : Nat := 4983230072969 + 3 ^ 40 * 7467005 * 2
def baseEnd_7467005 : Nat := 3834162614525663042297375

theorem tailTrace_7467005 : CollatzResearch.WordTrace tailWord_7467005 prefixEnd_7467005 3834162614525663042297375 := by
  unfold tailWord_7467005
  simp only [CollatzResearch.WordTrace]
  refine ⟨272344046313323622770242469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181562697542215748513494979 272344046313323622770242469)
  ·
    refine ⟨51064508683748179269420463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272344046313323622770242469 51064508683748179269420463)
    ·
      refine ⟨76596763025622268904130695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51064508683748179269420463 76596763025622268904130695)
      ·
        refine ⟨114895144538433403356196043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76596763025622268904130695 114895144538433403356196043)
        ·
          refine ⟨172342716807650105034294065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114895144538433403356196043 172342716807650105034294065)
          ·
            refine ⟨129257037605737578775720549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172342716807650105034294065 129257037605737578775720549)
            ·
              refine ⟨24235694551075796020447603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129257037605737578775720549 24235694551075796020447603)
              ·
                refine ⟨36353541826613694030671405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24235694551075796020447603 36353541826613694030671405)
                ·
                  refine ⟨13632578184980135261501777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36353541826613694030671405 13632578184980135261501777)
                  ·
                    refine ⟨10224433638735101446126333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13632578184980135261501777 10224433638735101446126333)
                    ·
                      refine ⟨3834162614525663042297375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224433638735101446126333 3834162614525663042297375)
                      ·
                        rfl

theorem cell23_7467005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_7467005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467005 prefixEnd_7467005 := by exact prefixLift 7467005
  have htrace : WordTrace (prefixWord ++ tailWord_7467005) baseStart_7467005 baseEnd_7467005 := by
    simpa [prefixWord, tailWord_7467005, baseEnd_7467005] using wordTrace_append hprefix tailTrace_7467005
  have hstable : (prefixWord ++ tailWord_7467005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467005).length < 2 ^ (prefixWord ++ tailWord_7467005).sum := by decide
  have hdescent : baseEnd_7467005 < baseStart_7467005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467006 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7467006 : Nat := 118140960795 + 7467006 * 2 ^ 59
def prefixEnd_7467006 : Nat := 4983230072969 + 3 ^ 40 * 7467006 * 2
def baseEnd_7467006 : Nat := 3834163128006317538384871

theorem tailTrace_7467006 : CollatzResearch.WordTrace tailWord_7467006 prefixEnd_7467006 3834163128006317538384871 := by
  unfold tailWord_7467006
  simp only [CollatzResearch.WordTrace]
  refine ⟨34043010348289999992628609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181562721857546666627352581 34043010348289999992628609)
  ·
    refine ⟨25532257761217499994471457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34043010348289999992628609 25532257761217499994471457)
    ·
      refine ⟨19149193320913124995853593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25532257761217499994471457 19149193320913124995853593)
      ·
        refine ⟨14361894990684843746890195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19149193320913124995853593 14361894990684843746890195)
        ·
          refine ⟨21542842486027265620335293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14361894990684843746890195 21542842486027265620335293)
          ·
            refine ⟨8078565932260224607625735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21542842486027265620335293 8078565932260224607625735)
            ·
              refine ⟨12117848898390336911438603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078565932260224607625735 12117848898390336911438603)
              ·
                refine ⟨18176773347585505367157905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12117848898390336911438603 18176773347585505367157905)
                ·
                  refine ⟨13632580010689129025368429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18176773347585505367157905 13632580010689129025368429)
                  ·
                    refine ⟨5112217504008423384513161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13632580010689129025368429 5112217504008423384513161)
                    ·
                      refine ⟨3834163128006317538384871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112217504008423384513161 3834163128006317538384871)
                      ·
                        rfl

theorem cell23_7467006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7467006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467006 prefixEnd_7467006 := by exact prefixLift 7467006
  have htrace : WordTrace (prefixWord ++ tailWord_7467006) baseStart_7467006 baseEnd_7467006 := by
    simpa [prefixWord, tailWord_7467006, baseEnd_7467006] using wordTrace_append hprefix tailTrace_7467006
  have hstable : (prefixWord ++ tailWord_7467006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467006).length < 2 ^ (prefixWord ++ tailWord_7467006).sum := by decide
  have hdescent : baseEnd_7467006 < baseStart_7467006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467015 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7467015 : Nat := 118140960795 + 7467015 * 2 ^ 59
def prefixEnd_7467015 : Nat := 4983230072969 + 3 ^ 40 * 7467015 * 2
def baseEnd_7467015 : Nat := 3834167749332208003172329

theorem tailTrace_7467015 : CollatzResearch.WordTrace tailWord_7467015 prefixEnd_7467015 3834167749332208003172329 := by
  unfold tailWord_7467015
  simp only [CollatzResearch.WordTrace]
  refine ⟨272344411043287394478106499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181562940695524929652070999 272344411043287394478106499)
  ·
    refine ⟨408516616564931091717159749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272344411043287394478106499 408516616564931091717159749)
    ·
      refine ⟨76596865605924579696967453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408516616564931091717159749 76596865605924579696967453)
      ·
        refine ⟨28723824602221717386362795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76596865605924579696967453 28723824602221717386362795)
        ·
          refine ⟨43085736903332576079544193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28723824602221717386362795 43085736903332576079544193)
          ·
            refine ⟨32314302677499432059658145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43085736903332576079544193 32314302677499432059658145)
            ·
              refine ⟨24235727008124574044743609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32314302677499432059658145 24235727008124574044743609)
              ·
                refine ⟨18176795256093430533557707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24235727008124574044743609 18176795256093430533557707)
                ·
                  refine ⟨27265192884140145800336561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18176795256093430533557707 27265192884140145800336561)
                  ·
                    refine ⟨20448894663105109350252421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27265192884140145800336561 20448894663105109350252421)
                    ·
                      refine ⟨3834167749332208003172329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20448894663105109350252421 3834167749332208003172329)
                      ·
                        rfl

theorem cell23_7467015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7467015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467015 prefixEnd_7467015 := by exact prefixLift 7467015
  have htrace : WordTrace (prefixWord ++ tailWord_7467015) baseStart_7467015 baseEnd_7467015 := by
    simpa [prefixWord, tailWord_7467015, baseEnd_7467015] using wordTrace_append hprefix tailTrace_7467015
  have hstable : (prefixWord ++ tailWord_7467015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467015).length < 2 ^ (prefixWord ++ tailWord_7467015).sum := by decide
  have hdescent : baseEnd_7467015 < baseStart_7467015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467022 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7467022 : Nat := 118140960795 + 7467022 * 2 ^ 59
def prefixEnd_7467022 : Nat := 4983230072969 + 3 ^ 40 * 7467022 * 2
def baseEnd_7467022 : Nat := 3834171343696789475784797

theorem tailTrace_7467022 : CollatzResearch.WordTrace tailWord_7467022 prefixEnd_7467022 3834171343696789475784797 := by
  unfold tailWord_7467022
  simp only [CollatzResearch.WordTrace]
  refine ⟨34043083294282754334201415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181563110902841356449074213 34043083294282754334201415)
  ·
    refine ⟨51064624941424131501302123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34043083294282754334201415 51064624941424131501302123)
    ·
      refine ⟨76596937412136197251953185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51064624941424131501302123 76596937412136197251953185)
      ·
        refine ⟨57447703059102147938964889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76596937412136197251953185 57447703059102147938964889)
        ·
          refine ⟨43085777294326610954223667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57447703059102147938964889 43085777294326610954223667)
          ·
            refine ⟨64628665941489916431335501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43085777294326610954223667 64628665941489916431335501)
            ·
              refine ⟨24235749728058718661750813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64628665941489916431335501 24235749728058718661750813)
              ·
                refine ⟨9088406148022019498156555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24235749728058718661750813 9088406148022019498156555)
                ·
                  refine ⟨13632609222033029247234833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9088406148022019498156555 13632609222033029247234833)
                  ·
                    refine ⟨10224456916524771935426125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13632609222033029247234833 10224456916524771935426125)
                    ·
                      refine ⟨3834171343696789475784797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224456916524771935426125 3834171343696789475784797)
                      ·
                        rfl

theorem cell23_7467022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7467022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467022 prefixEnd_7467022 := by exact prefixLift 7467022
  have htrace : WordTrace (prefixWord ++ tailWord_7467022) baseStart_7467022 baseEnd_7467022 := by
    simpa [prefixWord, tailWord_7467022, baseEnd_7467022] using wordTrace_append hprefix tailTrace_7467022
  have hstable : (prefixWord ++ tailWord_7467022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467022).length < 2 ^ (prefixWord ++ tailWord_7467022).sum := by decide
  have hdescent : baseEnd_7467022 < baseStart_7467022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467029 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_7467029 : Nat := 118140960795 + 7467029 * 2 ^ 59
def prefixEnd_7467029 : Nat := 4983230072969 + 3 ^ 40 * 7467029 * 2
def baseEnd_7467029 : Nat := 1278058312687123649465755

theorem tailTrace_7467029 : CollatzResearch.WordTrace tailWord_7467029 prefixEnd_7467029 1278058312687123649465755 := by
  unfold tailWord_7467029
  simp only [CollatzResearch.WordTrace]
  refine ⟨272344921665236674869116141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181563281110157783246077427 272344921665236674869116141)
  ·
    refine ⟨102129345624463753075918553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272344921665236674869116141 102129345624463753075918553)
    ·
      refine ⟨76597009218347814806938915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102129345624463753075918553 76597009218347814806938915)
      ·
        refine ⟨114895513827521722210408373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76597009218347814806938915 114895513827521722210408373)
        ·
          refine ⟨10771454421330161457225785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114895513827521722210408373 10771454421330161457225785)
          ·
            refine ⟨8078590815997621092919339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771454421330161457225785 8078590815997621092919339)
            ·
              refine ⟨12117886223996431639379009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078590815997621092919339 12117886223996431639379009)
              ·
                refine ⟨9088414667997323729534257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12117886223996431639379009 9088414667997323729534257)
                ·
                  refine ⟨6816311000997992797150693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9088414667997323729534257 6816311000997992797150693)
                  ·
                    refine ⟨1278058312687123649465755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816311000997992797150693 1278058312687123649465755)
                    ·
                      rfl

theorem cell23_7467029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_7467029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467029 prefixEnd_7467029 := by exact prefixLift 7467029
  have htrace : WordTrace (prefixWord ++ tailWord_7467029) baseStart_7467029 baseEnd_7467029 := by
    simpa [prefixWord, tailWord_7467029, baseEnd_7467029] using wordTrace_append hprefix tailTrace_7467029
  have hstable : (prefixWord ++ tailWord_7467029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467029).length < 2 ^ (prefixWord ++ tailWord_7467029).sum := by decide
  have hdescent : baseEnd_7467029 < baseStart_7467029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467036 : List Nat := [2, 2, 3, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7467036 : Nat := 118140960795 + 7467036 * 2 ^ 59
def prefixEnd_7467036 : Nat := 4983230072969 + 3 ^ 40 * 7467036 * 2
def baseEnd_7467036 : Nat := 3834178532425952421009733

theorem tailTrace_7467036 : CollatzResearch.WordTrace tailWord_7467036 prefixEnd_7467036 3834178532425952421009733 := by
  unfold tailWord_7467036
  simp only [CollatzResearch.WordTrace]
  refine ⟨136172588488105657532310481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181563451317474210043080641 136172588488105657532310481)
  ·
    refine ⟨102129441366079243149232861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136172588488105657532310481 102129441366079243149232861)
    ·
      refine ⟨38298540512279716180962323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102129441366079243149232861 38298540512279716180962323)
      ·
        refine ⟨57447810768419574271443485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38298540512279716180962323 57447810768419574271443485)
        ·
          refine ⟨21542929038157340351791307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57447810768419574271443485 21542929038157340351791307)
          ·
            refine ⟨32314393557236010527686961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21542929038157340351791307 32314393557236010527686961)
            ·
              refine ⟨24235795167927007895765221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32314393557236010527686961 24235795167927007895765221)
              ·
                refine ⟨4544211593986313980455979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24235795167927007895765221 4544211593986313980455979)
                ·
                  refine ⟨6816317390979470970683969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544211593986313980455979 6816317390979470970683969)
                  ·
                    refine ⟨5112238043234603228012977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6816317390979470970683969 5112238043234603228012977)
                    ·
                      refine ⟨3834178532425952421009733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112238043234603228012977 3834178532425952421009733)
                      ·
                        rfl

theorem cell23_7467036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7467036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467036 prefixEnd_7467036 := by exact prefixLift 7467036
  have htrace : WordTrace (prefixWord ++ tailWord_7467036) baseStart_7467036 baseEnd_7467036 := by
    simpa [prefixWord, tailWord_7467036, baseEnd_7467036] using wordTrace_append hprefix tailTrace_7467036
  have hstable : (prefixWord ++ tailWord_7467036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467036).length < 2 ^ (prefixWord ++ tailWord_7467036).sum := by decide
  have hdescent : baseEnd_7467036 < baseStart_7467036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467070 : List Nat := [4, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7467070 : Nat := 118140960795 + 7467070 * 2 ^ 59
def prefixEnd_7467070 : Nat := 4983230072969 + 3 ^ 40 * 7467070 * 2
def baseEnd_7467070 : Nat := 3834195990768205287984577

theorem tailTrace_7467070 : CollatzResearch.WordTrace tailWord_7467070 prefixEnd_7467070 3834195990768205287984577 := by
  unfold tailWord_7467070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34043302132261017358919833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181564278038725425914239109 34043302132261017358919833)
  ·
    refine ⟨25532476599195763019189875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34043302132261017358919833 25532476599195763019189875)
    ·
      refine ⟨38298714898793644528784813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25532476599195763019189875 38298714898793644528784813)
      ·
        refine ⟨14362018087047616698294305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38298714898793644528784813 14362018087047616698294305)
        ·
          refine ⟨10771513565285712523720729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14362018087047616698294305 10771513565285712523720729)
          ·
            refine ⟨8078635173964284392790547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10771513565285712523720729 8078635173964284392790547)
            ·
              refine ⟨12117952760946426589185821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8078635173964284392790547 12117952760946426589185821)
              ·
                refine ⟨4544232285354909970944683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12117952760946426589185821 4544232285354909970944683)
                ·
                  refine ⟨6816348428032364956417025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544232285354909970944683 6816348428032364956417025)
                  ·
                    refine ⟨5112261321024273717312769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6816348428032364956417025 5112261321024273717312769)
                    ·
                      refine ⟨3834195990768205287984577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112261321024273717312769 3834195990768205287984577)
                      ·
                        rfl

theorem cell23_7467070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7467070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467070 prefixEnd_7467070 := by exact prefixLift 7467070
  have htrace : WordTrace (prefixWord ++ tailWord_7467070) baseStart_7467070 baseEnd_7467070 := by
    simpa [prefixWord, tailWord_7467070, baseEnd_7467070] using wordTrace_append hprefix tailTrace_7467070
  have hstable : (prefixWord ++ tailWord_7467070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467070).length < 2 ^ (prefixWord ++ tailWord_7467070).sum := by decide
  have hdescent : baseEnd_7467070 < baseStart_7467070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467145 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_7467145 : Nat := 118140960795 + 7467145 * 2 ^ 59
def prefixEnd_7467145 : Nat := 4983230072969 + 3 ^ 40 * 7467145 * 2
def baseEnd_7467145 : Nat := 1278078167272430831515577

theorem tailTrace_7467145 : CollatzResearch.WordTrace tailWord_7467145 prefixEnd_7467145 1278078167272430831515577 := by
  unfold tailWord_7467145
  simp only [CollatzResearch.WordTrace]
  refine ⟨272349152532816426680338889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181566101688544284453559259 272349152532816426680338889)
  ·
    refine ⟨204261864399612320010254167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272349152532816426680338889 204261864399612320010254167)
    ·
      refine ⟨306392796599418480015381251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204261864399612320010254167 306392796599418480015381251)
      ·
        refine ⟨459589194899127720023071877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306392796599418480015381251 459589194899127720023071877)
        ·
          refine ⟨86172974043586447504325977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459589194899127720023071877 86172974043586447504325977)
          ·
            refine ⟨64629730532689835628244483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86172974043586447504325977 64629730532689835628244483)
            ·
              refine ⟨96944595799034753442366725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64629730532689835628244483 96944595799034753442366725)
              ·
                refine ⟨18177111712319016270443761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96944595799034753442366725 18177111712319016270443761)
                ·
                  refine ⟨13632833784239262202832821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18177111712319016270443761 13632833784239262202832821)
                  ·
                    refine ⟨1278078167272430831515577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13632833784239262202832821 1278078167272430831515577)
                    ·
                      rfl

theorem cell23_7467145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_7467145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467145 prefixEnd_7467145 := by exact prefixLift 7467145
  have htrace : WordTrace (prefixWord ++ tailWord_7467145) baseStart_7467145 baseEnd_7467145 := by
    simpa [prefixWord, tailWord_7467145, baseEnd_7467145] using wordTrace_append hprefix tailTrace_7467145
  have hstable : (prefixWord ++ tailWord_7467145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467145).length < 2 ^ (prefixWord ++ tailWord_7467145).sum := by decide
  have hdescent : baseEnd_7467145 < baseStart_7467145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467293 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7467293 : Nat := 118140960795 + 7467293 * 2 ^ 59
def prefixEnd_7467293 : Nat := 4983230072969 + 3 ^ 40 * 7467293 * 2
def baseEnd_7467293 : Nat := 3834310496954157915496051

theorem tailTrace_7467293 : CollatzResearch.WordTrace tailWord_7467293 prefixEnd_7467293 3834310496954157915496051 := by
  unfold tailWord_7467293
  simp only [CollatzResearch.WordTrace]
  refine ⟨272354550536280247956726533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181569700357520165304484355 272354550536280247956726533)
  ·
    refine ⟨51066478225552546491886225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272354550536280247956726533 51066478225552546491886225)
    ·
      refine ⟨38299858669164409868914669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51066478225552546491886225 38299858669164409868914669)
      ·
        refine ⟨14362447000936653700843001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38299858669164409868914669 14362447000936653700843001)
        ·
          refine ⟨10771835250702490275632251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14362447000936653700843001 10771835250702490275632251)
          ·
            refine ⟨16157752876053735413448377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771835250702490275632251 16157752876053735413448377)
            ·
              refine ⟨12118314657040301560086283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16157752876053735413448377 12118314657040301560086283)
              ·
                refine ⟨18177471985560452340129425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118314657040301560086283 18177471985560452340129425)
                ·
                  refine ⟨13633103989170339255097069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18177471985560452340129425 13633103989170339255097069)
                  ·
                    refine ⟨5112413995938877220661401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13633103989170339255097069 5112413995938877220661401)
                    ·
                      refine ⟨3834310496954157915496051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112413995938877220661401 3834310496954157915496051)
                      ·
                        rfl

theorem cell23_7467293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7467293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467293 prefixEnd_7467293 := by exact prefixLift 7467293
  have htrace : WordTrace (prefixWord ++ tailWord_7467293) baseStart_7467293 baseEnd_7467293 := by
    simpa [prefixWord, tailWord_7467293, baseEnd_7467293] using wordTrace_append hprefix tailTrace_7467293
  have hstable : (prefixWord ++ tailWord_7467293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467293).length < 2 ^ (prefixWord ++ tailWord_7467293).sum := by decide
  have hdescent : baseEnd_7467293 < baseStart_7467293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467316 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_7467316 : Nat := 118140960795 + 7467316 * 2 ^ 59
def prefixEnd_7467316 : Nat := 4983230072969 + 3 ^ 40 * 7467316 * 2
def baseEnd_7467316 : Nat := 1278107435669737108502815

theorem tailTrace_7467316 : CollatzResearch.WordTrace tailWord_7467316 prefixEnd_7467316 1278107435669737108502815 := by
  unfold tailWord_7467316
  simp only [CollatzResearch.WordTrace]
  refine ⟨136177694707598461442406901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181570259610131281923209201 136177694707598461442406901)
  ·
    refine ⟨12766658878837355760225647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136177694707598461442406901 12766658878837355760225647)
    ·
      refine ⟨19149988318256033640338471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12766658878837355760225647 19149988318256033640338471)
      ·
        refine ⟨28724982477384050460507707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19149988318256033640338471 28724982477384050460507707)
        ·
          refine ⟨43087473716076075690761561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28724982477384050460507707 43087473716076075690761561)
          ·
            refine ⟨32315605287057056768071171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43087473716076075690761561 32315605287057056768071171)
            ·
              refine ⟨48473407930585585152106757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32315605287057056768071171 48473407930585585152106757)
              ·
                refine ⟨9088763986984797216020017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48473407930585585152106757 9088763986984797216020017)
                ·
                  refine ⟨6816572990238597912015013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9088763986984797216020017 6816572990238597912015013)
                  ·
                    refine ⟨1278107435669737108502815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6816572990238597912015013 1278107435669737108502815)
                    ·
                      rfl

theorem cell23_7467316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_7467316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467316 prefixEnd_7467316 := by exact prefixLift 7467316
  have htrace : WordTrace (prefixWord ++ tailWord_7467316) baseStart_7467316 baseEnd_7467316 := by
    simpa [prefixWord, tailWord_7467316, baseEnd_7467316] using wordTrace_append hprefix tailTrace_7467316
  have hstable : (prefixWord ++ tailWord_7467316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467316).length < 2 ^ (prefixWord ++ tailWord_7467316).sum := by decide
  have hdescent : baseEnd_7467316 < baseStart_7467316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467360 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3]
def baseStart_7467360 : Nat := 118140960795 + 7467360 * 2 ^ 59
def prefixEnd_7467360 : Nat := 4983230072969 + 3 ^ 40 * 7467360 * 2
def baseEnd_7467360 : Nat := 3834344900158009153358243

theorem tailTrace_7467360 : CollatzResearch.WordTrace tailWord_7467360 prefixEnd_7467360 3834344900158009153358243 := by
  unfold tailWord_7467360
  simp only [CollatzResearch.WordTrace]
  refine ⟨136178497113518759199707767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181571329484691678932943689 136178497113518759199707767)
  ·
    refine ⟨204267745670278138799561651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136178497113518759199707767 204267745670278138799561651)
    ·
      refine ⟨306401618505417208199342477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204267745670278138799561651 306401618505417208199342477)
      ·
        refine ⟨114900606939531453074753429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306401618505417208199342477 114900606939531453074753429)
        ·
          refine ⟨5385965950290536862879067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114900606939531453074753429 5385965950290536862879067)
          ·
            refine ⟨8078948925435805294318601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385965950290536862879067 8078948925435805294318601)
            ·
              refine ⟨6059211694076853970738951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078948925435805294318601 6059211694076853970738951)
              ·
                refine ⟨9088817541115280956108427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059211694076853970738951 9088817541115280956108427)
                ·
                  refine ⟨13633226311672921434162641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9088817541115280956108427 13633226311672921434162641)
                  ·
                    refine ⟨10224919733754691075621981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13633226311672921434162641 10224919733754691075621981)
                    ·
                      refine ⟨3834344900158009153358243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10224919733754691075621981 3834344900158009153358243)
                      ·
                        rfl

theorem cell23_7467360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_7467360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467360 prefixEnd_7467360 := by exact prefixLift 7467360
  have htrace : WordTrace (prefixWord ++ tailWord_7467360) baseStart_7467360 baseEnd_7467360 := by
    simpa [prefixWord, tailWord_7467360, baseEnd_7467360] using wordTrace_append hprefix tailTrace_7467360
  have hstable : (prefixWord ++ tailWord_7467360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467360).length < 2 ^ (prefixWord ++ tailWord_7467360).sum := by decide
  have hdescent : baseEnd_7467360 < baseStart_7467360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467472 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_7467472 : Nat := 118140960795 + 7467472 * 2 ^ 59
def prefixEnd_7467472 : Nat := 4983230072969 + 3 ^ 40 * 7467472 * 2
def baseEnd_7467472 : Nat := 3834402409991312715157727

theorem tailTrace_7467472 : CollatzResearch.WordTrace tailWord_7467472 prefixEnd_7467472 3834402409991312715157727 := by
  unfold tailWord_7467472
  simp only [CollatzResearch.WordTrace]
  refine ⟨136180539601315880763746335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181574052801754507684995113 136180539601315880763746335)
  ·
    refine ⟨204270809401973821145619503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136180539601315880763746335 204270809401973821145619503)
    ·
      refine ⟨306406214102960731718429255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204270809401973821145619503 306406214102960731718429255)
      ·
        refine ⟨459609321154441097577643883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306406214102960731718429255 459609321154441097577643883)
        ·
          refine ⟨689413981731661646366465825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459609321154441097577643883 689413981731661646366465825)
          ·
            refine ⟨517060486298746234774849369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689413981731661646366465825 517060486298746234774849369)
            ·
              refine ⟨387795364724059676081137027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517060486298746234774849369 387795364724059676081137027)
              ·
                refine ⟨581693047086089514121705541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387795364724059676081137027 581693047086089514121705541)
                ·
                  refine ⟨109067446328641783897819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581693047086089514121705541 109067446328641783897819789)
                  ·
                    refine ⟨40900292373240668961682421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109067446328641783897819789 40900292373240668961682421)
                    ·
                      refine ⟨3834402409991312715157727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40900292373240668961682421 3834402409991312715157727)
                      ·
                        rfl

theorem cell23_7467472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_7467472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467472 prefixEnd_7467472 := by exact prefixLift 7467472
  have htrace : WordTrace (prefixWord ++ tailWord_7467472) baseStart_7467472 baseEnd_7467472 := by
    simpa [prefixWord, tailWord_7467472, baseEnd_7467472] using wordTrace_append hprefix tailTrace_7467472
  have hstable : (prefixWord ++ tailWord_7467472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467472).length < 2 ^ (prefixWord ++ tailWord_7467472).sum := by decide
  have hdescent : baseEnd_7467472 < baseStart_7467472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467533 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7467533 : Nat := 118140960795 + 7467533 * 2 ^ 59
def prefixEnd_7467533 : Nat := 4983230072969 + 3 ^ 40 * 7467533 * 2
def baseEnd_7467533 : Nat := 3834433732311236976494947

theorem tailTrace_7467533 : CollatzResearch.WordTrace tailWord_7467533 prefixEnd_7467533 3834433732311236976494947 := by
  unfold tailWord_7467533
  simp only [CollatzResearch.WordTrace]
  refine ⟨272363304055410768945463253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181575536036940512630308835 272363304055410768945463253)
  ·
    refine ⟨6383514938798689897159295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 272363304055410768945463253 6383514938798689897159295)
    ·
      refine ⟨9575272408198034845738943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383514938798689897159295 9575272408198034845738943)
      ·
        refine ⟨14362908612297052268608415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9575272408198034845738943 14362908612297052268608415)
        ·
          refine ⟨21544362918445578402912623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14362908612297052268608415 21544362918445578402912623)
          ·
            refine ⟨32316544377668367604368935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21544362918445578402912623 32316544377668367604368935)
            ·
              refine ⟨48474816566502551406553403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32316544377668367604368935 48474816566502551406553403)
              ·
                refine ⟨72712224849753827109830105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48474816566502551406553403 72712224849753827109830105)
                ·
                  refine ⟨54534168637315370332372579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72712224849753827109830105 54534168637315370332372579)
                  ·
                    refine ⟨81801252955973055498558869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54534168637315370332372579 81801252955973055498558869)
                    ·
                      refine ⟨3834433732311236976494947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81801252955973055498558869 3834433732311236976494947)
                      ·
                        rfl

theorem cell23_7467533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7467533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467533 prefixEnd_7467533 := by exact prefixLift 7467533
  have htrace : WordTrace (prefixWord ++ tailWord_7467533) baseStart_7467533 baseEnd_7467533 := by
    simpa [prefixWord, tailWord_7467533, baseEnd_7467533] using wordTrace_append hprefix tailTrace_7467533
  have hstable : (prefixWord ++ tailWord_7467533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467533).length < 2 ^ (prefixWord ++ tailWord_7467533).sum := by decide
  have hdescent : baseEnd_7467533 < baseStart_7467533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467553 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7467553 : Nat := 118140960795 + 7467553 * 2 ^ 59
def prefixEnd_7467553 : Nat := 4983230072969 + 3 ^ 40 * 7467553 * 2
def baseEnd_7467553 : Nat := 3834444001924326898244855

theorem tailTrace_7467553 : CollatzResearch.WordTrace tailWord_7467553 prefixEnd_7467553 3834444001924326898244855 := by
  unfold tailWord_7467553
  simp only [CollatzResearch.WordTrace]
  refine ⟨272364033515338312361191313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181576022343558874907460875 272364033515338312361191313)
  ·
    refine ⟨204273025136503734270893485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272364033515338312361191313 204273025136503734270893485)
    ·
      refine ⟨76602384426188900351585057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204273025136503734270893485 76602384426188900351585057)
      ·
        refine ⟨57451788319641675263688793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76602384426188900351585057 57451788319641675263688793)
        ·
          refine ⟨43088841239731256447766595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57451788319641675263688793 43088841239731256447766595)
          ·
            refine ⟨64633261859596884671649893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43088841239731256447766595 64633261859596884671649893)
            ·
              refine ⟨12118736598674415875934355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64633261859596884671649893 12118736598674415875934355)
              ·
                refine ⟨18178104898011623813901533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118736598674415875934355 18178104898011623813901533)
                ·
                  refine ⟨6816789336754358930213075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18178104898011623813901533 6816789336754358930213075)
                  ·
                    refine ⟨10225184005131538395319613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6816789336754358930213075 10225184005131538395319613)
                    ·
                      refine ⟨3834444001924326898244855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225184005131538395319613 3834444001924326898244855)
                      ·
                        rfl

theorem cell23_7467553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7467553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467553 prefixEnd_7467553 := by exact prefixLift 7467553
  have htrace : WordTrace (prefixWord ++ tailWord_7467553) baseStart_7467553 baseEnd_7467553 := by
    simpa [prefixWord, tailWord_7467553, baseEnd_7467553] using wordTrace_append hprefix tailTrace_7467553
  have hstable : (prefixWord ++ tailWord_7467553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467553).length < 2 ^ (prefixWord ++ tailWord_7467553).sum := by decide
  have hdescent : baseEnd_7467553 < baseStart_7467553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467576 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_7467576 : Nat := 118140960795 + 7467576 * 2 ^ 59
def prefixEnd_7467576 : Nat := 4983230072969 + 3 ^ 40 * 7467576 * 2
def baseEnd_7467576 : Nat := 3834455811979380308257249

theorem tailTrace_7467576 : CollatzResearch.WordTrace tailWord_7467576 prefixEnd_7467576 3834455811979380308257249 := by
  unfold tailWord_7467576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136182436197127493644639291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181576581596169991526185721 136182436197127493644639291)
  ·
    refine ⟨204273654295691240466958937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136182436197127493644639291 204273654295691240466958937)
    ·
      refine ⟨153205240721768430350219203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204273654295691240466958937 153205240721768430350219203)
      ·
        refine ⟨229807861082652645525328805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153205240721768430350219203 229807861082652645525328805)
        ·
          refine ⟨43088973952997371035999151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229807861082652645525328805 43088973952997371035999151)
          ·
            refine ⟨64633460929496056553998727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43088973952997371035999151 64633460929496056553998727)
            ·
              refine ⟨96950191394244084830998091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64633460929496056553998727 96950191394244084830998091)
              ·
                refine ⟨145425287091366127246497137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96950191394244084830998091 145425287091366127246497137)
                ·
                  refine ⟨109068965318524595434872853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145425287091366127246497137 109068965318524595434872853)
                  ·
                    refine ⟨5112607749305840411009665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109068965318524595434872853 5112607749305840411009665)
                    ·
                      refine ⟨3834455811979380308257249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112607749305840411009665 3834455811979380308257249)
                      ·
                        rfl

theorem cell23_7467576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_7467576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467576 prefixEnd_7467576 := by exact prefixLift 7467576
  have htrace : WordTrace (prefixWord ++ tailWord_7467576) baseStart_7467576 baseEnd_7467576 := by
    simpa [prefixWord, tailWord_7467576, baseEnd_7467576] using wordTrace_append hprefix tailTrace_7467576
  have hstable : (prefixWord ++ tailWord_7467576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467576).length < 2 ^ (prefixWord ++ tailWord_7467576).sum := by decide
  have hdescent : baseEnd_7467576 < baseStart_7467576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467590 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7467590 : Nat := 118140960795 + 7467590 * 2 ^ 59
def prefixEnd_7467590 : Nat := 4983230072969 + 3 ^ 40 * 7467590 * 2
def baseEnd_7467590 : Nat := 1278154333569514417827395

theorem tailTrace_7467590 : CollatzResearch.WordTrace tailWord_7467590 prefixEnd_7467590 1278154333569514417827395 := by
  unfold tailWord_7467590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511418219256383365009007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181576922010802845120192149 8511418219256383365009007)
  ·
    refine ⟨12767127328884575047513511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511418219256383365009007 12767127328884575047513511)
    ·
      refine ⟨19150690993326862571270267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767127328884575047513511 19150690993326862571270267)
      ·
        refine ⟨28726036489990293856905401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19150690993326862571270267 28726036489990293856905401)
        ·
          refine ⟨21544527367492720392679051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28726036489990293856905401 21544527367492720392679051)
          ·
            refine ⟨32316791051239080589018577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21544527367492720392679051 32316791051239080589018577)
            ·
              refine ⟨24237593288429310441763933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32316791051239080589018577 24237593288429310441763933)
              ·
                refine ⟨9089097483160991415661475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24237593288429310441763933 9089097483160991415661475)
                ·
                  refine ⟨13633646224741487123492213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089097483160991415661475 13633646224741487123492213)
                  ·
                    refine ⟨1278154333569514417827395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13633646224741487123492213 1278154333569514417827395)
                    ·
                      rfl

theorem cell23_7467590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7467590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467590 prefixEnd_7467590 := by exact prefixLift 7467590
  have htrace : WordTrace (prefixWord ++ tailWord_7467590) baseStart_7467590 baseEnd_7467590 := by
    simpa [prefixWord, tailWord_7467590, baseEnd_7467590] using wordTrace_append hprefix tailTrace_7467590
  have hstable : (prefixWord ++ tailWord_7467590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467590).length < 2 ^ (prefixWord ++ tailWord_7467590).sum := by decide
  have hdescent : baseEnd_7467590 < baseStart_7467590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467596 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7467596 : Nat := 118140960795 + 7467596 * 2 ^ 59
def prefixEnd_7467596 : Nat := 4983230072969 + 3 ^ 40 * 7467596 * 2
def baseEnd_7467596 : Nat := 3834466081592470230007157

theorem tailTrace_7467596 : CollatzResearch.WordTrace tailWord_7467596 prefixEnd_7467596 3834466081592470230007157 := by
  unfold tailWord_7467596
  simp only [CollatzResearch.WordTrace]
  refine ⟨136182800927091265352503321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181577067902788353803337761 136182800927091265352503321)
  ·
    refine ⟨102137100695318449014377491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136182800927091265352503321 102137100695318449014377491)
    ·
      refine ⟨153205651042977673521566237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102137100695318449014377491 153205651042977673521566237)
      ·
        refine ⟨57452119141116627570587339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153205651042977673521566237 57452119141116627570587339)
        ·
          refine ⟨86178178711674941355881009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57452119141116627570587339 86178178711674941355881009)
          ·
            refine ⟨64633634033756206016910757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86178178711674941355881009 64633634033756206016910757)
            ·
              refine ⟨12118806381329288628170767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64633634033756206016910757 12118806381329288628170767)
              ·
                refine ⟨18178209571993932942256151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12118806381329288628170767 18178209571993932942256151)
                ·
                  refine ⟨27267314357990899413384227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18178209571993932942256151 27267314357990899413384227)
                  ·
                    refine ⟨40900971536986349120076341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27267314357990899413384227 40900971536986349120076341)
                    ·
                      refine ⟨3834466081592470230007157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40900971536986349120076341 3834466081592470230007157)
                      ·
                        rfl

theorem cell23_7467596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7467596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467596 prefixEnd_7467596 := by exact prefixLift 7467596
  have htrace : WordTrace (prefixWord ++ tailWord_7467596) baseStart_7467596 baseEnd_7467596 := by
    simpa [prefixWord, tailWord_7467596, baseEnd_7467596] using wordTrace_append hprefix tailTrace_7467596
  have hstable : (prefixWord ++ tailWord_7467596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467596).length < 2 ^ (prefixWord ++ tailWord_7467596).sum := by decide
  have hdescent : baseEnd_7467596 < baseStart_7467596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467619 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7467619 : Nat := 118140960795 + 7467619 * 2 ^ 59
def prefixEnd_7467619 : Nat := 4983230072969 + 3 ^ 40 * 7467619 * 2
def baseEnd_7467619 : Nat := 3834477891647523640019551

theorem tailTrace_7467619 : CollatzResearch.WordTrace tailWord_7467619 prefixEnd_7467619 3834477891647523640019551 := by
  unfold tailWord_7467619
  simp only [CollatzResearch.WordTrace]
  refine ⟨272366440733099205633093911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181577627155399470422062607 272366440733099205633093911)
  ·
    refine ⟨408549661099648808449640867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272366440733099205633093911 408549661099648808449640867)
    ·
      refine ⟨612824491649473212674461301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408549661099648808449640867 612824491649473212674461301)
      ·
        refine ⟨57452296092138113688230747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 612824491649473212674461301 57452296092138113688230747)
        ·
          refine ⟨86178444138207170532346121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57452296092138113688230747 86178444138207170532346121)
          ·
            refine ⟨64633833103655377899259591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86178444138207170532346121 64633833103655377899259591)
            ·
              refine ⟨96950749655483066848889387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64633833103655377899259591 96950749655483066848889387)
              ·
                refine ⟨145426124483224600273334081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96950749655483066848889387 145426124483224600273334081)
                ·
                  refine ⟨109069593362418450205000561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145426124483224600273334081 109069593362418450205000561)
                  ·
                    refine ⟨81802195021813837653750421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109069593362418450205000561 81802195021813837653750421)
                    ·
                      refine ⟨3834477891647523640019551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81802195021813837653750421 3834477891647523640019551)
                      ·
                        rfl

theorem cell23_7467619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7467619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467619 prefixEnd_7467619 := by exact prefixLift 7467619
  have htrace : WordTrace (prefixWord ++ tailWord_7467619) baseStart_7467619 baseEnd_7467619 := by
    simpa [prefixWord, tailWord_7467619, baseEnd_7467619] using wordTrace_append hprefix tailTrace_7467619
  have hstable : (prefixWord ++ tailWord_7467619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467619).length < 2 ^ (prefixWord ++ tailWord_7467619).sum := by decide
  have hdescent : baseEnd_7467619 < baseStart_7467619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467630 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7467630 : Nat := 118140960795 + 7467630 * 2 ^ 59
def prefixEnd_7467630 : Nat := 4983230072969 + 3 ^ 40 * 7467630 * 2
def baseEnd_7467630 : Nat := 3834483539934723096982001

theorem tailTrace_7467630 : CollatzResearch.WordTrace tailWord_7467630 prefixEnd_7467630 3834483539934723096982001 := by
  unfold tailWord_7467630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34045855242007419313968043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181577894624039569674496229 34045855242007419313968043)
  ·
    refine ⟨51068782863011128970952065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34045855242007419313968043 51068782863011128970952065)
    ·
      refine ⟨38301587147258346728214049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51068782863011128970952065 38301587147258346728214049)
      ·
        refine ⟨28726190360443760046160537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38301587147258346728214049 28726190360443760046160537)
        ·
          refine ⟨21544642770332820034620403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28726190360443760046160537 21544642770332820034620403)
          ·
            refine ⟨32316964155499230051930605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21544642770332820034620403 32316964155499230051930605)
            ·
              refine ⟨12118861558312211269473977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32316964155499230051930605 12118861558312211269473977)
              ·
                refine ⟨9089146168734158452105483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12118861558312211269473977 9089146168734158452105483)
                ·
                  refine ⟨13633719253101237678158225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089146168734158452105483 13633719253101237678158225)
                  ·
                    refine ⟨10225289439825928258618669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13633719253101237678158225 10225289439825928258618669)
                    ·
                      refine ⟨3834483539934723096982001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225289439825928258618669 3834483539934723096982001)
                      ·
                        rfl

theorem cell23_7467630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7467630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467630 prefixEnd_7467630 := by exact prefixLift 7467630
  have htrace : WordTrace (prefixWord ++ tailWord_7467630) baseStart_7467630 baseEnd_7467630 := by
    simpa [prefixWord, tailWord_7467630, baseEnd_7467630] using wordTrace_append hprefix tailTrace_7467630
  have hstable : (prefixWord ++ tailWord_7467630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467630).length < 2 ^ (prefixWord ++ tailWord_7467630).sum := by decide
  have hdescent : baseEnd_7467630 < baseStart_7467630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467639 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_7467639 : Nat := 118140960795 + 7467639 * 2 ^ 59
def prefixEnd_7467639 : Nat := 4983230072969 + 3 ^ 40 * 7467639 * 2
def baseEnd_7467639 : Nat := 3834488161260613561769459

theorem tailTrace_7467639 : CollatzResearch.WordTrace tailWord_7467639 prefixEnd_7467639 3834488161260613561769459 := by
  unfold tailWord_7467639
  simp only [CollatzResearch.WordTrace]
  refine ⟨272367170193026749048821971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181578113462017832699214647 272367170193026749048821971)
  ·
    refine ⟨408550755289540123573232957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272367170193026749048821971 408550755289540123573232957)
    ·
      refine ⟨153206533233577546339962359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408550755289540123573232957 153206533233577546339962359)
      ·
        refine ⟨229809799850366319509943539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153206533233577546339962359 229809799850366319509943539)
        ·
          refine ⟨344714699775549479264915309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229809799850366319509943539 344714699775549479264915309)
          ·
            refine ⟨129268012415831054724343241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344714699775549479264915309 129268012415831054724343241)
            ·
              refine ⟨96951009311873291043257431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129268012415831054724343241 96951009311873291043257431)
              ·
                refine ⟨145426513967809936564886147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96951009311873291043257431 145426513967809936564886147)
                ·
                  refine ⟨218139770951714904847329221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145426513967809936564886147 218139770951714904847329221)
                  ·
                    refine ⟨40901207053446544658874229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218139770951714904847329221 40901207053446544658874229)
                    ·
                      refine ⟨3834488161260613561769459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40901207053446544658874229 3834488161260613561769459)
                      ·
                        rfl

theorem cell23_7467639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_7467639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467639 prefixEnd_7467639 := by exact prefixLift 7467639
  have htrace : WordTrace (prefixWord ++ tailWord_7467639) baseStart_7467639 baseEnd_7467639 := by
    simpa [prefixWord, tailWord_7467639, baseEnd_7467639] using wordTrace_append hprefix tailTrace_7467639
  have hstable : (prefixWord ++ tailWord_7467639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467639).length < 2 ^ (prefixWord ++ tailWord_7467639).sum := by decide
  have hdescent : baseEnd_7467639 < baseStart_7467639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467650 : List Nat := [3, 4, 3, 1, 1, 11]
def baseStart_7467650 : Nat := 118140960795 + 7467650 * 2 ^ 59
def prefixEnd_7467650 : Nat := 4983230072969 + 3 ^ 40 * 7467650 * 2
def baseEnd_7467650 : Nat := 15779809915834621476263

theorem tailTrace_7467650 : CollatzResearch.WordTrace tailWord_7467650 prefixEnd_7467650 15779809915834621476263 := by
  unfold tailWord_7467650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68091892848996724481868101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181578380930657931951648269 68091892848996724481868101)
  ·
    refine ⟨12767229909186885840350269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68091892848996724481868101 12767229909186885840350269)
    ·
      refine ⟨4787711215945082190131351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12767229909186885840350269 4787711215945082190131351)
      ·
        refine ⟨7181566823917623285197027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787711215945082190131351 7181566823917623285197027)
        ·
          refine ⟨10772350235876434927795541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181566823917623285197027 10772350235876434927795541)
          ·
            refine ⟨15779809915834621476263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10772350235876434927795541 15779809915834621476263)
            ·
              rfl

theorem cell23_7467650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 11].length) (baseStart_7467650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467650 prefixEnd_7467650 := by exact prefixLift 7467650
  have htrace : WordTrace (prefixWord ++ tailWord_7467650) baseStart_7467650 baseEnd_7467650 := by
    simpa [prefixWord, tailWord_7467650, baseEnd_7467650] using wordTrace_append hprefix tailTrace_7467650
  have hstable : (prefixWord ++ tailWord_7467650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467650).length < 2 ^ (prefixWord ++ tailWord_7467650).sum := by decide
  have hdescent : baseEnd_7467650 < baseStart_7467650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467676 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_7467676 : Nat := 118140960795 + 7467676 * 2 ^ 59
def prefixEnd_7467676 : Nat := 4983230072969 + 3 ^ 40 * 7467676 * 2
def baseEnd_7467676 : Nat := 1278169053348276639002263

theorem tailTrace_7467676 : CollatzResearch.WordTrace tailWord_7467676 prefixEnd_7467676 1278169053348276639002263 := by
  unfold tailWord_7467676
  simp only [CollatzResearch.WordTrace]
  refine ⟨136184259846946352183959441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181579013129261802911945921 136184259846946352183959441)
  ·
    refine ⟨102138194885209764137969581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136184259846946352183959441 102138194885209764137969581)
    ·
      refine ⟨38301823081953661551738593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102138194885209764137969581 38301823081953661551738593)
      ·
        refine ⟨28726367311465246163803945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38301823081953661551738593 28726367311465246163803945)
        ·
          refine ⟨21544775483598934622852959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28726367311465246163803945 21544775483598934622852959)
          ·
            refine ⟨32317163225398401934279439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21544775483598934622852959 32317163225398401934279439)
            ·
              refine ⟨48475744838097602901419159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32317163225398401934279439 48475744838097602901419159)
              ·
                refine ⟨72713617257146404352128739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48475744838097602901419159 72713617257146404352128739)
                ·
                  refine ⟨109070425885719606528193109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72713617257146404352128739 109070425885719606528193109)
                  ·
                    refine ⟨1278169053348276639002263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109070425885719606528193109 1278169053348276639002263)
                    ·
                      rfl

theorem cell23_7467676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_7467676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467676 prefixEnd_7467676 := by exact prefixLift 7467676
  have htrace : WordTrace (prefixWord ++ tailWord_7467676) baseStart_7467676 baseEnd_7467676 := by
    simpa [prefixWord, tailWord_7467676, baseEnd_7467676] using wordTrace_append hprefix tailTrace_7467676
  have hstable : (prefixWord ++ tailWord_7467676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467676).length < 2 ^ (prefixWord ++ tailWord_7467676).sum := by decide
  have hdescent : baseEnd_7467676 < baseStart_7467676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467689 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 9]
def baseStart_7467689 : Nat := 118140960795 + 7467689 * 2 ^ 59
def prefixEnd_7467689 : Nat := 4983230072969 + 3 ^ 40 * 7467689 * 2
def baseEnd_7467689 : Nat := 426057092810370929571581

theorem tailTrace_7467689 : CollatzResearch.WordTrace tailWord_7467689 prefixEnd_7467689 426057092810370929571581 := by
  unfold tailWord_7467689
  simp only [CollatzResearch.WordTrace]
  refine ⟨272368993842845607588142121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181579329228563738392094747 272368993842845607588142121)
  ·
    refine ⟨204276745382134205691106591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272368993842845607588142121 204276745382134205691106591)
    ·
      refine ⟨306415118073201308536659887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204276745382134205691106591 306415118073201308536659887)
      ·
        refine ⟨459622677109801962804989831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306415118073201308536659887 459622677109801962804989831)
        ·
          refine ⟨689434015664702944207484747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459622677109801962804989831 689434015664702944207484747)
          ·
            refine ⟨1034151023497054416311227121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689434015664702944207484747 1034151023497054416311227121)
            ·
              refine ⟨775613267622790812233420341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034151023497054416311227121 775613267622790812233420341)
              ·
                refine ⟨72713743839636638646883157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 775613267622790812233420341 72713743839636638646883157)
                ·
                  refine ⟨426057092810370929571581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72713743839636638646883157 426057092810370929571581)
                  ·
                    rfl

theorem cell23_7467689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_7467689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467689 prefixEnd_7467689 := by exact prefixLift 7467689
  have htrace : WordTrace (prefixWord ++ tailWord_7467689) baseStart_7467689 baseEnd_7467689 := by
    simpa [prefixWord, tailWord_7467689, baseEnd_7467689] using wordTrace_append hprefix tailTrace_7467689
  have hstable : (prefixWord ++ tailWord_7467689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467689).length < 2 ^ (prefixWord ++ tailWord_7467689).sum := by decide
  have hdescent : baseEnd_7467689 < baseStart_7467689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467736 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_7467736 : Nat := 118140960795 + 7467736 * 2 ^ 59
def prefixEnd_7467736 : Nat := 4983230072969 + 3 ^ 40 * 7467736 * 2
def baseEnd_7467736 : Nat := 1278179322961366560752171

theorem tailTrace_7467736 : CollatzResearch.WordTrace tailWord_7467736 prefixEnd_7467736 1278179322961366560752171 := by
  unfold tailWord_7467736
  simp only [CollatzResearch.WordTrace]
  refine ⟨136185354036837667307551531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181580472049116889743402041 136185354036837667307551531)
  ·
    refine ⟨204278031055256500961327297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136185354036837667307551531 204278031055256500961327297)
    ·
      refine ⟨153208523291442375720995473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204278031055256500961327297 153208523291442375720995473)
      ·
        refine ⟨114906392468581781790746605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153208523291442375720995473 114906392468581781790746605)
        ·
          refine ⟨43089897175718168171529977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114906392468581781790746605 43089897175718168171529977)
          ·
            refine ⟨32317422881788626128647483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43089897175718168171529977 32317422881788626128647483)
            ·
              refine ⟨48476134322682939192971225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32317422881788626128647483 48476134322682939192971225)
              ·
                refine ⟨36357100742012204394728419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48476134322682939192971225 36357100742012204394728419)
                ·
                  refine ⟨54535651113018306592092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36357100742012204394728419 54535651113018306592092629)
                  ·
                    refine ⟨1278179322961366560752171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54535651113018306592092629 1278179322961366560752171)
                    ·
                      rfl

theorem cell23_7467736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_7467736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467736 prefixEnd_7467736 := by exact prefixLift 7467736
  have htrace : WordTrace (prefixWord ++ tailWord_7467736) baseStart_7467736 baseEnd_7467736 := by
    simpa [prefixWord, tailWord_7467736, baseEnd_7467736] using wordTrace_append hprefix tailTrace_7467736
  have hstable : (prefixWord ++ tailWord_7467736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467736).length < 2 ^ (prefixWord ++ tailWord_7467736).sum := by decide
  have hdescent : baseEnd_7467736 < baseStart_7467736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467773 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7467773 : Nat := 118140960795 + 7467773 * 2 ^ 59
def prefixEnd_7467773 : Nat := 4983230072969 + 3 ^ 40 * 7467773 * 2
def baseEnd_7467773 : Nat := 3834556967668316037493843

theorem tailTrace_7467773 : CollatzResearch.WordTrace tailWord_7467773 prefixEnd_7467773 3834556967668316037493843 := by
  unfold tailWord_7467773
  simp only [CollatzResearch.WordTrace]
  refine ⟨272372057574541289934199973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181581371716360859956133315 272372057574541289934199973)
  ·
    refine ⟨51069760795226491862662495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272372057574541289934199973 51069760795226491862662495)
    ·
      refine ⟨76604641192839737793993743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51069760795226491862662495 76604641192839737793993743)
      ·
        refine ⟨114906961789259606690990615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76604641192839737793993743 114906961789259606690990615)
        ·
          refine ⟨172360442683889410036485923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114906961789259606690990615 172360442683889410036485923)
          ·
            refine ⟨258540664025834115054728885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172360442683889410036485923 258540664025834115054728885)
            ·
              refine ⟨24238187252421948286380833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258540664025834115054728885 24238187252421948286380833)
              ·
                refine ⟨18178640439316461214785625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24238187252421948286380833 18178640439316461214785625)
                ·
                  refine ⟨13633980329487345911089219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18178640439316461214785625 13633980329487345911089219)
                  ·
                    refine ⟨20450970494231018866633829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13633980329487345911089219 20450970494231018866633829)
                    ·
                      refine ⟨3834556967668316037493843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20450970494231018866633829 3834556967668316037493843)
                      ·
                        rfl

theorem cell23_7467773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7467773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467773 prefixEnd_7467773 := by exact prefixLift 7467773
  have htrace : WordTrace (prefixWord ++ tailWord_7467773) baseStart_7467773 baseEnd_7467773 := by
    simpa [prefixWord, tailWord_7467773, baseEnd_7467773] using wordTrace_append hprefix tailTrace_7467773
  have hstable : (prefixWord ++ tailWord_7467773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467773).length < 2 ^ (prefixWord ++ tailWord_7467773).sum := by decide
  have hdescent : baseEnd_7467773 < baseStart_7467773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467810 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_7467810 : Nat := 118140960795 + 7467810 * 2 ^ 59
def prefixEnd_7467810 : Nat := 4983230072969 + 3 ^ 40 * 7467810 * 2
def baseEnd_7467810 : Nat := 3834575966452532392731173

theorem tailTrace_7467810 : CollatzResearch.WordTrace tailWord_7467810 prefixEnd_7467810 3834575966452532392731173 := by
  unfold tailWord_7467810
  simp only [CollatzResearch.WordTrace]
  refine ⟨68093351768851811313324221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181582271383604830168864589 68093351768851811313324221)
  ·
    refine ⟨25535006913319429242496583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68093351768851811313324221 25535006913319429242496583)
    ·
      refine ⟨38302510369979143863744875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25535006913319429242496583 38302510369979143863744875)
      ·
        refine ⟨57453765554968715795617313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38302510369979143863744875 57453765554968715795617313)
        ·
          refine ⟨43090324166226536846712985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57453765554968715795617313 43090324166226536846712985)
          ·
            refine ⟨32317743124669902635034739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43090324166226536846712985 32317743124669902635034739)
            ·
              refine ⟨48476614687004853952552109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32317743124669902635034739 48476614687004853952552109)
              ·
                refine ⟨18178730507626820232207041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48476614687004853952552109 18178730507626820232207041)
                ·
                  refine ⟨13634047880720115174155281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18178730507626820232207041 13634047880720115174155281)
                  ·
                    refine ⟨10225535910540086380616461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13634047880720115174155281 10225535910540086380616461)
                    ·
                      refine ⟨3834575966452532392731173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225535910540086380616461 3834575966452532392731173)
                      ·
                        rfl

theorem cell23_7467810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_7467810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467810 prefixEnd_7467810 := by exact prefixLift 7467810
  have htrace : WordTrace (prefixWord ++ tailWord_7467810) baseStart_7467810 baseEnd_7467810 := by
    simpa [prefixWord, tailWord_7467810, baseEnd_7467810] using wordTrace_append hprefix tailTrace_7467810
  have hstable : (prefixWord ++ tailWord_7467810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467810).length < 2 ^ (prefixWord ++ tailWord_7467810).sum := by decide
  have hdescent : baseEnd_7467810 < baseStart_7467810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467857 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_7467857 : Nat := 118140960795 + 7467857 * 2 ^ 59
def prefixEnd_7467857 : Nat := 4983230072969 + 3 ^ 40 * 7467857 * 2
def baseEnd_7467857 : Nat := 3834600100043293708843457

theorem tailTrace_7467857 : CollatzResearch.WordTrace tailWord_7467857 prefixEnd_7467857 3834600100043293708843457 := by
  unfold tailWord_7467857
  simp only [CollatzResearch.WordTrace]
  refine ⟨272375121306236972280257825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181583414204157981520171883 272375121306236972280257825)
  ·
    refine ⟨204281340979677729210193369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272375121306236972280257825 204281340979677729210193369)
    ·
      refine ⟨153211005734758296907645027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204281340979677729210193369 153211005734758296907645027)
      ·
        refine ⟨229816508602137445361467541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153211005734758296907645027 229816508602137445361467541)
        ·
          refine ⟨10772648840725192751318791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229816508602137445361467541 10772648840725192751318791)
          ·
            refine ⟨16158973261087789126978187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772648840725192751318791 16158973261087789126978187)
            ·
              refine ⟨24238459891631683690467281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16158973261087789126978187 24238459891631683690467281)
              ·
                refine ⟨18178844918723762767850461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24238459891631683690467281 18178844918723762767850461)
                ·
                  refine ⟨6817066844521411037943923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18178844918723762767850461 6817066844521411037943923)
                  ·
                    refine ⟨10225600266782116556915885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6817066844521411037943923 10225600266782116556915885)
                    ·
                      refine ⟨3834600100043293708843457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225600266782116556915885 3834600100043293708843457)
                      ·
                        rfl

theorem cell23_7467857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_7467857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467857 prefixEnd_7467857 := by exact prefixLift 7467857
  have htrace : WordTrace (prefixWord ++ tailWord_7467857) baseStart_7467857 baseEnd_7467857 := by
    simpa [prefixWord, tailWord_7467857, baseEnd_7467857] using wordTrace_append hprefix tailTrace_7467857
  have hstable : (prefixWord ++ tailWord_7467857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467857).length < 2 ^ (prefixWord ++ tailWord_7467857).sum := by decide
  have hdescent : baseEnd_7467857 < baseStart_7467857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467897 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 3, 2, 2]
def baseStart_7467897 : Nat := 118140960795 + 7467897 * 2 ^ 59
def prefixEnd_7467897 : Nat := 4983230072969 + 3 ^ 40 * 7467897 * 2
def baseEnd_7467897 : Nat := 3834620639269473552343273

theorem tailTrace_7467897 : CollatzResearch.WordTrace tailWord_7467897 prefixEnd_7467897 3834620639269473552343273 := by
  unfold tailWord_7467897
  simp only [CollatzResearch.WordTrace]
  refine ⟨272376580226092059111713945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181584386817394706074475963 272376580226092059111713945)
  ·
    refine ⟨204282435169569044333785459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272376580226092059111713945 204282435169569044333785459)
    ·
      refine ⟨306423652754353566500678189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204282435169569044333785459 306423652754353566500678189)
      ·
        refine ⟨114908869782882587437754321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306423652754353566500678189 114908869782882587437754321)
        ·
          refine ⟨86181652337161940578315741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114908869782882587437754321 86181652337161940578315741)
          ·
            refine ⟨32318119626435727716868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86181652337161940578315741 32318119626435727716868403)
            ·
              refine ⟨48477179439653591575302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32318119626435727716868403 48477179439653591575302605)
              ·
                refine ⟨18178942289870096840738477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48477179439653591575302605 18178942289870096840738477)
                ·
                  refine ⟨6817103358701286315276929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18178942289870096840738477 6817103358701286315276929)
                  ·
                    refine ⟨5112827519025964736457697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817103358701286315276929 5112827519025964736457697)
                    ·
                      refine ⟨3834620639269473552343273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112827519025964736457697 3834620639269473552343273)
                      ·
                        rfl

theorem cell23_7467897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_7467897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467897 prefixEnd_7467897 := by exact prefixLift 7467897
  have htrace : WordTrace (prefixWord ++ tailWord_7467897) baseStart_7467897 baseEnd_7467897 := by
    simpa [prefixWord, tailWord_7467897, baseEnd_7467897] using wordTrace_append hprefix tailTrace_7467897
  have hstable : (prefixWord ++ tailWord_7467897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467897).length < 2 ^ (prefixWord ++ tailWord_7467897).sum := by decide
  have hdescent : baseEnd_7467897 < baseStart_7467897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467907 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 2, 4]
def baseStart_7467907 : Nat := 118140960795 + 7467907 * 2 ^ 59
def prefixEnd_7467907 : Nat := 4983230072969 + 3 ^ 40 * 7467907 * 2
def baseEnd_7467907 : Nat := 1278208591358672837739409

theorem tailTrace_7467907 : CollatzResearch.WordTrace tailWord_7467907 prefixEnd_7467907 1278208591358672837739409 := by
  unfold tailWord_7467907
  simp only [CollatzResearch.WordTrace]
  refine ⟨272376944956055830819577975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181584629970703887213051983 272376944956055830819577975)
  ·
    refine ⟨408565417434083746229366963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272376944956055830819577975 408565417434083746229366963)
    ·
      refine ⟨612848126151125619344050445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408565417434083746229366963 612848126151125619344050445)
      ·
        refine ⟨229818047306672107254018917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612848126151125619344050445 229818047306672107254018917)
        ·
          refine ⟨43090883870001020110128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229818047306672107254018917 43090883870001020110128547)
          ·
            refine ⟨64636325805001530165192821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43090883870001020110128547 64636325805001530165192821)
            ·
              refine ⟨6059655544218893452986827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64636325805001530165192821 6059655544218893452986827)
              ·
                refine ⟨9089483316328340179480241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059655544218893452986827 9089483316328340179480241)
                ·
                  refine ⟨6817112487246255134610181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9089483316328340179480241 6817112487246255134610181)
                  ·
                    refine ⟨1278208591358672837739409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817112487246255134610181 1278208591358672837739409)
                    ·
                      rfl

theorem cell23_7467907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 4].length) (baseStart_7467907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467907 prefixEnd_7467907 := by exact prefixLift 7467907
  have htrace : WordTrace (prefixWord ++ tailWord_7467907) baseStart_7467907 baseEnd_7467907 := by
    simpa [prefixWord, tailWord_7467907, baseEnd_7467907] using wordTrace_append hprefix tailTrace_7467907
  have hstable : (prefixWord ++ tailWord_7467907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467907).length < 2 ^ (prefixWord ++ tailWord_7467907).sum := by decide
  have hdescent : baseEnd_7467907 < baseStart_7467907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467914 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7467914 : Nat := 118140960795 + 7467914 * 2 ^ 59
def prefixEnd_7467914 : Nat := 4983230072969 + 3 ^ 40 * 7467914 * 2
def baseEnd_7467914 : Nat := 3834629368440599985830695

theorem tailTrace_7467914 : CollatzResearch.WordTrace tailWord_7467914 prefixEnd_7467914 3834629368440599985830695 := by
  unfold tailWord_7467914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68094300066757617753770699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181584800178020314010055197 68094300066757617753770699)
  ·
    refine ⟨102141450100136426630656049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68094300066757617753770699 102141450100136426630656049)
    ·
      refine ⟨76606087575102319972992037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102141450100136426630656049 76606087575102319972992037)
      ·
        refine ⟨14363641420331684994936007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76606087575102319972992037 14363641420331684994936007)
        ·
          refine ⟨21545462130497527492404011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14363641420331684994936007 21545462130497527492404011)
          ·
            refine ⟨32318193195746291238606017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21545462130497527492404011 32318193195746291238606017)
            ·
              refine ⟨24238644896809718428954513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32318193195746291238606017 24238644896809718428954513)
              ·
                refine ⟨18178983672607288821715885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24238644896809718428954513 18178983672607288821715885)
                ·
                  refine ⟨6817118877227733308143457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18178983672607288821715885 6817118877227733308143457)
                  ·
                    refine ⟨5112839157920799981107593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817118877227733308143457 5112839157920799981107593)
                    ·
                      refine ⟨3834629368440599985830695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112839157920799981107593 3834629368440599985830695)
                      ·
                        rfl

theorem cell23_7467914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7467914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467914 prefixEnd_7467914 := by exact prefixLift 7467914
  have htrace : WordTrace (prefixWord ++ tailWord_7467914) baseStart_7467914 baseEnd_7467914 := by
    simpa [prefixWord, tailWord_7467914, baseEnd_7467914] using wordTrace_append hprefix tailTrace_7467914
  have hstable : (prefixWord ++ tailWord_7467914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467914).length < 2 ^ (prefixWord ++ tailWord_7467914).sum := by decide
  have hdescent : baseEnd_7467914 < baseStart_7467914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467957 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_7467957 : Nat := 118140960795 + 7467957 * 2 ^ 59
def prefixEnd_7467957 : Nat := 4983230072969 + 3 ^ 40 * 7467957 * 2
def baseEnd_7467957 : Nat := 3834651448108743317592997

theorem tailTrace_7467957 : CollatzResearch.WordTrace tailWord_7467957 prefixEnd_7467957 3834651448108743317592997 := by
  unfold tailWord_7467957
  simp only [CollatzResearch.WordTrace]
  refine ⟨272378768605874689358898125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181585845737249792905932083 272378768605874689358898125)
  ·
    refine ⟨102142038227203008509586797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272378768605874689358898125 102142038227203008509586797)
    ·
      refine ⟨38303264335201128191095049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102142038227203008509586797 38303264335201128191095049)
      ·
        refine ⟨28727448251400846143321287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38303264335201128191095049 28727448251400846143321287)
        ·
          refine ⟨43091172377101269214981931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28727448251400846143321287 43091172377101269214981931)
          ·
            refine ⟨64636758565651903822472897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43091172377101269214981931 64636758565651903822472897)
            ·
              refine ⟨48477568924238927866854673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64636758565651903822472897 48477568924238927866854673)
              ·
                refine ⟨36358176693179195900141005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48477568924238927866854673 36358176693179195900141005)
                ·
                  refine ⟨13634316259942198462552877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36358176693179195900141005 13634316259942198462552877)
                  ·
                    refine ⟨5112868597478324423457329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13634316259942198462552877 5112868597478324423457329)
                    ·
                      refine ⟨3834651448108743317592997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5112868597478324423457329 3834651448108743317592997)
                      ·
                        rfl

theorem cell23_7467957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_7467957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467957 prefixEnd_7467957 := by exact prefixLift 7467957
  have htrace : WordTrace (prefixWord ++ tailWord_7467957) baseStart_7467957 baseEnd_7467957 := by
    simpa [prefixWord, tailWord_7467957, baseEnd_7467957] using wordTrace_append hprefix tailTrace_7467957
  have hstable : (prefixWord ++ tailWord_7467957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467957).length < 2 ^ (prefixWord ++ tailWord_7467957).sum := by decide
  have hdescent : baseEnd_7467957 < baseStart_7467957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7467958 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7467958 : Nat := 118140960795 + 7467958 * 2 ^ 59
def prefixEnd_7467958 : Nat := 4983230072969 + 3 ^ 40 * 7467958 * 2
def baseEnd_7467958 : Nat := 1278217320529799271226831

theorem tailTrace_7467958 : CollatzResearch.WordTrace tailWord_7467958 prefixEnd_7467958 1278217320529799271226831 := by
  unfold tailWord_7467958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023675317429441658105283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181585870052580711019789685 17023675317429441658105283)
  ·
    refine ⟨25535512976144162487157925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17023675317429441658105283 25535512976144162487157925)
    ·
      refine ⟨4787908683027030466342111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25535512976144162487157925 4787908683027030466342111)
      ·
        refine ⟨7181863024540545699513167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787908683027030466342111 7181863024540545699513167)
        ·
          refine ⟨10772794536810818549269751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7181863024540545699513167 10772794536810818549269751)
          ·
            refine ⟨16159191805216227823904627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772794536810818549269751 16159191805216227823904627)
            ·
              refine ⟨24238787707824341735856941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159191805216227823904627 24238787707824341735856941)
              ·
                refine ⟨9089545390434128150946353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24238787707824341735856941 9089545390434128150946353)
                ·
                  refine ⟨6817159042825596113209765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9089545390434128150946353 6817159042825596113209765)
                  ·
                    refine ⟨1278217320529799271226831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817159042825596113209765 1278217320529799271226831)
                    ·
                      rfl

theorem cell23_7467958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7467958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7467958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7467958 prefixEnd_7467958 := by exact prefixLift 7467958
  have htrace : WordTrace (prefixWord ++ tailWord_7467958) baseStart_7467958 baseEnd_7467958 := by
    simpa [prefixWord, tailWord_7467958, baseEnd_7467958] using wordTrace_append hprefix tailTrace_7467958
  have hstable : (prefixWord ++ tailWord_7467958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7467958).length < 2 ^ (prefixWord ++ tailWord_7467958).sum := by decide
  have hdescent : baseEnd_7467958 < baseStart_7467958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7467958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468040 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_7468040 : Nat := 118140960795 + 7468040 * 2 ^ 59
def prefixEnd_7468040 : Nat := 4983230072969 + 3 ^ 40 * 7468040 * 2
def baseEnd_7468040 : Nat := 1278231355667688830951705

theorem tailTrace_7468040 : CollatzResearch.WordTrace tailWord_7468040 prefixEnd_7468040 1278231355667688830951705 := by
  unfold tailWord_7468040
  simp only [CollatzResearch.WordTrace]
  refine ⟨136190897932286997267084787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181587863909715996356113049 136190897932286997267084787)
  ·
    refine ⟨204286346898430495900627181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136190897932286997267084787 204286346898430495900627181)
    ·
      refine ⟨76607380086911435962735193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204286346898430495900627181 76607380086911435962735193)
      ·
        refine ⟨57455535065183576972051395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76607380086911435962735193 57455535065183576972051395)
        ·
          refine ⟨86183302597775365458077093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57455535065183576972051395 86183302597775365458077093)
          ·
            refine ⟨16159369237082881023389455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86183302597775365458077093 16159369237082881023389455)
            ·
              refine ⟨24239053855624321535084183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159369237082881023389455 24239053855624321535084183)
              ·
                refine ⟨36358580783436482302626275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24239053855624321535084183 36358580783436482302626275)
                ·
                  refine ⟨54537871175154723453939413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36358580783436482302626275 54537871175154723453939413)
                  ·
                    refine ⟨1278231355667688830951705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54537871175154723453939413 1278231355667688830951705)
                    ·
                      rfl

theorem cell23_7468040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_7468040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468040 prefixEnd_7468040 := by exact prefixLift 7468040
  have htrace : WordTrace (prefixWord ++ tailWord_7468040) baseStart_7468040 baseEnd_7468040 := by
    simpa [prefixWord, tailWord_7468040, baseEnd_7468040] using wordTrace_append hprefix tailTrace_7468040
  have hstable : (prefixWord ++ tailWord_7468040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468040).length < 2 ^ (prefixWord ++ tailWord_7468040).sum := by decide
  have hdescent : baseEnd_7468040 < baseStart_7468040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_7468073 : Nat := 118140960795 + 7468073 * 2 ^ 59
def prefixEnd_7468073 : Nat := 4983230072969 + 3 ^ 40 * 7468073 * 2
def baseEnd_7468073 : Nat := 3834711011864664863742463

theorem tailTrace_7468073 : CollatzResearch.WordTrace tailWord_7468073 prefixEnd_7468073 3834711011864664863742463 := by
  unfold tailWord_7468073
  simp only [CollatzResearch.WordTrace]
  refine ⟨272382999473454441170120873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181588666315636294113413915 272382999473454441170120873)
  ·
    refine ⟨204287249605090830877590655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272382999473454441170120873 204287249605090830877590655)
    ·
      refine ⟨306430874407636246316385983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204287249605090830877590655 306430874407636246316385983)
      ·
        refine ⟨459646311611454369474578975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306430874407636246316385983 459646311611454369474578975)
        ·
          refine ⟨689469467417181554211868463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459646311611454369474578975 689469467417181554211868463)
          ·
            refine ⟨1034204201125772331317802695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689469467417181554211868463 1034204201125772331317802695)
            ·
              refine ⟨1551306301688658496976704043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034204201125772331317802695 1551306301688658496976704043)
              ·
                refine ⟨2326959452532987745465056065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551306301688658496976704043 2326959452532987745465056065)
                ·
                  refine ⟨1745219589399740809098792049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326959452532987745465056065 1745219589399740809098792049)
                  ·
                    refine ⟨1308914692049805606824094037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745219589399740809098792049 1308914692049805606824094037)
                    ·
                      refine ⟨3834711011864664863742463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1308914692049805606824094037 3834711011864664863742463)
                      ·
                        rfl

theorem cell23_7468073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_7468073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468073 prefixEnd_7468073 := by exact prefixLift 7468073
  have htrace : WordTrace (prefixWord ++ tailWord_7468073) baseStart_7468073 baseEnd_7468073 := by
    simpa [prefixWord, tailWord_7468073, baseEnd_7468073] using wordTrace_append hprefix tailTrace_7468073
  have hstable : (prefixWord ++ tailWord_7468073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468073).length < 2 ^ (prefixWord ++ tailWord_7468073).sum := by decide
  have hdescent : baseEnd_7468073 < baseStart_7468073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468080 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_7468080 : Nat := 118140960795 + 7468080 * 2 ^ 59
def prefixEnd_7468080 : Nat := 4983230072969 + 3 ^ 40 * 7468080 * 2
def baseEnd_7468080 : Nat := 3834714606229246336354931

theorem tailTrace_7468080 : CollatzResearch.WordTrace tailWord_7468080 prefixEnd_7468080 3834714606229246336354931 := by
  unfold tailWord_7468080
  simp only [CollatzResearch.WordTrace]
  refine ⟨136191627392214540682812847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181588836522952720910417129 136191627392214540682812847)
  ·
    refine ⟨204287441088321811024219271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136191627392214540682812847 204287441088321811024219271)
    ·
      refine ⟨306431161632482716536328907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204287441088321811024219271 306431161632482716536328907)
      ·
        refine ⟨459646742448724074804493361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306431161632482716536328907 459646742448724074804493361)
        ·
          refine ⟨344735056836543056103370021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459646742448724074804493361 344735056836543056103370021)
          ·
            refine ⟨64637823156851823019381879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344735056836543056103370021 64637823156851823019381879)
            ·
              refine ⟨96956734735277734529072819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64637823156851823019381879 96956734735277734529072819)
              ·
                refine ⟨145435102102916601793609229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96956734735277734529072819 145435102102916601793609229)
                ·
                  refine ⟨54538163288593725672603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145435102102916601793609229 54538163288593725672603461)
                  ·
                    refine ⟨10225905616611323563613149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54538163288593725672603461 10225905616611323563613149)
                    ·
                      refine ⟨3834714606229246336354931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225905616611323563613149 3834714606229246336354931)
                      ·
                        rfl

theorem cell23_7468080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_7468080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468080 prefixEnd_7468080 := by exact prefixLift 7468080
  have htrace : WordTrace (prefixWord ++ tailWord_7468080) baseStart_7468080 baseEnd_7468080 := by
    simpa [prefixWord, tailWord_7468080, baseEnd_7468080] using wordTrace_append hprefix tailTrace_7468080
  have hstable : (prefixWord ++ tailWord_7468080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468080).length < 2 ^ (prefixWord ++ tailWord_7468080).sum := by decide
  have hdescent : baseEnd_7468080 < baseStart_7468080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468114 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_7468114 : Nat := 118140960795 + 7468114 * 2 ^ 59
def prefixEnd_7468114 : Nat := 4983230072969 + 3 ^ 40 * 7468114 * 2
def baseEnd_7468114 : Nat := 3834732064571499203329775

theorem tailTrace_7468114 : CollatzResearch.WordTrace tailWord_7468114 prefixEnd_7468114 3834732064571499203329775 := by
  unfold tailWord_7468114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68096123716576476293090849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181589663244203936781575597 68096123716576476293090849)
  ·
    refine ⟨51072092787432357219818137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68096123716576476293090849 51072092787432357219818137)
    ·
      refine ⟨38304069590574267914863603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51072092787432357219818137 38304069590574267914863603)
      ·
        refine ⟨57456104385861401872295405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38304069590574267914863603 57456104385861401872295405)
        ·
          refine ⟨21546039144698025702110777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57456104385861401872295405 21546039144698025702110777)
          ·
            refine ⟨16159529358523519276583083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21546039144698025702110777 16159529358523519276583083)
            ·
              refine ⟨24239294037785278914874625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159529358523519276583083 24239294037785278914874625)
              ·
                refine ⟨18179470528338959186155969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24239294037785278914874625 18179470528338959186155969)
                ·
                  refine ⟨13634602896254219389616977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18179470528338959186155969 13634602896254219389616977)
                  ·
                    refine ⟨10225952172190664542212733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13634602896254219389616977 10225952172190664542212733)
                    ·
                      refine ⟨3834732064571499203329775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10225952172190664542212733 3834732064571499203329775)
                      ·
                        rfl

theorem cell23_7468114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_7468114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468114 prefixEnd_7468114 := by exact prefixLift 7468114
  have htrace : WordTrace (prefixWord ++ tailWord_7468114) baseStart_7468114 baseEnd_7468114 := by
    simpa [prefixWord, tailWord_7468114, baseEnd_7468114] using wordTrace_append hprefix tailTrace_7468114
  have hstable : (prefixWord ++ tailWord_7468114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468114).length < 2 ^ (prefixWord ++ tailWord_7468114).sum := by decide
  have hdescent : baseEnd_7468114 < baseStart_7468114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468160 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_7468160 : Nat := 118140960795 + 7468160 * 2 ^ 59
def prefixEnd_7468160 : Nat := 4983230072969 + 3 ^ 40 * 7468160 * 2
def baseEnd_7468160 : Nat := 1278251894893868674451521

theorem tailTrace_7468160 : CollatzResearch.WordTrace tailWord_7468160 prefixEnd_7468160 1278251894893868674451521 := by
  unfold tailWord_7468160
  simp only [CollatzResearch.WordTrace]
  refine ⟨136193086312069627514268967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181590781749426170019025289 136193086312069627514268967)
  ·
    refine ⟨204289629468104441271403451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136193086312069627514268967 204289629468104441271403451)
    ·
      refine ⟨306434444202156661907105177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204289629468104441271403451 306434444202156661907105177)
      ·
        refine ⟨229825833151617496430328883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306434444202156661907105177 229825833151617496430328883)
        ·
          refine ⟨344738749727426244645493325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229825833151617496430328883 344738749727426244645493325)
          ·
            refine ⟨129277031147784841742059997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344738749727426244645493325 129277031147784841742059997)
            ·
              refine ⟨48478886680419315653272499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129277031147784841742059997 48478886680419315653272499)
              ·
                refine ⟨72718330020628973479908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48478886680419315653272499 72718330020628973479908749)
                ·
                  refine ⟨27269373757735865054965781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72718330020628973479908749 27269373757735865054965781)
                  ·
                    refine ⟨1278251894893868674451521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27269373757735865054965781 1278251894893868674451521)
                    ·
                      rfl

theorem cell23_7468160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_7468160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468160 prefixEnd_7468160 := by exact prefixLift 7468160
  have htrace : WordTrace (prefixWord ++ tailWord_7468160) baseStart_7468160 baseEnd_7468160 := by
    simpa [prefixWord, tailWord_7468160, baseEnd_7468160] using wordTrace_append hprefix tailTrace_7468160
  have hstable : (prefixWord ++ tailWord_7468160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468160).length < 2 ^ (prefixWord ++ tailWord_7468160).sum := by decide
  have hdescent : baseEnd_7468160 < baseStart_7468160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468178 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7468178 : Nat := 118140960795 + 7468178 * 2 ^ 59
def prefixEnd_7468178 : Nat := 4983230072969 + 3 ^ 40 * 7468178 * 2
def baseEnd_7468178 : Nat := 3834764927333386952929481

theorem tailTrace_7468178 : CollatzResearch.WordTrace tailWord_7468178 prefixEnd_7468178 3834764927333386952929481 := by
  unfold tailWord_7468178
  simp only [CollatzResearch.WordTrace]
  refine ⟨68096707284518511025673297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181591219425382696068462125 68096707284518511025673297)
  ·
    refine ⟨51072530463388883269254973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68096707284518511025673297 51072530463388883269254973)
    ·
      refine ⟨19152198923770831225970615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51072530463388883269254973 19152198923770831225970615)
      ·
        refine ⟨28728298385656246838955923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19152198923770831225970615 28728298385656246838955923)
        ·
          refine ⟨43092447578484370258433885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28728298385656246838955923 43092447578484370258433885)
          ·
            refine ⟨16159667841931638846912707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43092447578484370258433885 16159667841931638846912707)
            ·
              refine ⟨24239501762897458270369061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16159667841931638846912707 24239501762897458270369061)
              ·
                refine ⟨4544906580543273425694199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24239501762897458270369061 4544906580543273425694199)
                ·
                  refine ⟨6817359870814910138541299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4544906580543273425694199 6817359870814910138541299)
                  ·
                    refine ⟨10226039806222365207811949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6817359870814910138541299 10226039806222365207811949)
                    ·
                      refine ⟨3834764927333386952929481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226039806222365207811949 3834764927333386952929481)
                      ·
                        rfl

theorem cell23_7468178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7468178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468178 prefixEnd_7468178 := by exact prefixLift 7468178
  have htrace : WordTrace (prefixWord ++ tailWord_7468178) baseStart_7468178 baseEnd_7468178 := by
    simpa [prefixWord, tailWord_7468178, baseEnd_7468178] using wordTrace_append hprefix tailTrace_7468178
  have hstable : (prefixWord ++ tailWord_7468178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468178).length < 2 ^ (prefixWord ++ tailWord_7468178).sum := by decide
  have hdescent : baseEnd_7468178 < baseStart_7468178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468197 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_7468197 : Nat := 118140960795 + 7468197 * 2 ^ 59
def prefixEnd_7468197 : Nat := 4983230072969 + 3 ^ 40 * 7468197 * 2
def baseEnd_7468197 : Nat := 3834774683465822378591893

theorem tailTrace_7468197 : CollatzResearch.WordTrace tailWord_7468197 prefixEnd_7468197 3834774683465822378591893 := by
  unfold tailWord_7468197
  simp only [CollatzResearch.WordTrace]
  refine ⟨272387522125005210347634845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181591681416670140231756563 272387522125005210347634845)
  ·
    refine ⟨102145320796876953880363067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272387522125005210347634845 102145320796876953880363067)
    ·
      refine ⟨153217981195315430820544601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102145320796876953880363067 153217981195315430820544601)
      ·
        refine ⟨114913485896486573115408451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153217981195315430820544601 114913485896486573115408451)
        ·
          refine ⟨172370228844729859673112677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114913485896486573115408451 172370228844729859673112677)
          ·
            refine ⟨32319417908386848688708627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172370228844729859673112677 32319417908386848688708627)
            ·
              refine ⟨48479126862580273033062941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32319417908386848688708627 48479126862580273033062941)
              ·
                refine ⟨18179672573467602387398603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48479126862580273033062941 18179672573467602387398603)
                ·
                  refine ⟨27269508860201403581097905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18179672573467602387398603 27269508860201403581097905)
                  ·
                    refine ⟨20452131645151052685823429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27269508860201403581097905 20452131645151052685823429)
                    ·
                      refine ⟨3834774683465822378591893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20452131645151052685823429 3834774683465822378591893)
                      ·
                        rfl

theorem cell23_7468197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_7468197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468197 prefixEnd_7468197 := by exact prefixLift 7468197
  have htrace : WordTrace (prefixWord ++ tailWord_7468197) baseStart_7468197 baseEnd_7468197 := by
    simpa [prefixWord, tailWord_7468197, baseEnd_7468197] using wordTrace_append hprefix tailTrace_7468197
  have hstable : (prefixWord ++ tailWord_7468197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468197).length < 2 ^ (prefixWord ++ tailWord_7468197).sum := by decide
  have hdescent : baseEnd_7468197 < baseStart_7468197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468205 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_7468205 : Nat := 118140960795 + 7468205 * 2 ^ 59
def prefixEnd_7468205 : Nat := 4983230072969 + 3 ^ 40 * 7468205 * 2
def baseEnd_7468205 : Nat := 3834778791311058347291857

theorem tailTrace_7468205 : CollatzResearch.WordTrace tailWord_7468205 prefixEnd_7468205 3834778791311058347291857 := by
  unfold tailWord_7468205
  simp only [CollatzResearch.WordTrace]
  refine ⟨272387813908976227713926069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181591875939317485142617379 272387813908976227713926069)
  ·
    refine ⟨25536357553966521348180569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 272387813908976227713926069 25536357553966521348180569)
    ·
      refine ⟨19152268165474891011135427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25536357553966521348180569 19152268165474891011135427)
      ·
        refine ⟨28728402248212336516703141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19152268165474891011135427 28728402248212336516703141)
        ·
          refine ⟨5386575421539813096881839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28728402248212336516703141 5386575421539813096881839)
          ·
            refine ⟨8079863132309719645322759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5386575421539813096881839 8079863132309719645322759)
            ·
              refine ⟨12119794698464579467984139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079863132309719645322759 12119794698464579467984139)
              ·
                refine ⟨18179692047696869201976209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12119794698464579467984139 18179692047696869201976209)
                ·
                  refine ⟨13634769035772651901482157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18179692047696869201976209 13634769035772651901482157)
                  ·
                    refine ⟨5113038388414744463055809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13634769035772651901482157 5113038388414744463055809)
                    ·
                      refine ⟨3834778791311058347291857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113038388414744463055809 3834778791311058347291857)
                      ·
                        rfl

theorem cell23_7468205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_7468205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468205 prefixEnd_7468205 := by exact prefixLift 7468205
  have htrace : WordTrace (prefixWord ++ tailWord_7468205) baseStart_7468205 baseEnd_7468205 := by
    simpa [prefixWord, tailWord_7468205, baseEnd_7468205] using wordTrace_append hprefix tailTrace_7468205
  have hstable : (prefixWord ++ tailWord_7468205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468205).length < 2 ^ (prefixWord ++ tailWord_7468205).sum := by decide
  have hdescent : baseEnd_7468205 < baseStart_7468205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468221 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7468221 : Nat := 118140960795 + 7468221 * 2 ^ 59
def prefixEnd_7468221 : Nat := 4983230072969 + 3 ^ 40 * 7468221 * 2
def baseEnd_7468221 : Nat := 3834787007001530284691783

theorem tailTrace_7468221 : CollatzResearch.WordTrace tailWord_7468221 prefixEnd_7468221 3834787007001530284691783 := by
  unfold tailWord_7468221
  simp only [CollatzResearch.WordTrace]
  refine ⟨272388397476918262446508517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181592264984612174964339011 272388397476918262446508517)
  ·
    refine ⟨51072824526922174208720347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 272388397476918262446508517 51072824526922174208720347)
    ·
      refine ⟨76609236790383261313080521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51072824526922174208720347 76609236790383261313080521)
      ·
        refine ⟨57456927592787445984810391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76609236790383261313080521 57456927592787445984810391)
        ·
          refine ⟨86185391389181168977215587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57456927592787445984810391 86185391389181168977215587)
          ·
            refine ⟨129278087083771753465823381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86185391389181168977215587 129278087083771753465823381)
            ·
              refine ⟨6059910332051800943710471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129278087083771753465823381 6059910332051800943710471)
              ·
                refine ⟨9089865498077701415565707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6059910332051800943710471 9089865498077701415565707)
                ·
                  refine ⟨13634798247116552123348561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9089865498077701415565707 13634798247116552123348561)
                  ·
                    refine ⟨10226098685337414092511421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13634798247116552123348561 10226098685337414092511421)
                    ·
                      refine ⟨3834787007001530284691783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226098685337414092511421 3834787007001530284691783)
                      ·
                        rfl

theorem cell23_7468221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7468221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468221 prefixEnd_7468221 := by exact prefixLift 7468221
  have htrace : WordTrace (prefixWord ++ tailWord_7468221) baseStart_7468221 baseEnd_7468221 := by
    simpa [prefixWord, tailWord_7468221, baseEnd_7468221] using wordTrace_append hprefix tailTrace_7468221
  have hstable : (prefixWord ++ tailWord_7468221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468221).length < 2 ^ (prefixWord ++ tailWord_7468221).sum := by decide
  have hdescent : baseEnd_7468221 < baseStart_7468221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468228 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_7468228 : Nat := 118140960795 + 7468228 * 2 ^ 59
def prefixEnd_7468228 : Nat := 4983230072969 + 3 ^ 40 * 7468228 * 2
def baseEnd_7468228 : Nat := 1278263533788703919101417

theorem tailTrace_7468228 : CollatzResearch.WordTrace tailWord_7468228 prefixEnd_7468228 1278263533788703919101417 := by
  unfold tailWord_7468228
  simp only [CollatzResearch.WordTrace]
  refine ⟨136194326393946451321006669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181592435191928601761342225 136194326393946451321006669)
  ·
    refine ⟨51072872397729919245377501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136194326393946451321006669 51072872397729919245377501)
    ·
      refine ⟨19152327149148719717016563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51072872397729919245377501 19152327149148719717016563)
      ·
        refine ⟨28728490723723079575524845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19152327149148719717016563 28728490723723079575524845)
        ·
          refine ⟨10773184021396154840821817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28728490723723079575524845 10773184021396154840821817)
          ·
            refine ⟨8079888016047116130616363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10773184021396154840821817 8079888016047116130616363)
            ·
              refine ⟨12119832024070674195924545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8079888016047116130616363 12119832024070674195924545)
              ·
                refine ⟨9089874018053005646943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12119832024070674195924545 9089874018053005646943409)
                ·
                  refine ⟨6817405513539754235207557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9089874018053005646943409 6817405513539754235207557)
                  ·
                    refine ⟨1278263533788703919101417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817405513539754235207557 1278263533788703919101417)
                    ·
                      rfl

theorem cell23_7468228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_7468228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468228 prefixEnd_7468228 := by exact prefixLift 7468228
  have htrace : WordTrace (prefixWord ++ tailWord_7468228) baseStart_7468228 baseEnd_7468228 := by
    simpa [prefixWord, tailWord_7468228, baseEnd_7468228] using wordTrace_append hprefix tailTrace_7468228
  have hstable : (prefixWord ++ tailWord_7468228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468228).length < 2 ^ (prefixWord ++ tailWord_7468228).sum := by decide
  have hdescent : baseEnd_7468228 < baseStart_7468228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468291 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 4, 2, 2]
def baseStart_7468291 : Nat := 118140960795 + 7468291 * 2 ^ 59
def prefixEnd_7468291 : Nat := 4983230072969 + 3 ^ 40 * 7468291 * 2
def baseEnd_7468291 : Nat := 3834822950647345010816461

theorem tailTrace_7468291 : CollatzResearch.WordTrace tailWord_7468291 prefixEnd_7468291 3834822950647345010816461 := by
  unfold tailWord_7468291
  simp only [CollatzResearch.WordTrace]
  refine ⟨272390950586664664401556727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181593967057776442934371151 272390950586664664401556727)
  ·
    refine ⟨408586425879996996602335091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272390950586664664401556727 408586425879996996602335091)
    ·
      refine ⟨612879638819995494903502637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408586425879996996602335091 612879638819995494903502637)
      ·
        refine ⟨229829864557498310588813489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612879638819995494903502637 229829864557498310588813489)
        ·
          refine ⟨172372398418123732941610117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229829864557498310588813489 172372398418123732941610117)
          ·
            refine ⟨32319824703398199926551897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172372398418123732941610117 32319824703398199926551897)
            ·
              refine ⟨24239868527548649944913923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32319824703398199926551897 24239868527548649944913923)
              ·
                refine ⟨36359802791322974917370885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24239868527548649944913923 36359802791322974917370885)
                ·
                  refine ⟨6817463023373057797007041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36359802791322974917370885 6817463023373057797007041)
                  ·
                    refine ⟨5113097267529793347755281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817463023373057797007041 5113097267529793347755281)
                    ·
                      refine ⟨3834822950647345010816461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113097267529793347755281 3834822950647345010816461)
                      ·
                        rfl

theorem cell23_7468291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_7468291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468291 prefixEnd_7468291 := by exact prefixLift 7468291
  have htrace : WordTrace (prefixWord ++ tailWord_7468291) baseStart_7468291 baseEnd_7468291 := by
    simpa [prefixWord, tailWord_7468291, baseEnd_7468291] using wordTrace_append hprefix tailTrace_7468291
  have hstable : (prefixWord ++ tailWord_7468291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468291).length < 2 ^ (prefixWord ++ tailWord_7468291).sum := by decide
  have hdescent : baseEnd_7468291 < baseStart_7468291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468348 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 5]
def baseStart_7468348 : Nat := 118140960795 + 7468348 * 2 ^ 59
def prefixEnd_7468348 : Nat := 4983230072969 + 3 ^ 40 * 7468348 * 2
def baseEnd_7468348 : Nat := 426094691004961254200411

theorem tailTrace_7468348 : CollatzResearch.WordTrace tailWord_7468348 prefixEnd_7468348 426094691004961254200411 := by
  unfold tailWord_7468348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136196514773729081568190849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181595353031638775424254465 136196514773729081568190849)
  ·
    refine ⟨102147386080296811176143137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136196514773729081568190849 102147386080296811176143137)
    ·
      refine ⟨76610539560222608382107353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102147386080296811176143137 76610539560222608382107353)
      ·
        refine ⟨57457904670166956286580515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76610539560222608382107353 57457904670166956286580515)
        ·
          refine ⟨86186857005250434429870773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57457904670166956286580515 86186857005250434429870773)
          ·
            refine ⟨8080017844242228227800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86186857005250434429870773 8080017844242228227800385)
            ·
              refine ⟨6060013383181671170850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080017844242228227800385 6060013383181671170850289)
              ·
                refine ⟨4545010037386253378137717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060013383181671170850289 4545010037386253378137717)
                ·
                  refine ⟨426094691004961254200411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4545010037386253378137717 426094691004961254200411)
                  ·
                    rfl

theorem cell23_7468348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_7468348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468348 prefixEnd_7468348 := by exact prefixLift 7468348
  have htrace : WordTrace (prefixWord ++ tailWord_7468348) baseStart_7468348 baseEnd_7468348 := by
    simpa [prefixWord, tailWord_7468348, baseEnd_7468348] using wordTrace_append hprefix tailTrace_7468348
  have hstable : (prefixWord ++ tailWord_7468348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468348).length < 2 ^ (prefixWord ++ tailWord_7468348).sum := by decide
  have hdescent : baseEnd_7468348 < baseStart_7468348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468407 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_7468407 : Nat := 118140960795 + 7468407 * 2 ^ 59
def prefixEnd_7468407 : Nat := 4983230072969 + 3 ^ 40 * 7468407 * 2
def baseEnd_7468407 : Nat := 3834882514403266556965927

theorem tailTrace_7468407 : CollatzResearch.WordTrace tailWord_7468407 prefixEnd_7468407 3834882514403266556965927 := by
  unfold tailWord_7468407
  simp only [CollatzResearch.WordTrace]
  refine ⟨272395181454244416212779475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181596787636162944141852983 272395181454244416212779475)
  ·
    refine ⟨408592772181366624319169213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272395181454244416212779475 408592772181366624319169213)
    ·
      refine ⟨153222289568012484119688455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408592772181366624319169213 153222289568012484119688455)
      ·
        refine ⟨229833434352018726179532683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153222289568012484119688455 229833434352018726179532683)
        ·
          refine ⟨344750151528028089269299025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229833434352018726179532683 344750151528028089269299025)
          ·
            refine ⟨258562613646021066951974269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344750151528028089269299025 258562613646021066951974269)
            ·
              refine ⟨96960980117257900106990351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258562613646021066951974269 96960980117257900106990351)
              ·
                refine ⟨145441470175886850160485527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96960980117257900106990351 145441470175886850160485527)
                ·
                  refine ⟨218162205263830275240728291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145441470175886850160485527 218162205263830275240728291)
                  ·
                    refine ⟨327243307895745412861092437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218162205263830275240728291 327243307895745412861092437)
                    ·
                      refine ⟨3834882514403266556965927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 327243307895745412861092437 3834882514403266556965927)
                      ·
                        rfl

theorem cell23_7468407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_7468407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468407 prefixEnd_7468407 := by exact prefixLift 7468407
  have htrace : WordTrace (prefixWord ++ tailWord_7468407) baseStart_7468407 baseEnd_7468407 := by
    simpa [prefixWord, tailWord_7468407, baseEnd_7468407] using wordTrace_append hprefix tailTrace_7468407
  have hstable : (prefixWord ++ tailWord_7468407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468407).length < 2 ^ (prefixWord ++ tailWord_7468407).sum := by decide
  have hdescent : baseEnd_7468407 < baseStart_7468407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468418 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7468418 : Nat := 118140960795 + 7468418 * 2 ^ 59
def prefixEnd_7468418 : Nat := 4983230072969 + 3 ^ 40 * 7468418 * 2
def baseEnd_7468418 : Nat := 3834888162690466013928377

theorem tailTrace_7468418 : CollatzResearch.WordTrace tailWord_7468418 prefixEnd_7468418 3834888162690466013928377 := by
  unfold tailWord_7468418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68098895664301141272857477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181597055104803043394286605 68098895664301141272857477)
  ·
    refine ⟨12768542937056463988660777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68098895664301141272857477 12768542937056463988660777)
    ·
      refine ⟨9576407202792347991495583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12768542937056463988660777 9576407202792347991495583)
      ·
        refine ⟨14364610804188521987243375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576407202792347991495583 14364610804188521987243375)
        ·
          refine ⟨21546916206282782980865063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14364610804188521987243375 21546916206282782980865063)
          ·
            refine ⟨32320374309424174471297595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21546916206282782980865063 32320374309424174471297595)
            ·
              refine ⟨48480561464136261706946393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32320374309424174471297595 48480561464136261706946393)
              ·
                refine ⟨36360421098102196280209795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48480561464136261706946393 36360421098102196280209795)
                ·
                  refine ⟨54540631647153294420314693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36360421098102196280209795 54540631647153294420314693)
                  ·
                    refine ⟨10226368433841242703809005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54540631647153294420314693 10226368433841242703809005)
                    ·
                      refine ⟨3834888162690466013928377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226368433841242703809005 3834888162690466013928377)
                      ·
                        rfl

theorem cell23_7468418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7468418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468418 prefixEnd_7468418 := by exact prefixLift 7468418
  have htrace : WordTrace (prefixWord ++ tailWord_7468418) baseStart_7468418 baseEnd_7468418 := by
    simpa [prefixWord, tailWord_7468418, baseEnd_7468418] using wordTrace_append hprefix tailTrace_7468418
  have hstable : (prefixWord ++ tailWord_7468418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468418).length < 2 ^ (prefixWord ++ tailWord_7468418).sum := by decide
  have hdescent : baseEnd_7468418 < baseStart_7468418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468441 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 5, 2]
def baseStart_7468441 : Nat := 118140960795 + 7468441 * 2 ^ 59
def prefixEnd_7468441 : Nat := 4983230072969 + 3 ^ 40 * 7468441 * 2
def baseEnd_7468441 : Nat := 3834899972745519423940771

theorem tailTrace_7468441 : CollatzResearch.WordTrace tailWord_7468441 prefixEnd_7468441 3834899972745519423940771 := by
  unfold tailWord_7468441
  simp only [CollatzResearch.WordTrace]
  refine ⟨272396421536121240019517177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181597614357414160013011451 272396421536121240019517177)
  ·
    refine ⟨204297316152090930014637883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272396421536121240019517177 204297316152090930014637883)
    ·
      refine ⟨306445974228136395021956825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204297316152090930014637883 306445974228136395021956825)
      ·
        refine ⟨229834480671102296266467619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306445974228136395021956825 229834480671102296266467619)
        ·
          refine ⟨344751721006653444399701429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229834480671102296266467619 344751721006653444399701429)
          ·
            refine ⟨32320473844373760412472009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 344751721006653444399701429 32320473844373760412472009)
            ·
              refine ⟨24240355383280320309354007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32320473844373760412472009 24240355383280320309354007)
              ·
                refine ⟨36360533074920480464031011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24240355383280320309354007 36360533074920480464031011)
                ·
                  refine ⟨54540799612380720696046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36360533074920480464031011 54540799612380720696046517)
                  ·
                    refine ⟨5113199963660692565254361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54540799612380720696046517 5113199963660692565254361)
                    ·
                      refine ⟨3834899972745519423940771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113199963660692565254361 3834899972745519423940771)
                      ·
                        rfl

theorem cell23_7468441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_7468441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468441 prefixEnd_7468441 := by exact prefixLift 7468441
  have htrace : WordTrace (prefixWord ++ tailWord_7468441) baseStart_7468441 baseEnd_7468441 := by
    simpa [prefixWord, tailWord_7468441, baseEnd_7468441] using wordTrace_append hprefix tailTrace_7468441
  have hstable : (prefixWord ++ tailWord_7468441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468441).length < 2 ^ (prefixWord ++ tailWord_7468441).sum := by decide
  have hdescent : baseEnd_7468441 < baseStart_7468441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468474 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_7468474 : Nat := 118140960795 + 7468474 * 2 ^ 59
def prefixEnd_7468474 : Nat := 4983230072969 + 3 ^ 40 * 7468474 * 2
def baseEnd_7468474 : Nat := 3834916917607117794828119

theorem tailTrace_7468474 : CollatzResearch.WordTrace tailWord_7468474 prefixEnd_7468474 3834916917607117794828119 := by
  unfold tailWord_7468474
  simp only [CollatzResearch.WordTrace]
  refine ⟨68099406286250421663867119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181598416763334457770312317 68099406286250421663867119)
  ·
    refine ⟨102149109429375632495800679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68099406286250421663867119 102149109429375632495800679)
    ·
      refine ⟨153223664144063448743701019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102149109429375632495800679 153223664144063448743701019)
      ·
        refine ⟨229835496216095173115551529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153223664144063448743701019 229835496216095173115551529)
        ·
          refine ⟨172376622162071379836663647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229835496216095173115551529 172376622162071379836663647)
          ·
            refine ⟨258564933243107069754995471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172376622162071379836663647 258564933243107069754995471)
            ·
              refine ⟨387847399864660604632493207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258564933243107069754995471 387847399864660604632493207)
              ·
                refine ⟨581771099796990906948739811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387847399864660604632493207 581771099796990906948739811)
                ·
                  refine ⟨872656649695486360423109717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581771099796990906948739811 872656649695486360423109717)
                  ·
                    refine ⟨10226445113618980786208317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 872656649695486360423109717 10226445113618980786208317)
                    ·
                      refine ⟨3834916917607117794828119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226445113618980786208317 3834916917607117794828119)
                      ·
                        rfl

theorem cell23_7468474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_7468474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468474 prefixEnd_7468474 := by exact prefixLift 7468474
  have htrace : WordTrace (prefixWord ++ tailWord_7468474) baseStart_7468474 baseEnd_7468474 := by
    simpa [prefixWord, tailWord_7468474, baseEnd_7468474] using wordTrace_append hprefix tailTrace_7468474
  have hstable : (prefixWord ++ tailWord_7468474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468474).length < 2 ^ (prefixWord ++ tailWord_7468474).sum := by decide
  have hdescent : baseEnd_7468474 < baseStart_7468474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468488 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_7468488 : Nat := 118140960795 + 7468488 * 2 ^ 59
def prefixEnd_7468488 : Nat := 4983230072969 + 3 ^ 40 * 7468488 * 2
def baseEnd_7468488 : Nat := 3834924106336280740053055

theorem tailTrace_7468488 : CollatzResearch.WordTrace tailWord_7468488 prefixEnd_7468488 3834924106336280740053055 := by
  unfold tailWord_7468488
  simp only [CollatzResearch.WordTrace]
  refine ⟨136199067883475483523239059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181598757177967311364318745 136199067883475483523239059)
  ·
    refine ⟨204298601825213225284858589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136199067883475483523239059 204298601825213225284858589)
    ·
      refine ⟨76611975684454959481821971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204298601825213225284858589 76611975684454959481821971)
      ·
        refine ⟨114917963526682439222732957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76611975684454959481821971 114917963526682439222732957)
        ·
          refine ⟨43094236322505914708524859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114917963526682439222732957 43094236322505914708524859)
          ·
            refine ⟨64641354483758872062787289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43094236322505914708524859 64641354483758872062787289)
            ·
              refine ⟨48481015862819154047090467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64641354483758872062787289 48481015862819154047090467)
              ·
                refine ⟨72721523794228731070635701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48481015862819154047090467 72721523794228731070635701)
                ·
                  refine ⟨6817642855708943537872097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72721523794228731070635701 6817642855708943537872097)
                  ·
                    refine ⟨5113232141781707653404073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6817642855708943537872097 5113232141781707653404073)
                    ·
                      refine ⟨3834924106336280740053055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113232141781707653404073 3834924106336280740053055)
                      ·
                        rfl

theorem cell23_7468488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_7468488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468488 prefixEnd_7468488 := by exact prefixLift 7468488
  have htrace : WordTrace (prefixWord ++ tailWord_7468488) baseStart_7468488 baseEnd_7468488 := by
    simpa [prefixWord, tailWord_7468488, baseEnd_7468488] using wordTrace_append hprefix tailTrace_7468488
  have hstable : (prefixWord ++ tailWord_7468488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468488).length < 2 ^ (prefixWord ++ tailWord_7468488).sum := by decide
  have hdescent : baseEnd_7468488 < baseStart_7468488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468494 : List Nat := [4, 1, 1, 1, 2, 1, 4, 9]
def baseStart_7468494 : Nat := 118140960795 + 7468494 * 2 ^ 59
def prefixEnd_7468494 : Nat := 4983230072969 + 3 ^ 40 * 7468494 * 2
def baseEnd_7468494 : Nat := 142034340267415100614001

theorem tailTrace_7468494 : CollatzResearch.WordTrace tailWord_7468494 prefixEnd_7468494 142034340267415100614001 := by
  unfold tailWord_7468494
  simp only [CollatzResearch.WordTrace]
  refine ⟨34049794325616153758899567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181598903069952820047464357 34049794325616153758899567)
  ·
    refine ⟨51074691488424230638349351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34049794325616153758899567 51074691488424230638349351)
    ·
      refine ⟨76612037232636345957524027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51074691488424230638349351 76612037232636345957524027)
      ·
        refine ⟨114918055848954518936286041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76612037232636345957524027 114918055848954518936286041)
        ·
          refine ⟨86188541886715889202214531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114918055848954518936286041 86188541886715889202214531)
          ·
            refine ⟨129282812830073833803321797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86188541886715889202214531 129282812830073833803321797)
            ·
              refine ⟨24240527405638843838122837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129282812830073833803321797 24240527405638843838122837)
              ·
                refine ⟨142034340267415100614001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24240527405638843838122837 142034340267415100614001)
                ·
                  rfl

theorem cell23_7468494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_7468494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468494 prefixEnd_7468494 := by exact prefixLift 7468494
  have htrace : WordTrace (prefixWord ++ tailWord_7468494) baseStart_7468494 baseEnd_7468494 := by
    simpa [prefixWord, tailWord_7468494, baseEnd_7468494] using wordTrace_append hprefix tailTrace_7468494
  have hstable : (prefixWord ++ tailWord_7468494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468494).length < 2 ^ (prefixWord ++ tailWord_7468494).sum := by decide
  have hdescent : baseEnd_7468494 < baseStart_7468494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468501 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7468501 : Nat := 118140960795 + 7468501 * 2 ^ 59
def prefixEnd_7468501 : Nat := 4983230072969 + 3 ^ 40 * 7468501 * 2
def baseEnd_7468501 : Nat := 3834930781584789189190495

theorem tailTrace_7468501 : CollatzResearch.WordTrace tailWord_7468501 prefixEnd_7468501 3834930781584789189190495 := by
  unfold tailWord_7468501
  simp only [CollatzResearch.WordTrace]
  refine ⟨272398609915903870266701357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181599073277269246844467571 272398609915903870266701357)
  ·
    refine ⟨102149478718463951350013009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272398609915903870266701357 102149478718463951350013009)
    ·
      refine ⟨76612109038847963512509757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102149478718463951350013009 76612109038847963512509757)
      ·
        refine ⟨28729540889567986317191159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76612109038847963512509757 28729540889567986317191159)
        ·
          refine ⟨43094311334351979475786739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729540889567986317191159 43094311334351979475786739)
          ·
            refine ⟨64641467001527969213680109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43094311334351979475786739 64641467001527969213680109)
            ·
              refine ⟨24240550125572988455130041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64641467001527969213680109 24240550125572988455130041)
              ·
                refine ⟨18180412594179741341347531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24240550125572988455130041 18180412594179741341347531)
                ·
                  refine ⟨27270618891269612012021297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18180412594179741341347531 27270618891269612012021297)
                  ·
                    refine ⟨20452964168452209009015973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27270618891269612012021297 20452964168452209009015973)
                    ·
                      refine ⟨3834930781584789189190495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20452964168452209009015973 3834930781584789189190495)
                      ·
                        rfl

theorem cell23_7468501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7468501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468501 prefixEnd_7468501 := by exact prefixLift 7468501
  have htrace : WordTrace (prefixWord ++ tailWord_7468501) baseStart_7468501 baseEnd_7468501 := by
    simpa [prefixWord, tailWord_7468501, baseEnd_7468501] using wordTrace_append hprefix tailTrace_7468501
  have hstable : (prefixWord ++ tailWord_7468501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468501).length < 2 ^ (prefixWord ++ tailWord_7468501).sum := by decide
  have hdescent : baseEnd_7468501 < baseStart_7468501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468521 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_7468521 : Nat := 118140960795 + 7468521 * 2 ^ 59
def prefixEnd_7468521 : Nat := 4983230072969 + 3 ^ 40 * 7468521 * 2
def baseEnd_7468521 : Nat := 3834941051197879110940403

theorem tailTrace_7468521 : CollatzResearch.WordTrace tailWord_7468521 prefixEnd_7468521 3834941051197879110940403 := by
  unfold tailWord_7468521
  simp only [CollatzResearch.WordTrace]
  refine ⟨272399339375831413682429417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181599559583887609121619611 272399339375831413682429417)
  ·
    refine ⟨204299504531873560261822063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272399339375831413682429417 204299504531873560261822063)
    ·
      refine ⟨306449256797810340392733095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204299504531873560261822063 306449256797810340392733095)
      ·
        refine ⟨459673885196715510589099643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306449256797810340392733095 459673885196715510589099643)
        ·
          refine ⟨689510827795073265883649465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459673885196715510589099643 689510827795073265883649465)
          ·
            refine ⟨517133120846304949412737099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689510827795073265883649465 517133120846304949412737099)
            ·
              refine ⟨775699681269457424119105649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517133120846304949412737099 775699681269457424119105649)
              ·
                refine ⟨581774760952093068089329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775699681269457424119105649 581774760952093068089329237)
                ·
                  refine ⟨6817672979907340641671827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 581774760952093068089329237 6817672979907340641671827)
                  ·
                    refine ⟨10226509469861010962507741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6817672979907340641671827 10226509469861010962507741)
                    ·
                      refine ⟨3834941051197879110940403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226509469861010962507741 3834941051197879110940403)
                      ·
                        rfl

theorem cell23_7468521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_7468521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468521 prefixEnd_7468521 := by exact prefixLift 7468521
  have htrace : WordTrace (prefixWord ++ tailWord_7468521) baseStart_7468521 baseEnd_7468521 := by
    simpa [prefixWord, tailWord_7468521, baseEnd_7468521] using wordTrace_append hprefix tailTrace_7468521
  have hstable : (prefixWord ++ tailWord_7468521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468521).length < 2 ^ (prefixWord ++ tailWord_7468521).sum := by decide
  have hdescent : baseEnd_7468521 < baseStart_7468521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468538 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_7468538 : Nat := 118140960795 + 7468538 * 2 ^ 59
def prefixEnd_7468538 : Nat := 4983230072969 + 3 ^ 40 * 7468538 * 2
def baseEnd_7468538 : Nat := 3834949780369005544427825

theorem tailTrace_7468538 : CollatzResearch.WordTrace tailWord_7468538 prefixEnd_7468538 3834949780369005544427825 := by
  unfold tailWord_7468538
  simp only [CollatzResearch.WordTrace]
  refine ⟨68099989854192456396449567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181599972944513217057198845 68099989854192456396449567)
  ·
    refine ⟨102149984781288684594674351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68099989854192456396449567 102149984781288684594674351)
    ·
      refine ⟨153224977171933026892011527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102149984781288684594674351 153224977171933026892011527)
      ·
        refine ⟨229837465757899540338017291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153224977171933026892011527 229837465757899540338017291)
        ·
          refine ⟨344756198636849310507025937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229837465757899540338017291 344756198636849310507025937)
          ·
            refine ⟨258567148977636982880269453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344756198636849310507025937 258567148977636982880269453)
            ·
              refine ⟨96962680866613868580101045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258567148977636982880269453 96962680866613868580101045)
              ·
                refine ⟨9090251331245050179384473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96962680866613868580101045 9090251331245050179384473)
                ·
                  refine ⟨6817688498433787634538355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090251331245050179384473 6817688498433787634538355)
                  ·
                    refine ⟨10226532747650681451807533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6817688498433787634538355 10226532747650681451807533)
                    ·
                      refine ⟨3834949780369005544427825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226532747650681451807533 3834949780369005544427825)
                      ·
                        rfl

theorem cell23_7468538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_7468538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468538 prefixEnd_7468538 := by exact prefixLift 7468538
  have htrace : WordTrace (prefixWord ++ tailWord_7468538) baseStart_7468538 baseEnd_7468538 := by
    simpa [prefixWord, tailWord_7468538, baseEnd_7468538] using wordTrace_append hprefix tailTrace_7468538
  have hstable : (prefixWord ++ tailWord_7468538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468538).length < 2 ^ (prefixWord ++ tailWord_7468538).sum := by decide
  have hdescent : baseEnd_7468538 < baseStart_7468538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468565 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_7468565 : Nat := 118140960795 + 7468565 * 2 ^ 59
def prefixEnd_7468565 : Nat := 4983230072969 + 3 ^ 40 * 7468565 * 2
def baseEnd_7468565 : Nat := 3834963644346676938790201

theorem tailTrace_7468565 : CollatzResearch.WordTrace tailWord_7468565 prefixEnd_7468565 3834963644346676938790201 := by
  unfold tailWord_7468565
  simp only [CollatzResearch.WordTrace]
  refine ⟨272400944187672009197031149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181600629458448006131354099 272400944187672009197031149)
  ·
    refine ⟨102150354070377003448886681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272400944187672009197031149 102150354070377003448886681)
    ·
      refine ⟨76612765552782752586665011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102150354070377003448886681 76612765552782752586665011)
      ·
        refine ⟨114919148329174128879997517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76612765552782752586665011 114919148329174128879997517)
        ·
          refine ⟨43094680623440298329999069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114919148329174128879997517 43094680623440298329999069)
          ·
            refine ⟨16160505233790111873749651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43094680623440298329999069 16160505233790111873749651)
            ·
              refine ⟨24240757850685167810624477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16160505233790111873749651 24240757850685167810624477)
              ·
                refine ⟨9090284194006937928984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24240757850685167810624477 9090284194006937928984179)
                ·
                  refine ⟨13635426291010406893476269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9090284194006937928984179 13635426291010406893476269)
                  ·
                    refine ⟨5113284859128902585053601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13635426291010406893476269 5113284859128902585053601)
                    ·
                      refine ⟨3834963644346676938790201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113284859128902585053601 3834963644346676938790201)
                      ·
                        rfl

theorem cell23_7468565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_7468565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468565 prefixEnd_7468565 := by exact prefixLift 7468565
  have htrace : WordTrace (prefixWord ++ tailWord_7468565) baseStart_7468565 baseEnd_7468565 := by
    simpa [prefixWord, tailWord_7468565, baseEnd_7468565] using wordTrace_append hprefix tailTrace_7468565
  have hstable : (prefixWord ++ tailWord_7468565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468565).length < 2 ^ (prefixWord ++ tailWord_7468565).sum := by decide
  have hdescent : baseEnd_7468565 < baseStart_7468565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468578 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_7468578 : Nat := 118140960795 + 7468578 * 2 ^ 59
def prefixEnd_7468578 : Nat := 4983230072969 + 3 ^ 40 * 7468578 * 2
def baseEnd_7468578 : Nat := 3834970319595185387927641

theorem tailTrace_7468578 : CollatzResearch.WordTrace tailWord_7468578 prefixEnd_7468578 3834970319595185387927641 := by
  unfold tailWord_7468578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68100354584156228104313597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181600945557749941611502925 68100354584156228104313597)
  ·
    refine ⟨25537632969058585539117599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68100354584156228104313597 25537632969058585539117599)
    ·
      refine ⟨38306449453587878308676399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25537632969058585539117599 38306449453587878308676399)
      ·
        refine ⟨57459674180381817463014599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38306449453587878308676399 57459674180381817463014599)
        ·
          refine ⟨86189511270572726194521899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57459674180381817463014599 86189511270572726194521899)
          ·
            refine ⟨129284266905859089291782849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86189511270572726194521899 129284266905859089291782849)
            ·
              refine ⟨96963200179394316968837137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129284266905859089291782849 96963200179394316968837137)
              ·
                refine ⟨72722400134545737726627853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96963200179394316968837137 72722400134545737726627853)
                ·
                  refine ⟨27270900050454651647485445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72722400134545737726627853 27270900050454651647485445)
                  ·
                    refine ⟨5113293759460247183903521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27270900050454651647485445 5113293759460247183903521)
                    ·
                      refine ⟨3834970319595185387927641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113293759460247183903521 3834970319595185387927641)
                      ·
                        rfl

theorem cell23_7468578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_7468578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468578 prefixEnd_7468578 := by exact prefixLift 7468578
  have htrace : WordTrace (prefixWord ++ tailWord_7468578) baseStart_7468578 baseEnd_7468578 := by
    simpa [prefixWord, tailWord_7468578, baseEnd_7468578] using wordTrace_append hprefix tailTrace_7468578
  have hstable : (prefixWord ++ tailWord_7468578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468578).length < 2 ^ (prefixWord ++ tailWord_7468578).sum := by decide
  have hdescent : baseEnd_7468578 < baseStart_7468578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468595 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 4, 2]
def baseStart_7468595 : Nat := 118140960795 + 7468595 * 2 ^ 59
def prefixEnd_7468595 : Nat := 4983230072969 + 3 ^ 40 * 7468595 * 2
def baseEnd_7468595 : Nat := 3834979048766311821415063

theorem tailTrace_7468595 : CollatzResearch.WordTrace tailWord_7468595 prefixEnd_7468595 3834979048766311821415063 := by
  unfold tailWord_7468595
  simp only [CollatzResearch.WordTrace]
  refine ⟨272402038377563324320623239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181601358918375549547082159 272402038377563324320623239)
  ·
    refine ⟨408603057566344986480934859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272402038377563324320623239 408603057566344986480934859)
    ·
      refine ⟨612904586349517479721402289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408603057566344986480934859 612904586349517479721402289)
      ·
        refine ⟨459678439762138109791051717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612904586349517479721402289 459678439762138109791051717)
        ·
          refine ⟨86189707455400895585822197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459678439762138109791051717 86189707455400895585822197)
          ·
            refine ⟨8080285073943833961170831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86189707455400895585822197 8080285073943833961170831)
            ·
              refine ⟨12120427610915750941756247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8080285073943833961170831 12120427610915750941756247)
              ·
                refine ⟨18180641416373626412634371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120427610915750941756247 18180641416373626412634371)
                ·
                  refine ⟨27270962124560439618951557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18180641416373626412634371 27270962124560439618951557)
                  ·
                    refine ⟨5113305398355082428553417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27270962124560439618951557 5113305398355082428553417)
                    ·
                      refine ⟨3834979048766311821415063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113305398355082428553417 3834979048766311821415063)
                      ·
                        rfl

theorem cell23_7468595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4, 2].length) (baseStart_7468595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468595 prefixEnd_7468595 := by exact prefixLift 7468595
  have htrace : WordTrace (prefixWord ++ tailWord_7468595) baseStart_7468595 baseEnd_7468595 := by
    simpa [prefixWord, tailWord_7468595, baseEnd_7468595] using wordTrace_append hprefix tailTrace_7468595
  have hstable : (prefixWord ++ tailWord_7468595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468595).length < 2 ^ (prefixWord ++ tailWord_7468595).sum := by decide
  have hdescent : baseEnd_7468595 < baseStart_7468595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468601 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 7]
def baseStart_7468601 : Nat := 118140960795 + 7468601 * 2 ^ 59
def prefixEnd_7468601 : Nat := 4983230072969 + 3 ^ 40 * 7468601 * 2
def baseEnd_7468601 : Nat := 426109125516693199771115

theorem tailTrace_7468601 : CollatzResearch.WordTrace tailWord_7468601 prefixEnd_7468601 426109125516693199771115 := by
  unfold tailWord_7468601
  simp only [CollatzResearch.WordTrace]
  refine ⟨272402257215541587345341657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181601504810361058230227771 272402257215541587345341657)
  ·
    refine ⟨204301692911656190509006243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272402257215541587345341657 204301692911656190509006243)
    ·
      refine ⟨306452539367484285763509365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204301692911656190509006243 306452539367484285763509365)
      ·
        refine ⟨28729925565701651790329003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 306452539367484285763509365 28729925565701651790329003)
        ·
          refine ⟨43094888348552477685493505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729925565701651790329003 43094888348552477685493505)
          ·
            refine ⟨32321166261414358264120129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43094888348552477685493505 32321166261414358264120129)
            ·
              refine ⟨24240874696060768698090097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32321166261414358264120129 24240874696060768698090097)
              ·
                refine ⟨18180656022045576523567573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24240874696060768698090097 18180656022045576523567573)
                ·
                  refine ⟨426109125516693199771115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18180656022045576523567573 426109125516693199771115)
                  ·
                    rfl

theorem cell23_7468601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_7468601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468601 prefixEnd_7468601 := by exact prefixLift 7468601
  have htrace : WordTrace (prefixWord ++ tailWord_7468601) baseStart_7468601 baseEnd_7468601 := by
    simpa [prefixWord, tailWord_7468601, baseEnd_7468601] using wordTrace_append hprefix tailTrace_7468601
  have hstable : (prefixWord ++ tailWord_7468601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468601).length < 2 ^ (prefixWord ++ tailWord_7468601).sum := by decide
  have hdescent : baseEnd_7468601 < baseStart_7468601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468631 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 4, 5]
def baseStart_7468631 : Nat := 118140960795 + 7468631 * 2 ^ 59
def prefixEnd_7468631 : Nat := 4983230072969 + 3 ^ 40 * 7468631 * 2
def baseEnd_7468631 : Nat := 1278332511356624560188299

theorem tailTrace_7468631 : CollatzResearch.WordTrace tailWord_7468631 prefixEnd_7468631 1278332511356624560188299 := by
  unfold tailWord_7468631
  simp only [CollatzResearch.WordTrace]
  refine ⟨272403351405432902468933747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181602234270288601645955831 272403351405432902468933747)
  ·
    refine ⟨408605027108149353703400621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272403351405432902468933747 408605027108149353703400621)
    ·
      refine ⟨153226885165556007638775233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408605027108149353703400621 153226885165556007638775233)
      ·
        refine ⟨114920163874167005729081425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153226885165556007638775233 114920163874167005729081425)
        ·
          refine ⟨86190122905625254296811069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114920163874167005729081425 86190122905625254296811069)
          ·
            refine ⟨32321296089609470361304151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86190122905625254296811069 32321296089609470361304151)
            ·
              refine ⟨48481944134414205541956227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32321296089609470361304151 48481944134414205541956227)
              ·
                refine ⟨72722916201621308312934341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48481944134414205541956227 72722916201621308312934341)
                ·
                  refine ⟨13635546787803995308675189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72722916201621308312934341 13635546787803995308675189)
                  ·
                    refine ⟨1278332511356624560188299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13635546787803995308675189 1278332511356624560188299)
                    ·
                      rfl

theorem cell23_7468631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_7468631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468631 prefixEnd_7468631 := by exact prefixLift 7468631
  have htrace : WordTrace (prefixWord ++ tailWord_7468631) baseStart_7468631 baseEnd_7468631 := by
    simpa [prefixWord, tailWord_7468631, baseEnd_7468631] using wordTrace_append hprefix tailTrace_7468631
  have hstable : (prefixWord ++ tailWord_7468631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468631).length < 2 ^ (prefixWord ++ tailWord_7468631).sum := by decide
  have hdescent : baseEnd_7468631 < baseStart_7468631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468641 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_7468641 : Nat := 118140960795 + 7468641 * 2 ^ 59
def prefixEnd_7468641 : Nat := 4983230072969 + 3 ^ 40 * 7468641 * 2
def baseEnd_7468641 : Nat := 3835002668876418641439851

theorem tailTrace_7468641 : CollatzResearch.WordTrace tailWord_7468641 prefixEnd_7468641 3835002668876418641439851 := by
  unfold tailWord_7468641
  simp only [CollatzResearch.WordTrace]
  refine ⟨272403716135396674176797777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181602477423597782784531851 272403716135396674176797777)
  ·
    refine ⟨204302787101547505632598333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272403716135396674176797777 204302787101547505632598333)
    ·
      refine ⟨76613545163080314612224375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204302787101547505632598333 76613545163080314612224375)
      ·
        refine ⟨114920317744620471918336563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76613545163080314612224375 114920317744620471918336563)
        ·
          refine ⟨172380476616930707877504845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114920317744620471918336563 172380476616930707877504845)
          ·
            refine ⟨64642678731349015454064317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172380476616930707877504845 64642678731349015454064317)
            ·
              refine ⟨24241004524255880795274119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64642678731349015454064317 24241004524255880795274119)
              ·
                refine ⟨36361506786383821192911179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24241004524255880795274119 36361506786383821192911179)
                ·
                  refine ⟨54542260179575731789366769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36361506786383821192911179 54542260179575731789366769)
                  ·
                    refine ⟨40906695134681798842025077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54542260179575731789366769 40906695134681798842025077)
                    ·
                      refine ⟨3835002668876418641439851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40906695134681798842025077 3835002668876418641439851)
                      ·
                        rfl

theorem cell23_7468641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_7468641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468641 prefixEnd_7468641 := by exact prefixLift 7468641
  have htrace : WordTrace (prefixWord ++ tailWord_7468641) baseStart_7468641 baseEnd_7468641 := by
    simpa [prefixWord, tailWord_7468641, baseEnd_7468641] using wordTrace_append hprefix tailTrace_7468641
  have hstable : (prefixWord ++ tailWord_7468641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468641).length < 2 ^ (prefixWord ++ tailWord_7468641).sum := by decide
  have hdescent : baseEnd_7468641 < baseStart_7468641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468668 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_7468668 : Nat := 118140960795 + 7468668 * 2 ^ 59
def prefixEnd_7468668 : Nat := 4983230072969 + 3 ^ 40 * 7468668 * 2
def baseEnd_7468668 : Nat := 3835016532854090035802227

theorem tailTrace_7468668 : CollatzResearch.WordTrace tailWord_7468668 prefixEnd_7468668 3835016532854090035802227 := by
  unfold tailWord_7468668
  simp only [CollatzResearch.WordTrace]
  refine ⟨136202350453149428894015329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181603133937532571858687105 136202350453149428894015329)
  ·
    refine ⟨102151762839862071670511497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136202350453149428894015329 102151762839862071670511497)
    ·
      refine ⟨76613822129896553752883623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102151762839862071670511497 76613822129896553752883623)
      ·
        refine ⟨114920733194844830629325435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76613822129896553752883623 114920733194844830629325435)
        ·
          refine ⟨172381099792267245943988153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114920733194844830629325435 172381099792267245943988153)
          ·
            refine ⟨129285824844200434457991115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172381099792267245943988153 129285824844200434457991115)
            ·
              refine ⟨193928737266300651686986673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129285824844200434457991115 193928737266300651686986673)
              ·
                refine ⟨145446552949725488765240005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193928737266300651686986673 145446552949725488765240005)
                ·
                  refine ⟨27271228678073529143482501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145446552949725488765240005 27271228678073529143482501)
                  ·
                    refine ⟨5113355377138786714402969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27271228678073529143482501 5113355377138786714402969)
                    ·
                      refine ⟨3835016532854090035802227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113355377138786714402969 3835016532854090035802227)
                      ·
                        rfl

theorem cell23_7468668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_7468668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468668 prefixEnd_7468668 := by exact prefixLift 7468668
  have htrace : WordTrace (prefixWord ++ tailWord_7468668) baseStart_7468668 baseEnd_7468668 := by
    simpa [prefixWord, tailWord_7468668, baseEnd_7468668] using wordTrace_append hprefix tailTrace_7468668
  have hstable : (prefixWord ++ tailWord_7468668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468668).length < 2 ^ (prefixWord ++ tailWord_7468668).sum := by decide
  have hdescent : baseEnd_7468668 < baseStart_7468668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468671 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_7468671 : Nat := 118140960795 + 7468671 * 2 ^ 59
def prefixEnd_7468671 : Nat := 4983230072969 + 3 ^ 40 * 7468671 * 2
def baseEnd_7468671 : Nat := 3835018073296053524064713

theorem tailTrace_7468671 : CollatzResearch.WordTrace tailWord_7468671 prefixEnd_7468671 3835018073296053524064713 := by
  unfold tailWord_7468671
  simp only [CollatzResearch.WordTrace]
  refine ⟨272404810325287989300389867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181603206883525326200259911 272404810325287989300389867)
  ·
    refine ⟨408607215487931983950584801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272404810325287989300389867 408607215487931983950584801)
    ·
      refine ⟨306455411615948987962938601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408607215487931983950584801 306455411615948987962938601)
      ·
        refine ⟨229841558711961740972203951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306455411615948987962938601 229841558711961740972203951)
        ·
          refine ⟨344762338067942611458305927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229841558711961740972203951 344762338067942611458305927)
          ·
            refine ⟨517143507101913917187458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344762338067942611458305927 517143507101913917187458891)
            ·
              refine ⟨775715260652870875781188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517143507101913917187458891 775715260652870875781188337)
              ·
                refine ⟨581786445489653156835891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775715260652870875781188337 581786445489653156835891253)
                ·
                  refine ⟨54542479264654983453364805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581786445489653156835891253 54542479264654983453364805)
                  ·
                    refine ⟨10226714862122809397505901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54542479264654983453364805 10226714862122809397505901)
                    ·
                      refine ⟨3835018073296053524064713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226714862122809397505901 3835018073296053524064713)
                      ·
                        rfl

theorem cell23_7468671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_7468671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468671 prefixEnd_7468671 := by exact prefixLift 7468671
  have htrace : WordTrace (prefixWord ++ tailWord_7468671) baseStart_7468671 baseEnd_7468671 := by
    simpa [prefixWord, tailWord_7468671, baseEnd_7468671] using wordTrace_append hprefix tailTrace_7468671
  have hstable : (prefixWord ++ tailWord_7468671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468671).length < 2 ^ (prefixWord ++ tailWord_7468671).sum := by decide
  have hdescent : baseEnd_7468671 < baseStart_7468671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468702 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7468702 : Nat := 118140960795 + 7468702 * 2 ^ 59
def prefixEnd_7468702 : Nat := 4983230072969 + 3 ^ 40 * 7468702 * 2
def baseEnd_7468702 : Nat := 3835033991196342902777071

theorem tailTrace_7468702 : CollatzResearch.WordTrace tailWord_7468702 prefixEnd_7468702 3835033991196342902777071 := by
  unfold tailWord_7468702
  simp only [CollatzResearch.WordTrace]
  refine ⟨34050742623521960199346045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181603960658783787729845573 34050742623521960199346045)
  ·
    refine ⟨12769028483820735074754767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34050742623521960199346045 12769028483820735074754767)
    ·
      refine ⟨19153542725731102612132151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769028483820735074754767 19153542725731102612132151)
      ·
        refine ⟨28730314088596653918198227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153542725731102612132151 28730314088596653918198227)
        ·
          refine ⟨43095471132894980877297341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28730314088596653918198227 43095471132894980877297341)
          ·
            refine ⟨16160801674835617828986503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43095471132894980877297341 16160801674835617828986503)
            ·
              refine ⟨24241202512253426743479755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16160801674835617828986503 24241202512253426743479755)
              ·
                refine ⟨36361803768380140115219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24241202512253426743479755 36361803768380140115219633)
                ·
                  refine ⟨27271352826285105086414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36361803768380140115219633 27271352826285105086414725)
                  ·
                    refine ⟨5113378654928457203702761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27271352826285105086414725 5113378654928457203702761)
                    ·
                      refine ⟨3835033991196342902777071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113378654928457203702761 3835033991196342902777071)
                      ·
                        rfl

theorem cell23_7468702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7468702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468702 prefixEnd_7468702 := by exact prefixLift 7468702
  have htrace : WordTrace (prefixWord ++ tailWord_7468702) baseStart_7468702 baseEnd_7468702 := by
    simpa [prefixWord, tailWord_7468702, baseEnd_7468702] using wordTrace_append hprefix tailTrace_7468702
  have hstable : (prefixWord ++ tailWord_7468702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468702).length < 2 ^ (prefixWord ++ tailWord_7468702).sum := by decide
  have hdescent : baseEnd_7468702 < baseStart_7468702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468708 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 6]
def baseStart_7468708 : Nat := 118140960795 + 7468708 * 2 ^ 59
def prefixEnd_7468708 : Nat := 4983230072969 + 3 ^ 40 * 7468708 * 2
def baseEnd_7468708 : Nat := 426115230231141097700227

theorem tailTrace_7468708 : CollatzResearch.WordTrace tailWord_7468708 prefixEnd_7468708 426115230231141097700227 := by
  unfold tailWord_7468708
  simp only [CollatzResearch.WordTrace]
  refine ⟨136203079913076972309743389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181604106550769296412991185 136203079913076972309743389)
  ·
    refine ⟨51076154967403864616153771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136203079913076972309743389 51076154967403864616153771)
    ·
      refine ⟨76614232451105796924230657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51076154967403864616153771 76614232451105796924230657)
      ·
        refine ⟨57460674338329347693172993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76614232451105796924230657 57460674338329347693172993)
        ·
          refine ⟨43095505753747010769879745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57460674338329347693172993 43095505753747010769879745)
          ·
            refine ⟨32321629315310258077409809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43095505753747010769879745 32321629315310258077409809)
            ·
              refine ⟨24241221986482693558057357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32321629315310258077409809 24241221986482693558057357)
              ·
                refine ⟨9090458244931010084271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24241221986482693558057357 9090458244931010084271509)
                ·
                  refine ⟨426115230231141097700227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9090458244931010084271509 426115230231141097700227)
                  ·
                    rfl

theorem cell23_7468708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_7468708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468708 prefixEnd_7468708 := by exact prefixLift 7468708
  have htrace : WordTrace (prefixWord ++ tailWord_7468708) baseStart_7468708 baseEnd_7468708 := by
    simpa [prefixWord, tailWord_7468708, baseEnd_7468708] using wordTrace_append hprefix tailTrace_7468708
  have hstable : (prefixWord ++ tailWord_7468708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468708).length < 2 ^ (prefixWord ++ tailWord_7468708).sum := by decide
  have hdescent : baseEnd_7468708 < baseStart_7468708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468742 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_7468742 : Nat := 118140960795 + 7468742 * 2 ^ 59
def prefixEnd_7468742 : Nat := 4983230072969 + 3 ^ 40 * 7468742 * 2
def baseEnd_7468742 : Nat := 426117170046946971808543

theorem tailTrace_7468742 : CollatzResearch.WordTrace tailWord_7468742 prefixEnd_7468742 426117170046946971808543 := by
  unfold tailWord_7468742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512731247125961513319515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181604933272020512284149653 8512731247125961513319515)
  ·
    refine ⟨12769096870688942269979273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8512731247125961513319515 12769096870688942269979273)
    ·
      refine ⟨9576822653016706702484455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12769096870688942269979273 9576822653016706702484455)
      ·
        refine ⟨14365233979525060053726683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9576822653016706702484455 14365233979525060053726683)
        ·
          refine ⟨21547850969287590080590025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14365233979525060053726683 21547850969287590080590025)
          ·
            refine ⟨16160888226965692560442519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21547850969287590080590025 16160888226965692560442519)
            ·
              refine ⟨24241332340448538840663779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16160888226965692560442519 24241332340448538840663779)
              ·
                refine ⟨36361998510672808260995669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24241332340448538840663779 36361998510672808260995669)
                ·
                  refine ⟨426117170046946971808543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36361998510672808260995669 426117170046946971808543)
                  ·
                    rfl

theorem cell23_7468742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_7468742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468742 prefixEnd_7468742 := by exact prefixLift 7468742
  have htrace : WordTrace (prefixWord ++ tailWord_7468742) baseStart_7468742 baseEnd_7468742 := by
    simpa [prefixWord, tailWord_7468742, baseEnd_7468742] using wordTrace_append hprefix tailTrace_7468742
  have hstable : (prefixWord ++ tailWord_7468742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468742).length < 2 ^ (prefixWord ++ tailWord_7468742).sum := by decide
  have hdescent : baseEnd_7468742 < baseStart_7468742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468751 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 6]
def baseStart_7468751 : Nat := 118140960795 + 7468751 * 2 ^ 59
def prefixEnd_7468751 : Nat := 4983230072969 + 3 ^ 40 * 7468751 * 2
def baseEnd_7468751 : Nat := 1278353050582804403688115

theorem tailTrace_7468751 : CollatzResearch.WordTrace tailWord_7468751 prefixEnd_7468751 1278353050582804403688115 := by
  unfold tailWord_7468751
  simp only [CollatzResearch.WordTrace]
  refine ⟨272407728164998162963302107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181605152109998775308868071 272407728164998162963302107)
  ·
    refine ⟨408611592247497244444953161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272407728164998162963302107 408611592247497244444953161)
    ·
      refine ⟨306458694185622933333714871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408611592247497244444953161 306458694185622933333714871)
      ·
        refine ⟨459688041278434400000572307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306458694185622933333714871 459688041278434400000572307)
        ·
          refine ⟨689532061917651600000858461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459688041278434400000572307 689532061917651600000858461)
          ·
            refine ⟨258574523219119350000321923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689532061917651600000858461 258574523219119350000321923)
            ·
              refine ⟨387861784828679025000482885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258574523219119350000321923 387861784828679025000482885)
              ·
                refine ⟨72724084655377317187590541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387861784828679025000482885 72724084655377317187590541)
                ·
                  refine ⟨27271531745766493945346453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72724084655377317187590541 27271531745766493945346453)
                  ·
                    refine ⟨1278353050582804403688115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27271531745766493945346453 1278353050582804403688115)
                    ·
                      rfl

theorem cell23_7468751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_7468751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468751 prefixEnd_7468751 := by exact prefixLift 7468751
  have htrace : WordTrace (prefixWord ++ tailWord_7468751) baseStart_7468751 baseEnd_7468751 := by
    simpa [prefixWord, tailWord_7468751, baseEnd_7468751] using wordTrace_append hprefix tailTrace_7468751
  have hstable : (prefixWord ++ tailWord_7468751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468751).length < 2 ^ (prefixWord ++ tailWord_7468751).sum := by decide
  have hdescent : baseEnd_7468751 < baseStart_7468751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468768 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_7468768 : Nat := 118140960795 + 7468768 * 2 ^ 59
def prefixEnd_7468768 : Nat := 4983230072969 + 3 ^ 40 * 7468768 * 2
def baseEnd_7468768 : Nat := 1278355960306513214850589

theorem tailTrace_7468768 : CollatzResearch.WordTrace tailWord_7468768 prefixEnd_7468768 1278355960306513214850589 := by
  unfold tailWord_7468768
  simp only [CollatzResearch.WordTrace]
  refine ⟨136204174102968287433335479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181605565470624383244447305 136204174102968287433335479)
  ·
    refine ⟨204306261154452431150003219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136204174102968287433335479 204306261154452431150003219)
    ·
      refine ⟨306459391731678646725004829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204306261154452431150003219 306459391731678646725004829)
      ·
        refine ⟨114922271899379492521876811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306459391731678646725004829 114922271899379492521876811)
        ·
          refine ⟨172383407849069238782815217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114922271899379492521876811 172383407849069238782815217)
          ·
            refine ⟨129287555886801929087111413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172383407849069238782815217 129287555886801929087111413)
            ·
              refine ⟨12120708364387680851916695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129287555886801929087111413 12120708364387680851916695)
              ·
                refine ⟨18181062546581521277875043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12120708364387680851916695 18181062546581521277875043)
                ·
                  refine ⟨27271593819872281916812565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18181062546581521277875043 27271593819872281916812565)
                  ·
                    refine ⟨1278355960306513214850589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27271593819872281916812565 1278355960306513214850589)
                    ·
                      rfl

theorem cell23_7468768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_7468768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468768 prefixEnd_7468768 := by exact prefixLift 7468768
  have htrace : WordTrace (prefixWord ++ tailWord_7468768) baseStart_7468768 baseEnd_7468768 := by
    simpa [prefixWord, tailWord_7468768, baseEnd_7468768] using wordTrace_append hprefix tailTrace_7468768
  have hstable : (prefixWord ++ tailWord_7468768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468768).length < 2 ^ (prefixWord ++ tailWord_7468768).sum := by decide
  have hdescent : baseEnd_7468768 < baseStart_7468768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468802 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7468802 : Nat := 118140960795 + 7468802 * 2 ^ 59
def prefixEnd_7468802 : Nat := 4983230072969 + 3 ^ 40 * 7468802 * 2
def baseEnd_7468802 : Nat := 1278361779753930837175537

theorem tailTrace_7468802 : CollatzResearch.WordTrace tailWord_7468802 prefixEnd_7468802 1278361779753930837175537 := by
  unfold tailWord_7468802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68102397071953349668352165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181606392191875599115605773 68102397071953349668352165)
  ·
    refine ⟨12769199450991253062816031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68102397071953349668352165 12769199450991253062816031)
    ·
      refine ⟨19153799176486879594224047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769199450991253062816031 19153799176486879594224047)
      ·
        refine ⟨28730698764730319391336071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19153799176486879594224047 28730698764730319391336071)
        ·
          refine ⟨43096048147095479087004107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28730698764730319391336071 43096048147095479087004107)
          ·
            refine ⟨64644072220643218630506161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43096048147095479087004107 64644072220643218630506161)
            ·
              refine ⟨48483054165482413972879621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64644072220643218630506161 48483054165482413972879621)
              ·
                refine ⟨9090572656027952619914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48483054165482413972879621 9090572656027952619914929)
                ·
                  refine ⟨6817929492020964464936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090572656027952619914929 6817929492020964464936197)
                  ·
                    refine ⟨1278361779753930837175537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6817929492020964464936197 1278361779753930837175537)
                    ·
                      rfl

theorem cell23_7468802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7468802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468802 prefixEnd_7468802 := by exact prefixLift 7468802
  have htrace : WordTrace (prefixWord ++ tailWord_7468802) baseStart_7468802 baseEnd_7468802 := by
    simpa [prefixWord, tailWord_7468802, baseEnd_7468802] using wordTrace_append hprefix tailTrace_7468802
  have hstable : (prefixWord ++ tailWord_7468802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468802).length < 2 ^ (prefixWord ++ tailWord_7468802).sum := by decide
  have hdescent : baseEnd_7468802 < baseStart_7468802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468846 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7468846 : Nat := 118140960795 + 7468846 * 2 ^ 59
def prefixEnd_7468846 : Nat := 4983230072969 + 3 ^ 40 * 7468846 * 2
def baseEnd_7468846 : Nat := 3835107932410590339376409

theorem tailTrace_7468846 : CollatzResearch.WordTrace tailWord_7468846 prefixEnd_7468846 3835107932410590339376409 := by
  unfold tailWord_7468846
  simp only [CollatzResearch.WordTrace]
  refine ⟨34051399137456749273501299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181607462066435996125340261 34051399137456749273501299)
  ·
    refine ⟨51077098706185123910251949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34051399137456749273501299 51077098706185123910251949)
    ·
      refine ⟨19153912014819421466344481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51077098706185123910251949 19153912014819421466344481)
      ·
        refine ⟨14365434011114566099758361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19153912014819421466344481 14365434011114566099758361)
        ·
          refine ⟨10774075508335924574818771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14365434011114566099758361 10774075508335924574818771)
          ·
            refine ⟨16161113262503886862228157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774075508335924574818771 16161113262503886862228157)
            ·
              refine ⟨6060417473438957573335559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16161113262503886862228157 6060417473438957573335559)
              ·
                refine ⟨9090626210158436360003339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060417473438957573335559 9090626210158436360003339)
                ·
                  refine ⟨13635939315237654540005009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9090626210158436360003339 13635939315237654540005009)
                  ·
                    refine ⟨10226954486428240905003757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13635939315237654540005009 10226954486428240905003757)
                    ·
                      refine ⟨3835107932410590339376409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10226954486428240905003757 3835107932410590339376409)
                      ·
                        rfl

theorem cell23_7468846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7468846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468846 prefixEnd_7468846 := by exact prefixLift 7468846
  have htrace : WordTrace (prefixWord ++ tailWord_7468846) baseStart_7468846 baseEnd_7468846 := by
    simpa [prefixWord, tailWord_7468846, baseEnd_7468846] using wordTrace_append hprefix tailTrace_7468846
  have hstable : (prefixWord ++ tailWord_7468846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468846).length < 2 ^ (prefixWord ++ tailWord_7468846).sum := by decide
  have hdescent : baseEnd_7468846 < baseStart_7468846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468882 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_7468882 : Nat := 118140960795 + 7468882 * 2 ^ 59
def prefixEnd_7468882 : Nat := 4983230072969 + 3 ^ 40 * 7468882 * 2
def baseEnd_7468882 : Nat := 3835126417714152198526243

theorem tailTrace_7468882 : CollatzResearch.WordTrace tailWord_7468882 prefixEnd_7468882 3835126417714152198526243 := by
  unfold tailWord_7468882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68103126531880893084080225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181608337418349048224213933 68103126531880893084080225)
  ·
    refine ⟨51077344898910669813060169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68103126531880893084080225 51077344898910669813060169)
    ·
      refine ⟨38308008674183002359795127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51077344898910669813060169 38308008674183002359795127)
      ·
        refine ⟨57462013011274503539692691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38308008674183002359795127 57462013011274503539692691)
        ·
          refine ⟨86193019516911755309539037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57462013011274503539692691 86193019516911755309539037)
          ·
            refine ⟨32322382318841908241077139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86193019516911755309539037 32322382318841908241077139)
            ·
              refine ⟨48483573478262862361615709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32322382318841908241077139 48483573478262862361615709)
              ·
                refine ⟨18181340054348573385605891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48483573478262862361615709 18181340054348573385605891)
                ·
                  refine ⟨27272010081522860078408837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18181340054348573385605891 27272010081522860078408837)
                  ·
                    refine ⟨5113501890285536264701657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27272010081522860078408837 5113501890285536264701657)
                    ·
                      refine ⟨3835126417714152198526243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113501890285536264701657 3835126417714152198526243)
                      ·
                        rfl

theorem cell23_7468882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_7468882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468882 prefixEnd_7468882 := by exact prefixLift 7468882
  have htrace : WordTrace (prefixWord ++ tailWord_7468882) baseStart_7468882 baseEnd_7468882 := by
    simpa [prefixWord, tailWord_7468882, baseEnd_7468882] using wordTrace_append hprefix tailTrace_7468882
  have hstable : (prefixWord ++ tailWord_7468882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468882).length < 2 ^ (prefixWord ++ tailWord_7468882).sum := by decide
  have hdescent : baseEnd_7468882 < baseStart_7468882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468928 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_7468928 : Nat := 118140960795 + 7468928 * 2 ^ 59
def prefixEnd_7468928 : Nat := 4983230072969 + 3 ^ 40 * 7468928 * 2
def baseEnd_7468928 : Nat := 3835150037824259018551031

theorem tailTrace_7468928 : CollatzResearch.WordTrace tailWord_7468928 prefixEnd_7468928 3835150037824259018551031 := by
  unfold tailWord_7468928
  simp only [CollatzResearch.WordTrace]
  refine ⟨136207091942678461096247719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181609455923571281461663625 136207091942678461096247719)
  ·
    refine ⟨204310637914017691644371579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136207091942678461096247719 204310637914017691644371579)
    ·
      refine ⟨306465956871026537466557369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204310637914017691644371579 306465956871026537466557369)
      ·
        refine ⟨229849467653269903099918027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306465956871026537466557369 229849467653269903099918027)
        ·
          refine ⟨344774201479904854649877041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229849467653269903099918027 344774201479904854649877041)
          ·
            refine ⟨258580651109928640987407781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344774201479904854649877041 258580651109928640987407781)
            ·
              refine ⟨48483872083111620185138959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258580651109928640987407781 48483872083111620185138959)
              ·
                refine ⟨72725808124667430277708439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48483872083111620185138959 72725808124667430277708439)
                ·
                  refine ⟨109088712187001145416562659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72725808124667430277708439 109088712187001145416562659)
                  ·
                    refine ⟨163633068280501718124843989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109088712187001145416562659 163633068280501718124843989)
                    ·
                      refine ⟨3835150037824259018551031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163633068280501718124843989 3835150037824259018551031)
                      ·
                        rfl

theorem cell23_7468928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_7468928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468928 prefixEnd_7468928 := by exact prefixLift 7468928
  have htrace : WordTrace (prefixWord ++ tailWord_7468928) baseStart_7468928 baseEnd_7468928 := by
    simpa [prefixWord, tailWord_7468928, baseEnd_7468928] using wordTrace_append hprefix tailTrace_7468928
  have hstable : (prefixWord ++ tailWord_7468928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468928).length < 2 ^ (prefixWord ++ tailWord_7468928).sum := by decide
  have hdescent : baseEnd_7468928 < baseStart_7468928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7468965 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_7468965 : Nat := 118140960795 + 7468965 * 2 ^ 59
def prefixEnd_7468965 : Nat := 4983230072969 + 3 ^ 40 * 7468965 * 2
def baseEnd_7468965 : Nat := 1278389678869491791262787

theorem tailTrace_7468965 : CollatzResearch.WordTrace tailWord_7468965 prefixEnd_7468965 1278389678869491791262787 := by
  unfold tailWord_7468965
  simp only [CollatzResearch.WordTrace]
  refine ⟨272415533386222877511592349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181610355590815251674394899 272415533386222877511592349)
  ·
    refine ⟨102155825019833579066847131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 272415533386222877511592349 102155825019833579066847131)
    ·
      refine ⟨153233737529750368600270697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102155825019833579066847131 153233737529750368600270697)
      ·
        refine ⟨114925303147312776450203023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153233737529750368600270697 114925303147312776450203023)
        ·
          refine ⟨172387954720969164675304535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114925303147312776450203023 172387954720969164675304535)
          ·
            refine ⟨258581932081453747012956803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172387954720969164675304535 258581932081453747012956803)
            ·
              refine ⟨387872898122180620519435205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258581932081453747012956803 387872898122180620519435205)
              ·
                refine ⟨72726168397908866347394101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 387872898122180620519435205 72726168397908866347394101)
                ·
                  refine ⟨6818078287303956220068197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72726168397908866347394101 6818078287303956220068197)
                  ·
                    refine ⟨1278389678869491791262787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818078287303956220068197 1278389678869491791262787)
                    ·
                      rfl

theorem cell23_7468965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_7468965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7468965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7468965 prefixEnd_7468965 := by exact prefixLift 7468965
  have htrace : WordTrace (prefixWord ++ tailWord_7468965) baseStart_7468965 baseEnd_7468965 := by
    simpa [prefixWord, tailWord_7468965, baseEnd_7468965] using wordTrace_append hprefix tailTrace_7468965
  have hstable : (prefixWord ++ tailWord_7468965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7468965).length < 2 ^ (prefixWord ++ tailWord_7468965).sum := by decide
  have hdescent : baseEnd_7468965 < baseStart_7468965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7468965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469032 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7469032 : Nat := 118140960795 + 7469032 * 2 ^ 59
def prefixEnd_7469032 : Nat := 4983230072969 + 3 ^ 40 * 7469032 * 2
def baseEnd_7469032 : Nat := 3835203439812326611650553

theorem tailTrace_7469032 : CollatzResearch.WordTrace tailWord_7469032 prefixEnd_7469032 3835203439812326611650553 := by
  unfold tailWord_7469032
  simp only [CollatzResearch.WordTrace]
  refine ⟨136208988538490073977140675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181611984717986765302854233 136208988538490073977140675)
  ·
    refine ⟨204313482807735110965711013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136208988538490073977140675 204313482807735110965711013)
    ·
      refine ⟨38308778026450333306070815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204313482807735110965711013 38308778026450333306070815)
      ·
        refine ⟨57463167039675499959106223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38308778026450333306070815 57463167039675499959106223)
        ·
          refine ⟨86194750559513249938659335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57463167039675499959106223 86194750559513249938659335)
          ·
            refine ⟨129292125839269874907989003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86194750559513249938659335 129292125839269874907989003)
            ·
              refine ⟨193938188758904812361983505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129292125839269874907989003 193938188758904812361983505)
              ·
                refine ⟨145453641569178609271487629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193938188758904812361983505 145453641569178609271487629)
                ·
                  refine ⟨54545115588441978476807861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145453641569178609271487629 54545115588441978476807861)
                  ·
                    refine ⟨5113604586416435482200737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54545115588441978476807861 5113604586416435482200737)
                    ·
                      refine ⟨3835203439812326611650553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113604586416435482200737 3835203439812326611650553)
                      ·
                        rfl

theorem cell23_7469032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7469032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469032 prefixEnd_7469032 := by exact prefixLift 7469032
  have htrace : WordTrace (prefixWord ++ tailWord_7469032) baseStart_7469032 baseEnd_7469032 := by
    simpa [prefixWord, tailWord_7469032, baseEnd_7469032] using wordTrace_append hprefix tailTrace_7469032
  have hstable : (prefixWord ++ tailWord_7469032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469032).length < 2 ^ (prefixWord ++ tailWord_7469032).sum := by decide
  have hdescent : baseEnd_7469032 < baseStart_7469032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469089 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_7469089 : Nat := 118140960795 + 7469089 * 2 ^ 59
def prefixEnd_7469089 : Nat := 4983230072969 + 3 ^ 40 * 7469089 * 2
def baseEnd_7469089 : Nat := 1278410902736544296212597

theorem tailTrace_7469089 : CollatzResearch.WordTrace tailWord_7469089 prefixEnd_7469089 1278410902736544296212597 := by
  unfold tailWord_7469089
  simp only [CollatzResearch.WordTrace]
  refine ⟨272420056037773646689106321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181613370691849097792737547 272420056037773646689106321)
  ·
    refine ⟨204315042028330235016829741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272420056037773646689106321 204315042028330235016829741)
    ·
      refine ⟨76618140760623838131311153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204315042028330235016829741 76618140760623838131311153)
      ·
        refine ⟨57463605570467878598483365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76618140760623838131311153 57463605570467878598483365)
        ·
          refine ⟨10774426044462727237215631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57463605570467878598483365 10774426044462727237215631)
          ·
            refine ⟨16161639066694090855823447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774426044462727237215631 16161639066694090855823447)
            ·
              refine ⟨24242458600041136283735171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16161639066694090855823447 24242458600041136283735171)
              ·
                refine ⟨36363687900061704425602757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24242458600041136283735171 36363687900061704425602757)
                ·
                  refine ⟨6818191481261569579800517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36363687900061704425602757 6818191481261569579800517)
                  ·
                    refine ⟨1278410902736544296212597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818191481261569579800517 1278410902736544296212597)
                    ·
                      rfl

theorem cell23_7469089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_7469089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469089 prefixEnd_7469089 := by exact prefixLift 7469089
  have htrace : WordTrace (prefixWord ++ tailWord_7469089) baseStart_7469089 baseEnd_7469089 := by
    simpa [prefixWord, tailWord_7469089, baseEnd_7469089] using wordTrace_append hprefix tailTrace_7469089
  have hstable : (prefixWord ++ tailWord_7469089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469089).length < 2 ^ (prefixWord ++ tailWord_7469089).sum := by decide
  have hdescent : baseEnd_7469089 < baseStart_7469089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469106 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_7469106 : Nat := 118140960795 + 7469106 * 2 ^ 59
def prefixEnd_7469106 : Nat := 4983230072969 + 3 ^ 40 * 7469106 * 2
def baseEnd_7469106 : Nat := 1278413812460253107375071

theorem tailTrace_7469106 : CollatzResearch.WordTrace tailWord_7469106 prefixEnd_7469106 1278413812460253107375071 := by
  unfold tailWord_7469106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68105169019678014648118793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181613784052474705728316781 68105169019678014648118793)
  ·
    refine ⟨51078876764758510986089095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68105169019678014648118793 51078876764758510986089095)
    ·
      refine ⟨76618315147137766479133643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51078876764758510986089095 76618315147137766479133643)
      ·
        refine ⟨114927472720706649718700465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76618315147137766479133643 114927472720706649718700465)
        ·
          refine ⟨86195604540529987289025349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114927472720706649718700465 86195604540529987289025349)
          ·
            refine ⟨16161675851349372616692253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86195604540529987289025349 16161675851349372616692253)
            ·
              refine ⟨6060628444256014731259595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16161675851349372616692253 6060628444256014731259595)
              ·
                refine ⟨9090942666384022096889393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060628444256014731259595 9090942666384022096889393)
                ·
                  refine ⟨6818206999788016572667045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9090942666384022096889393 6818206999788016572667045)
                  ·
                    refine ⟨1278413812460253107375071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818206999788016572667045 1278413812460253107375071)
                    ·
                      rfl

theorem cell23_7469106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_7469106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469106 prefixEnd_7469106 := by exact prefixLift 7469106
  have htrace : WordTrace (prefixWord ++ tailWord_7469106) baseStart_7469106 baseEnd_7469106 := by
    simpa [prefixWord, tailWord_7469106, baseEnd_7469106] using wordTrace_append hprefix tailTrace_7469106
  have hstable : (prefixWord ++ tailWord_7469106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469106).length < 2 ^ (prefixWord ++ tailWord_7469106).sum := by decide
  have hdescent : baseEnd_7469106 < baseStart_7469106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469169 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_7469169 : Nat := 118140960795 + 7469169 * 2 ^ 59
def prefixEnd_7469169 : Nat := 4983230072969 + 3 ^ 40 * 7469169 * 2
def baseEnd_7469169 : Nat := 3835273786661992575637423

theorem tailTrace_7469169 : CollatzResearch.WordTrace tailWord_7469169 prefixEnd_7469169 3835273786661992575637423 := by
  unfold tailWord_7469169
  simp only [CollatzResearch.WordTrace]
  refine ⟨272422973877483820352018561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181615315918322546901345707 272422973877483820352018561)
  ·
    refine ⟨204317230408112865264013921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272422973877483820352018561 204317230408112865264013921)
    ·
      refine ⟨153237922806084648948010441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204317230408112865264013921 153237922806084648948010441)
      ·
        refine ⟨114928442104563486711007831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153237922806084648948010441 114928442104563486711007831)
        ·
          refine ⟨172392663156845230066511747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114928442104563486711007831 172392663156845230066511747)
          ·
            refine ⟨258588994735267845099767621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172392663156845230066511747 258588994735267845099767621)
            ·
              refine ⟨48485436512862720956206429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258588994735267845099767621 48485436512862720956206429)
              ·
                refine ⟨18182038692323520358577411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48485436512862720956206429 18182038692323520358577411)
                ·
                  refine ⟨27273058038485280537866117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18182038692323520358577411 27273058038485280537866117)
                  ·
                    refine ⟨5113698382215990100849897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27273058038485280537866117 5113698382215990100849897)
                    ·
                      refine ⟨3835273786661992575637423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113698382215990100849897 3835273786661992575637423)
                      ·
                        rfl

theorem cell23_7469169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_7469169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469169 prefixEnd_7469169 := by exact prefixLift 7469169
  have htrace : WordTrace (prefixWord ++ tailWord_7469169) baseStart_7469169 baseEnd_7469169 := by
    simpa [prefixWord, tailWord_7469169, baseEnd_7469169] using wordTrace_append hprefix tailTrace_7469169
  have hstable : (prefixWord ++ tailWord_7469169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469169).length < 2 ^ (prefixWord ++ tailWord_7469169).sum := by decide
  have hdescent : baseEnd_7469169 < baseStart_7469169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469226 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_7469226 : Nat := 118140960795 + 7469226 * 2 ^ 59
def prefixEnd_7469226 : Nat := 4983230072969 + 3 ^ 40 * 7469226 * 2
def baseEnd_7469226 : Nat := 426144783895477650291629

theorem tailTrace_7469226 : CollatzResearch.WordTrace tailWord_7469226 prefixEnd_7469226 426144783895477650291629 := by
  unfold tailWord_7469226
  simp only [CollatzResearch.WordTrace]
  refine ⟨68106263209569329771710883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181616701892184879391229021 68106263209569329771710883)
  ·
    refine ⟨102159394814353994657566325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68106263209569329771710883 102159394814353994657566325)
    ·
      refine ⟨9577443263845686999146843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102159394814353994657566325 9577443263845686999146843)
      ·
        refine ⟨14366164895768530498720265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9577443263845686999146843 14366164895768530498720265)
        ·
          refine ⟨10774623671826397874040199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14366164895768530498720265 10774623671826397874040199)
          ·
            refine ⟨16161935507739596811060299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774623671826397874040199 16161935507739596811060299)
            ·
              refine ⟨24242903261609395216590449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16161935507739596811060299 24242903261609395216590449)
              ·
                refine ⟨18182177446207046412442837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24242903261609395216590449 18182177446207046412442837)
                ·
                  refine ⟨426144783895477650291629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18182177446207046412442837 426144783895477650291629)
                  ·
                    rfl

theorem cell23_7469226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_7469226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469226 prefixEnd_7469226 := by exact prefixLift 7469226
  have htrace : WordTrace (prefixWord ++ tailWord_7469226) baseStart_7469226 baseEnd_7469226 := by
    simpa [prefixWord, tailWord_7469226, baseEnd_7469226] using wordTrace_append hprefix tailTrace_7469226
  have hstable : (prefixWord ++ tailWord_7469226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469226).length < 2 ^ (prefixWord ++ tailWord_7469226).sum := by decide
  have hdescent : baseEnd_7469226 < baseStart_7469226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469239 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 2, 5]
def baseStart_7469239 : Nat := 118140960795 + 7469239 * 2 ^ 59
def prefixEnd_7469239 : Nat := 4983230072969 + 3 ^ 40 * 7469239 * 2
def baseEnd_7469239 : Nat := 1278436576769269100587367

theorem tailTrace_7469239 : CollatzResearch.WordTrace tailWord_7469239 prefixEnd_7469239 1278436576769269100587367 := by
  unfold tailWord_7469239
  simp only [CollatzResearch.WordTrace]
  refine ⟨272425526987230222307066771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181617017991486814871377847 272425526987230222307066771)
  ·
    refine ⟨408638290480845333460600157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272425526987230222307066771 408638290480845333460600157)
    ·
      refine ⟨153239358930317000047725059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408638290480845333460600157 153239358930317000047725059)
      ·
        refine ⟨229859038395475500071587589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153239358930317000047725059 229859038395475500071587589)
        ·
          refine ⟨43098569699151656263422673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229859038395475500071587589 43098569699151656263422673)
          ·
            refine ⟨32323927274363742197567005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43098569699151656263422673 32323927274363742197567005)
            ·
              refine ⟨12121472727886403324087627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32323927274363742197567005 12121472727886403324087627)
              ·
                refine ⟨18182209091829604986131441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12121472727886403324087627 18182209091829604986131441)
                ·
                  refine ⟨13636656818872203739598581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18182209091829604986131441 13636656818872203739598581)
                  ·
                    refine ⟨1278436576769269100587367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13636656818872203739598581 1278436576769269100587367)
                    ·
                      rfl

theorem cell23_7469239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_7469239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469239 prefixEnd_7469239 := by exact prefixLift 7469239
  have htrace : WordTrace (prefixWord ++ tailWord_7469239) baseStart_7469239 baseEnd_7469239 := by
    simpa [prefixWord, tailWord_7469239, baseEnd_7469239] using wordTrace_append hprefix tailTrace_7469239
  have hstable : (prefixWord ++ tailWord_7469239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469239).length < 2 ^ (prefixWord ++ tailWord_7469239).sum := by decide
  have hdescent : baseEnd_7469239 < baseStart_7469239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469259 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 4, 2]
def baseStart_7469259 : Nat := 118140960795 + 7469259 * 2 ^ 59
def prefixEnd_7469259 : Nat := 4983230072969 + 3 ^ 40 * 7469259 * 2
def baseEnd_7469259 : Nat := 3835319999920897223512009

theorem tailTrace_7469259 : CollatzResearch.WordTrace tailWord_7469259 prefixEnd_7469259 3835319999920897223512009 := by
  unfold tailWord_7469259
  simp only [CollatzResearch.WordTrace]
  refine ⟨272426256447157765722794831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181617504298105177148529887 272426256447157765722794831)
  ·
    refine ⟨408639384670736648584192247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272426256447157765722794831 408639384670736648584192247)
    ·
      refine ⟨612959077006104972876288371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408639384670736648584192247 612959077006104972876288371)
      ·
        refine ⟨919438615509157459314432557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612959077006104972876288371 919438615509157459314432557)
        ·
          refine ⟨344789480815934047242912209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 919438615509157459314432557 344789480815934047242912209)
          ·
            refine ⟨258592110611950535432184157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344789480815934047242912209 258592110611950535432184157)
            ·
              refine ⟨96972041479481450787069059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258592110611950535432184157 96972041479481450787069059)
              ·
                refine ⟨145458062219222176180603589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96972041479481450787069059 145458062219222176180603589)
                ·
                  refine ⟨27273386666104158033863173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145458062219222176180603589 27273386666104158033863173)
                  ·
                    refine ⟨5113759999894529631349345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27273386666104158033863173 5113759999894529631349345)
                    ·
                      refine ⟨3835319999920897223512009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113759999894529631349345 3835319999920897223512009)
                      ·
                        rfl

theorem cell23_7469259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4, 2].length) (baseStart_7469259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469259 prefixEnd_7469259 := by exact prefixLift 7469259
  have htrace : WordTrace (prefixWord ++ tailWord_7469259) baseStart_7469259 baseEnd_7469259 := by
    simpa [prefixWord, tailWord_7469259, baseEnd_7469259] using wordTrace_append hprefix tailTrace_7469259
  have hstable : (prefixWord ++ tailWord_7469259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469259).length < 2 ^ (prefixWord ++ tailWord_7469259).sum := by decide
  have hdescent : baseEnd_7469259 < baseStart_7469259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469320 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 1, 4]
def baseStart_7469320 : Nat := 118140960795 + 7469320 * 2 ^ 59
def prefixEnd_7469320 : Nat := 4983230072969 + 3 ^ 40 * 7469320 * 2
def baseEnd_7469320 : Nat := 1278450440746940494949743

theorem tailTrace_7469320 : CollatzResearch.WordTrace tailWord_7469320 prefixEnd_7469320 1278450440746940494949743 := by
  unfold tailWord_7469320
  simp only [CollatzResearch.WordTrace]
  refine ⟨136214240649968386570382707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181618987533291182093843609 136214240649968386570382707)
  ·
    refine ⟨204321360974952579855574061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136214240649968386570382707 204321360974952579855574061)
    ·
      refine ⟨76620510365607217445840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204321360974952579855574061 76620510365607217445840273)
      ·
        refine ⟨57465382774205413084380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76620510365607217445840273 57465382774205413084380205)
        ·
          refine ⟨21549518540327029906642577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57465382774205413084380205 21549518540327029906642577)
          ·
            refine ⟨16162138905245272429981933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21549518540327029906642577 16162138905245272429981933)
            ·
              refine ⟨6060802089466977161243225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16162138905245272429981933 6060802089466977161243225)
              ·
                refine ⟨4545601567100232870932419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060802089466977161243225 4545601567100232870932419)
                ·
                  refine ⟨6818402350650349306398629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545601567100232870932419 6818402350650349306398629)
                  ·
                    refine ⟨1278450440746940494949743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818402350650349306398629 1278450440746940494949743)
                    ·
                      rfl

theorem cell23_7469320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_7469320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469320 prefixEnd_7469320 := by exact prefixLift 7469320
  have htrace : WordTrace (prefixWord ++ tailWord_7469320) baseStart_7469320 baseEnd_7469320 := by
    simpa [prefixWord, tailWord_7469320, baseEnd_7469320] using wordTrace_append hprefix tailTrace_7469320
  have hstable : (prefixWord ++ tailWord_7469320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469320).length < 2 ^ (prefixWord ++ tailWord_7469320).sum := by decide
  have hdescent : baseEnd_7469320 < baseStart_7469320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469336 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7469336 : Nat := 118140960795 + 7469336 * 2 ^ 59
def prefixEnd_7469336 : Nat := 4983230072969 + 3 ^ 40 * 7469336 * 2
def baseEnd_7469336 : Nat := 3835359537931293422249155

theorem tailTrace_7469336 : CollatzResearch.WordTrace tailWord_7469336 prefixEnd_7469336 3835359537931293422249155 := by
  unfold tailWord_7469336
  simp only [CollatzResearch.WordTrace]
  refine ⟨136214532433939403936673931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181619376578585871915565241 136214532433939403936673931)
  ·
    refine ⟨204321798650909105905010897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136214532433939403936673931 204321798650909105905010897)
    ·
      refine ⟨153241348988181829428758173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204321798650909105905010897 153241348988181829428758173)
      ·
        refine ⟨57465505870568186035784315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153241348988181829428758173 57465505870568186035784315)
        ·
          refine ⟨86198258805852279053676473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57465505870568186035784315 86198258805852279053676473)
          ·
            refine ⟨64648694104389209290257355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86198258805852279053676473 64648694104389209290257355)
            ·
              refine ⟨96973041156583813935386033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64648694104389209290257355 96973041156583813935386033)
              ·
                refine ⟨72729780867437860451539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96973041156583813935386033 72729780867437860451539525)
                ·
                  refine ⟨13636833912644598834663661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72729780867437860451539525 13636833912644598834663661)
                  ·
                    refine ⟨5113812717241724562998873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13636833912644598834663661 5113812717241724562998873)
                    ·
                      refine ⟨3835359537931293422249155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113812717241724562998873 3835359537931293422249155)
                      ·
                        rfl

theorem cell23_7469336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7469336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469336 prefixEnd_7469336 := by exact prefixLift 7469336
  have htrace : WordTrace (prefixWord ++ tailWord_7469336) baseStart_7469336 baseEnd_7469336 := by
    simpa [prefixWord, tailWord_7469336, baseEnd_7469336] using wordTrace_append hprefix tailTrace_7469336
  have hstable : (prefixWord ++ tailWord_7469336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469336).length < 2 ^ (prefixWord ++ tailWord_7469336).sum := by decide
  have hdescent : baseEnd_7469336 < baseStart_7469336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469346 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7469346 : Nat := 118140960795 + 7469346 * 2 ^ 59
def prefixEnd_7469346 : Nat := 4983230072969 + 3 ^ 40 * 7469346 * 2
def baseEnd_7469346 : Nat := 1278454890912612794374703

theorem tailTrace_7469346 : CollatzResearch.WordTrace tailWord_7469346 prefixEnd_7469346 1278454890912612794374703 := by
  unfold tailWord_7469346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68107357399460644895302973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181619619731895053054141261 68107357399460644895302973)
  ·
    refine ⟨25540259024797741835738615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68107357399460644895302973 25540259024797741835738615)
    ·
      refine ⟨38310388537196612753607923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25540259024797741835738615 38310388537196612753607923)
      ·
        refine ⟨57465582805794919130411885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38310388537196612753607923 57465582805794919130411885)
        ·
          refine ⟨21549593552173094673904457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57465582805794919130411885 21549593552173094673904457)
          ·
            refine ⟨16162195164129821005428343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21549593552173094673904457 16162195164129821005428343)
            ·
              refine ⟨24243292746194731508142515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162195164129821005428343 24243292746194731508142515)
              ·
                refine ⟨36364939119292097262213773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24243292746194731508142515 36364939119292097262213773)
                ·
                  refine ⟨13636852169734536473330165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36364939119292097262213773 13636852169734536473330165)
                  ·
                    refine ⟨1278454890912612794374703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13636852169734536473330165 1278454890912612794374703)
                    ·
                      rfl

theorem cell23_7469346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7469346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469346 prefixEnd_7469346 := by exact prefixLift 7469346
  have htrace : WordTrace (prefixWord ++ tailWord_7469346) baseStart_7469346 baseEnd_7469346 := by
    simpa [prefixWord, tailWord_7469346, baseEnd_7469346] using wordTrace_append hprefix tailTrace_7469346
  have hstable : (prefixWord ++ tailWord_7469346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469346).length < 2 ^ (prefixWord ++ tailWord_7469346).sum := by decide
  have hdescent : baseEnd_7469346 < baseStart_7469346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469359 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 6, 4]
def baseStart_7469359 : Nat := 118140960795 + 7469359 * 2 ^ 59
def prefixEnd_7469359 : Nat := 4983230072969 + 3 ^ 40 * 7469359 * 2
def baseEnd_7469359 : Nat := 1278457115995448944087183

theorem tailTrace_7469359 : CollatzResearch.WordTrace tailWord_7469359 prefixEnd_7469359 1278457115995448944087183 := by
  unfold tailWord_7469359
  simp only [CollatzResearch.WordTrace]
  refine ⟨272429903746795482801435131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181619935831196988534290087 272429903746795482801435131)
  ·
    refine ⟨408644855620193224202152697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272429903746795482801435131 408644855620193224202152697)
    ·
      refine ⟨306483641715144918151614523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408644855620193224202152697 306483641715144918151614523)
      ·
        refine ⟨459725462572717377227421785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306483641715144918151614523 459725462572717377227421785)
        ·
          refine ⟨344794096929538032920566339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459725462572717377227421785 344794096929538032920566339)
          ·
            refine ⟨517191145394307049380849509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344794096929538032920566339 517191145394307049380849509)
            ·
              refine ⟨96973339761432571758909283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517191145394307049380849509 96973339761432571758909283)
              ·
                refine ⟨145460009642148857638363925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96973339761432571758909283 145460009642148857638363925)
                ·
                  refine ⟨6818437951975727701798309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145460009642148857638363925 6818437951975727701798309)
                  ·
                    refine ⟨1278457115995448944087183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6818437951975727701798309 1278457115995448944087183)
                    ·
                      rfl

theorem cell23_7469359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_7469359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469359 prefixEnd_7469359 := by exact prefixLift 7469359
  have htrace : WordTrace (prefixWord ++ tailWord_7469359) baseStart_7469359 baseEnd_7469359 := by
    simpa [prefixWord, tailWord_7469359, baseEnd_7469359] using wordTrace_append hprefix tailTrace_7469359
  have hstable : (prefixWord ++ tailWord_7469359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469359).length < 2 ^ (prefixWord ++ tailWord_7469359).sum := by decide
  have hdescent : baseEnd_7469359 < baseStart_7469359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469377 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7469377 : Nat := 118140960795 + 7469377 * 2 ^ 59
def prefixEnd_7469377 : Nat := 4983230072969 + 3 ^ 40 * 7469377 * 2
def baseEnd_7469377 : Nat := 3835380590638127761836467

theorem tailTrace_7469377 : CollatzResearch.WordTrace tailWord_7469377 prefixEnd_7469377 3835380590638127761836467 := by
  unfold tailWord_7469377
  simp only [CollatzResearch.WordTrace]
  refine ⟨272430560260730271875590385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181620373507153514583726923 272430560260730271875590385)
  ·
    refine ⟨204322920195547703906692789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272430560260730271875590385 204322920195547703906692789)
    ·
      refine ⟨19155273768332597241252449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204322920195547703906692789 19155273768332597241252449)
      ·
        refine ⟨14366455326249447930939337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19155273768332597241252449 14366455326249447930939337)
        ·
          refine ⟨10774841494687085948204503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14366455326249447930939337 10774841494687085948204503)
          ·
            refine ⟨16162262242030628922306755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10774841494687085948204503 16162262242030628922306755)
            ·
              refine ⟨24243393363045943383460133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16162262242030628922306755 24243393363045943383460133)
              ·
                refine ⟨4545636255571114384398775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24243393363045943383460133 4545636255571114384398775)
                ·
                  refine ⟨6818454383356671576598163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4545636255571114384398775 6818454383356671576598163)
                  ·
                    refine ⟨10227681575035007364897245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6818454383356671576598163 10227681575035007364897245)
                    ·
                      refine ⟨3835380590638127761836467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10227681575035007364897245 3835380590638127761836467)
                      ·
                        rfl

theorem cell23_7469377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7469377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469377 prefixEnd_7469377 := by exact prefixLift 7469377
  have htrace : WordTrace (prefixWord ++ tailWord_7469377) baseStart_7469377 baseEnd_7469377 := by
    simpa [prefixWord, tailWord_7469377, baseEnd_7469377] using wordTrace_append hprefix tailTrace_7469377
  have hstable : (prefixWord ++ tailWord_7469377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469377).length < 2 ^ (prefixWord ++ tailWord_7469377).sum := by decide
  have hdescent : baseEnd_7469377 < baseStart_7469377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469383 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_7469383 : Nat := 118140960795 + 7469383 * 2 ^ 59
def prefixEnd_7469383 : Nat := 4983230072969 + 3 ^ 40 * 7469383 * 2
def baseEnd_7469383 : Nat := 3835383671522054738361439

theorem tailTrace_7469383 : CollatzResearch.WordTrace tailWord_7469383 prefixEnd_7469383 3835383671522054738361439 := by
  unfold tailWord_7469383
  simp only [CollatzResearch.WordTrace]
  refine ⟨272430779098708534900308803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181620519399139023266872535 272430779098708534900308803)
  ·
    refine ⟨408646168648062802350463205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272430779098708534900308803 408646168648062802350463205)
    ·
      refine ⟨76621156621511775440711851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408646168648062802350463205 76621156621511775440711851)
      ·
        refine ⟨114931734932267663161067777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76621156621511775440711851 114931734932267663161067777)
        ·
          refine ⟨86198801199200747370800833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114931734932267663161067777 86198801199200747370800833)
          ·
            refine ⟨64649100899400560528100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86198801199200747370800833 64649100899400560528100625)
            ·
              refine ⟨48486825674550420396075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64649100899400560528100625 48486825674550420396075469)
              ·
                refine ⟨18182559627956407648528301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48486825674550420396075469 18182559627956407648528301)
                ·
                  refine ⟨6818459860483652868198113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18182559627956407648528301 6818459860483652868198113)
                  ·
                    refine ⟨5113844895362739651148585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6818459860483652868198113 5113844895362739651148585)
                    ·
                      refine ⟨3835383671522054738361439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113844895362739651148585 3835383671522054738361439)
                      ·
                        rfl

theorem cell23_7469383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_7469383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469383 prefixEnd_7469383 := by exact prefixLift 7469383
  have htrace : WordTrace (prefixWord ++ tailWord_7469383) baseStart_7469383 baseEnd_7469383 := by
    simpa [prefixWord, tailWord_7469383, baseEnd_7469383] using wordTrace_append hprefix tailTrace_7469383
  have hstable : (prefixWord ++ tailWord_7469383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469383).length < 2 ^ (prefixWord ++ tailWord_7469383).sum := by decide
  have hdescent : baseEnd_7469383 < baseStart_7469383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469396 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_7469396 : Nat := 118140960795 + 7469396 * 2 ^ 59
def prefixEnd_7469396 : Nat := 4983230072969 + 3 ^ 40 * 7469396 * 2
def baseEnd_7469396 : Nat := 3835390346770563187498879

theorem tailTrace_7469396 : CollatzResearch.WordTrace tailWord_7469396 prefixEnd_7469396 3835390346770563187498879 := by
  unfold tailWord_7469396
  simp only [CollatzResearch.WordTrace]
  refine ⟨136215626623830719060266021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181620835498440958747021361 136215626623830719060266021)
  ·
    refine ⟨25540429991968259823799879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136215626623830719060266021 25540429991968259823799879)
    ·
      refine ⟨38310644987952389735699819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25540429991968259823799879 38310644987952389735699819)
      ·
        refine ⟨57465967481928584603549729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38310644987952389735699819 57465967481928584603549729)
        ·
          refine ⟨43099475611446438452662297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57465967481928584603549729 43099475611446438452662297)
          ·
            refine ⟨32324606708584828839496723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43099475611446438452662297 32324606708584828839496723)
            ·
              refine ⟨48486910062877243259245085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32324606708584828839496723 48486910062877243259245085)
              ·
                refine ⟨18182591273578966222216907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48486910062877243259245085 18182591273578966222216907)
                ·
                  refine ⟨27273886910368449333325361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18182591273578966222216907 27273886910368449333325361)
                  ·
                    refine ⟨20455415182776336999994021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27273886910368449333325361 20455415182776336999994021)
                    ·
                      refine ⟨3835390346770563187498879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20455415182776336999994021 3835390346770563187498879)
                      ·
                        rfl

theorem cell23_7469396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_7469396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469396 prefixEnd_7469396 := by exact prefixLift 7469396
  have htrace : WordTrace (prefixWord ++ tailWord_7469396) baseStart_7469396 baseEnd_7469396 := by
    simpa [prefixWord, tailWord_7469396, baseEnd_7469396] using wordTrace_append hprefix tailTrace_7469396
  have hstable : (prefixWord ++ tailWord_7469396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469396).length < 2 ^ (prefixWord ++ tailWord_7469396).sum := by decide
  have hdescent : baseEnd_7469396 < baseStart_7469396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7469404 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7469404 : Nat := 118140960795 + 7469404 * 2 ^ 59
def prefixEnd_7469404 : Nat := 4983230072969 + 3 ^ 40 * 7469404 * 2
def baseEnd_7469404 : Nat := 3835394454615799156198843

theorem tailTrace_7469404 : CollatzResearch.WordTrace tailWord_7469404 prefixEnd_7469404 3835394454615799156198843 := by
  unfold tailWord_7469404
  simp only [CollatzResearch.WordTrace]
  refine ⟨136215772515816227743411633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181621030021088303657882177 136215772515816227743411633)
  ·
    refine ⟨102161829386862170807558725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136215772515816227743411633 102161829386862170807558725)
    ·
      refine ⟨19155343010036657026417261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102161829386862170807558725 19155343010036657026417261)
      ·
        refine ⟨7183253628763746384906473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19155343010036657026417261 7183253628763746384906473)
        ·
          refine ⟨5387440221572809788679855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7183253628763746384906473 5387440221572809788679855)
          ·
            refine ⟨8081160332359214683019783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387440221572809788679855 8081160332359214683019783)
            ·
              refine ⟨12121740498538822024529675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081160332359214683019783 12121740498538822024529675)
              ·
                refine ⟨18182610747808233036794513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12121740498538822024529675 18182610747808233036794513)
                ·
                  refine ⟨13636958060856174777595885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18182610747808233036794513 13636958060856174777595885)
                  ·
                    refine ⟨5113859272821065541598457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13636958060856174777595885 5113859272821065541598457)
                    ·
                      refine ⟨3835394454615799156198843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5113859272821065541598457 3835394454615799156198843)
                      ·
                        rfl

theorem cell23_7469404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7469404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7469404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7469404 prefixEnd_7469404 := by exact prefixLift 7469404
  have htrace : WordTrace (prefixWord ++ tailWord_7469404) baseStart_7469404 baseEnd_7469404 := by
    simpa [prefixWord, tailWord_7469404, baseEnd_7469404] using wordTrace_append hprefix tailTrace_7469404
  have hstable : (prefixWord ++ tailWord_7469404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7469404).length < 2 ^ (prefixWord ++ tailWord_7469404).sum := by decide
  have hdescent : baseEnd_7469404 < baseStart_7469404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7469404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
