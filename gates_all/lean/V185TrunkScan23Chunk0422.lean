import V185TrunkScan23Chunk0421

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2495151 : List Nat := [1, 1, 2, 1, 2, 16]
def baseStart_2495151 : Nat := 118140960795 + 2495151 * 2 ^ 59
def prefixEnd_2495151 : Nat := 4983230072969 + 3 ^ 40 * 2495151 * 2
def baseEnd_2495151 : Nat := 5272476413772314584105

theorem tailTrace_2495151 : CollatzResearch.WordTrace tailWord_2495151 prefixEnd_2495151 5272476413772314584105 := by
  unfold tailWord_2495151
  simp only [CollatzResearch.WordTrace]
  refine ⟨91005633383501539709341307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60670422255667693139560871 91005633383501539709341307)
  ·
    refine ⟨136508450075252309564011961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91005633383501539709341307 136508450075252309564011961)
    ·
      refine ⟨102381337556439232173008971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136508450075252309564011961 102381337556439232173008971)
      ·
        refine ⟨153572006334658848259513457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102381337556439232173008971 153572006334658848259513457)
        ·
          refine ⟨115179004750994136194635093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153572006334658848259513457 115179004750994136194635093)
          ·
            refine ⟨5272476413772314584105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 115179004750994136194635093 5272476413772314584105)
            ·
              rfl

theorem cell23_2495151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 16].length) (baseStart_2495151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495151 prefixEnd_2495151 := by exact prefixLift 2495151
  have htrace : WordTrace (prefixWord ++ tailWord_2495151) baseStart_2495151 baseEnd_2495151 := by
    simpa [prefixWord, tailWord_2495151, baseEnd_2495151] using wordTrace_append hprefix tailTrace_2495151
  have hstable : (prefixWord ++ tailWord_2495151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495151).length < 2 ^ (prefixWord ++ tailWord_2495151).sum := by decide
  have hdescent : baseEnd_2495151 < baseStart_2495151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495155 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 2, 4]
def baseStart_2495155 : Nat := 118140960795 + 2495155 * 2 ^ 59
def prefixEnd_2495155 : Nat := 4983230072969 + 3 ^ 40 * 2495155 * 2
def baseEnd_2495155 : Nat := 427071274156430142762499

theorem tailTrace_2495155 : CollatzResearch.WordTrace tailWord_2495155 prefixEnd_2495155 427071274156430142762499 := by
  unfold tailWord_2495155
  simp only [CollatzResearch.WordTrace]
  refine ⟨91005779275487048392486919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60670519516991365594991279 91005779275487048392486919)
  ·
    refine ⟨136508668913230572588730379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91005779275487048392486919 136508668913230572588730379)
    ·
      refine ⟨204763003369845858883095569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136508668913230572588730379 204763003369845858883095569)
      ·
        refine ⟨153572252527384394162321677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204763003369845858883095569 153572252527384394162321677)
        ·
          refine ⟨57589594697769147810870629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153572252527384394162321677 57589594697769147810870629)
          ·
            refine ⟨10798049005831715214538243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57589594697769147810870629 10798049005831715214538243)
            ·
              refine ⟨16197073508747572821807365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798049005831715214538243 16197073508747572821807365)
              ·
                refine ⟨3036951282890169904088881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16197073508747572821807365 3036951282890169904088881)
                ·
                  refine ⟨2277713462167627428066661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036951282890169904088881 2277713462167627428066661)
                  ·
                    refine ⟨427071274156430142762499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277713462167627428066661 427071274156430142762499)
                    ·
                      rfl

theorem cell23_2495155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 4].length) (baseStart_2495155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495155 prefixEnd_2495155 := by exact prefixLift 2495155
  have htrace : WordTrace (prefixWord ++ tailWord_2495155) baseStart_2495155 baseEnd_2495155 := by
    simpa [prefixWord, tailWord_2495155, baseEnd_2495155] using wordTrace_append hprefix tailTrace_2495155
  have hstable : (prefixWord ++ tailWord_2495155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495155).length < 2 ^ (prefixWord ++ tailWord_2495155).sum := by decide
  have hdescent : baseEnd_2495155 < baseStart_2495155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495162 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_2495162 : Nat := 118140960795 + 2495162 * 2 ^ 59
def prefixEnd_2495162 : Nat := 4983230072969 + 3 ^ 40 * 2495162 * 2
def baseEnd_2495162 : Nat := 1281217416833871900899965

theorem tailTrace_2495162 : CollatzResearch.WordTrace tailWord_2495162 prefixEnd_2495162 1281217416833871900899965 := by
  unfold tailWord_2495162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751508646615422146997935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60670689724307792391994493 22751508646615422146997935)
  ·
    refine ⟨34127262969923133220496903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22751508646615422146997935 34127262969923133220496903)
    ·
      refine ⟨51190894454884699830745355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34127262969923133220496903 51190894454884699830745355)
      ·
        refine ⟨76786341682327049746118033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51190894454884699830745355 76786341682327049746118033)
        ·
          refine ⟨57589756261745287309588525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76786341682327049746118033 57589756261745287309588525)
          ·
            refine ⟨21596158598154482741095697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57589756261745287309588525 21596158598154482741095697)
            ·
              refine ⟨16197118948615862055821773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21596158598154482741095697 16197118948615862055821773)
              ·
                refine ⟨6073919605730948270933165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16197118948615862055821773 6073919605730948270933165)
                ·
                  refine ⟨2277719852149105601599937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6073919605730948270933165 2277719852149105601599937)
                  ·
                    refine ⟨1708289889111829201199953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277719852149105601599937 1708289889111829201199953)
                    ·
                      refine ⟨1281217416833871900899965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708289889111829201199953 1281217416833871900899965)
                      ·
                        rfl

theorem cell23_2495162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_2495162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495162 prefixEnd_2495162 := by exact prefixLift 2495162
  have htrace : WordTrace (prefixWord ++ tailWord_2495162) baseStart_2495162 baseEnd_2495162 := by
    simpa [prefixWord, tailWord_2495162, baseEnd_2495162] using wordTrace_append hprefix tailTrace_2495162
  have hstable : (prefixWord ++ tailWord_2495162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495162).length < 2 ^ (prefixWord ++ tailWord_2495162).sum := by decide
  have hdescent : baseEnd_2495162 < baseStart_2495162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495165 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2495165 : Nat := 118140960795 + 2495165 * 2 ^ 59
def prefixEnd_2495165 : Nat := 4983230072969 + 3 ^ 40 * 2495165 * 2
def baseEnd_2495165 : Nat := 1281218957275835389162451

theorem tailTrace_2495165 : CollatzResearch.WordTrace tailWord_2495165 prefixEnd_2495165 1281218957275835389162451 := by
  unfold tailWord_2495165
  simp only [CollatzResearch.WordTrace]
  refine ⟨91006144005450820100350949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60670762670300546733567299 91006144005450820100350949)
  ·
    refine ⟨17063652001022028768815803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91006144005450820100350949 17063652001022028768815803)
    ·
      refine ⟨25595478001533043153223705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17063652001022028768815803 25595478001533043153223705)
      ·
        refine ⟨19196608501149782364917779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25595478001533043153223705 19196608501149782364917779)
        ·
          refine ⟨28794912751724673547376669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19196608501149782364917779 28794912751724673547376669)
          ·
            refine ⟨10798092281896752580266251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28794912751724673547376669 10798092281896752580266251)
            ·
              refine ⟨16197138422845128870399377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798092281896752580266251 16197138422845128870399377)
              ·
                refine ⟨12147853817133846652799533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16197138422845128870399377 12147853817133846652799533)
                ·
                  refine ⟨4555445181425192494799825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12147853817133846652799533 4555445181425192494799825)
                  ·
                    refine ⟨3416583886068894371099869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555445181425192494799825 3416583886068894371099869)
                    ·
                      refine ⟨1281218957275835389162451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3416583886068894371099869 1281218957275835389162451)
                      ·
                        rfl

theorem cell23_2495165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2495165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495165 prefixEnd_2495165 := by exact prefixLift 2495165
  have htrace : WordTrace (prefixWord ++ tailWord_2495165) baseStart_2495165 baseEnd_2495165 := by
    simpa [prefixWord, tailWord_2495165, baseEnd_2495165] using wordTrace_append hprefix tailTrace_2495165
  have hstable : (prefixWord ++ tailWord_2495165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495165).length < 2 ^ (prefixWord ++ tailWord_2495165).sum := by decide
  have hdescent : baseEnd_2495165 < baseStart_2495165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495168 : List Nat := [2, 1, 1, 2, 4, 2, 3, 8]
def baseStart_2495168 : Nat := 118140960795 + 2495168 * 2 ^ 59
def prefixEnd_2495168 : Nat := 4983230072969 + 3 ^ 40 * 2495168 * 2
def baseEnd_2495168 : Nat := 47452611026585143608331

theorem tailTrace_2495168 : CollatzResearch.WordTrace tailWord_2495168 prefixEnd_2495168 47452611026585143608331 := by
  unfold tailWord_2495168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503126712219975806355079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60670835616293301075140105 45503126712219975806355079)
  ·
    refine ⟨68254690068329963709532619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45503126712219975806355079 68254690068329963709532619)
    ·
      refine ⟨102382035102494945564298929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68254690068329963709532619 102382035102494945564298929)
      ·
        refine ⟨76786526326871209173224197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102382035102494945564298929 76786526326871209173224197)
        ·
          refine ⟨14397473686288351719979537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76786526326871209173224197 14397473686288351719979537)
          ·
            refine ⟨10798105264716263789984653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14397473686288351719979537 10798105264716263789984653)
            ·
              refine ⟨4049289474268598921244245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10798105264716263789984653 4049289474268598921244245)
              ·
                refine ⟨47452611026585143608331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4049289474268598921244245 47452611026585143608331)
                ·
                  rfl

theorem cell23_2495168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_2495168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495168 prefixEnd_2495168 := by exact prefixLift 2495168
  have htrace : WordTrace (prefixWord ++ tailWord_2495168) baseStart_2495168 baseEnd_2495168 := by
    simpa [prefixWord, tailWord_2495168, baseEnd_2495168] using wordTrace_append hprefix tailTrace_2495168
  have hstable : (prefixWord ++ tailWord_2495168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495168).length < 2 ^ (prefixWord ++ tailWord_2495168).sum := by decide
  have hdescent : baseEnd_2495168 < baseStart_2495168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495172 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2495172 : Nat := 118140960795 + 2495172 * 2 ^ 59
def prefixEnd_2495172 : Nat := 4983230072969 + 3 ^ 40 * 2495172 * 2
def baseEnd_2495172 : Nat := 427074183880138953924973

theorem tailTrace_2495172 : CollatzResearch.WordTrace tailWord_2495172 prefixEnd_2495172 427074183880138953924973 := by
  unfold tailWord_2495172
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503199658212730147927885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60670932877616973530570513 45503199658212730147927885)
  ·
    refine ⟨17063699871829773805472957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45503199658212730147927885 17063699871829773805472957)
    ·
      refine ⟨6398887451936165177052359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17063699871829773805472957 6398887451936165177052359)
      ·
        refine ⟨9598331177904247765578539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398887451936165177052359 9598331177904247765578539)
        ·
          refine ⟨14397496766856371648367809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9598331177904247765578539 14397496766856371648367809)
          ·
            refine ⟨10798122575142278736275857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14397496766856371648367809 10798122575142278736275857)
            ·
              refine ⟨8098591931356709052206893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10798122575142278736275857 8098591931356709052206893)
              ·
                refine ⟨3036971974258765894577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8098591931356709052206893 3036971974258765894577585)
                ·
                  refine ⟨2277728980694074420933189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036971974258765894577585 2277728980694074420933189)
                  ·
                    refine ⟨427074183880138953924973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277728980694074420933189 427074183880138953924973)
                    ·
                      rfl

theorem cell23_2495172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2495172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495172 prefixEnd_2495172 := by exact prefixLift 2495172
  have htrace : WordTrace (prefixWord ++ tailWord_2495172) baseStart_2495172 baseEnd_2495172 := by
    simpa [prefixWord, tailWord_2495172, baseEnd_2495172] using wordTrace_append hprefix tailTrace_2495172
  have hstable : (prefixWord ++ tailWord_2495172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495172).length < 2 ^ (prefixWord ++ tailWord_2495172).sum := by decide
  have hdescent : baseEnd_2495172 < baseStart_2495172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495196 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2495196 : Nat := 118140960795 + 2495196 * 2 ^ 59
def prefixEnd_2495196 : Nat := 4983230072969 + 3 ^ 40 * 2495196 * 2
def baseEnd_2495196 : Nat := 1281234875176124767874809

theorem tailTrace_2495196 : CollatzResearch.WordTrace tailWord_2495196 prefixEnd_2495196 1281234875176124767874809 := by
  unfold tailWord_2495196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503637334169256197364721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60671516445559008263152961 45503637334169256197364721)
  ·
    refine ⟨34127728000626942148023541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45503637334169256197364721 34127728000626942148023541)
    ·
      refine ⟨3199474500058775826377207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34127728000626942148023541 3199474500058775826377207)
      ·
        refine ⟨4799211750088163739565811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199474500058775826377207 4799211750088163739565811)
        ·
          refine ⟨7198817625132245609348717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799211750088163739565811 7198817625132245609348717)
          ·
            refine ⟨2699556609424592103505769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7198817625132245609348717 2699556609424592103505769)
            ·
              refine ⟨2024667457068444077629327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699556609424592103505769 2024667457068444077629327)
              ·
                refine ⟨3037001185602666116443991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024667457068444077629327 3037001185602666116443991)
                ·
                  refine ⟨4555501778403999174665987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037001185602666116443991 4555501778403999174665987)
                  ·
                    refine ⟨6833252667605998761998981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4555501778403999174665987 6833252667605998761998981)
                    ·
                      refine ⟨1281234875176124767874809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6833252667605998761998981 1281234875176124767874809)
                      ·
                        rfl

theorem cell23_2495196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2495196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495196 prefixEnd_2495196 := by exact prefixLift 2495196
  have htrace : WordTrace (prefixWord ++ tailWord_2495196) baseStart_2495196 baseEnd_2495196 := by
    simpa [prefixWord, tailWord_2495196, baseEnd_2495196] using wordTrace_append hprefix tailTrace_2495196
  have hstable : (prefixWord ++ tailWord_2495196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495196).length < 2 ^ (prefixWord ++ tailWord_2495196).sum := by decide
  have hdescent : baseEnd_2495196 < baseStart_2495196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495199 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 1, 2, 3]
def baseStart_2495199 : Nat := 118140960795 + 2495199 * 2 ^ 59
def prefixEnd_2495199 : Nat := 4983230072969 + 3 ^ 40 * 2495199 * 2
def baseEnd_2495199 : Nat := 1281236415618088256137295

theorem tailTrace_2495199 : CollatzResearch.WordTrace tailWord_2495199 prefixEnd_2495199 1281236415618088256137295 := by
  unfold tailWord_2495199
  simp only [CollatzResearch.WordTrace]
  refine ⟨91007384087327643907088651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60671589391551762604725767 91007384087327643907088651)
  ·
    refine ⟨136511076130991465860632977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91007384087327643907088651 136511076130991465860632977)
    ·
      refine ⟨102383307098243599395474733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136511076130991465860632977 102383307098243599395474733)
      ·
        refine ⟨38393740161841349773303025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102383307098243599395474733 38393740161841349773303025)
        ·
          refine ⟨28795305121381012329977269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38393740161841349773303025 28795305121381012329977269)
          ·
            refine ⟨2699559855129469905935369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28795305121381012329977269 2699559855129469905935369)
            ·
              refine ⟨2024669891347102429451527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699559855129469905935369 2024669891347102429451527)
              ·
                refine ⟨3037004837020653644177291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024669891347102429451527 3037004837020653644177291)
                ·
                  refine ⟨4555507255530980466265937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037004837020653644177291 4555507255530980466265937)
                  ·
                    refine ⟨3416630441648235349699453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4555507255530980466265937 3416630441648235349699453)
                    ·
                      refine ⟨1281236415618088256137295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3416630441648235349699453 1281236415618088256137295)
                      ·
                        rfl

theorem cell23_2495199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_2495199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495199 prefixEnd_2495199 := by exact prefixLift 2495199
  have htrace : WordTrace (prefixWord ++ tailWord_2495199) baseStart_2495199 baseEnd_2495199 := by
    simpa [prefixWord, tailWord_2495199, baseEnd_2495199] using wordTrace_append hprefix tailTrace_2495199
  have hstable : (prefixWord ++ tailWord_2495199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495199).length < 2 ^ (prefixWord ++ tailWord_2495199).sum := by decide
  have hdescent : baseEnd_2495199 < baseStart_2495199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495229 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_2495229 : Nat := 118140960795 + 2495229 * 2 ^ 59
def prefixEnd_2495229 : Nat := 4983230072969 + 3 ^ 40 * 2495229 * 2
def baseEnd_2495229 : Nat := 1281251820037723138762157

theorem tailTrace_2495229 : CollatzResearch.WordTrace tailWord_2495229 prefixEnd_2495229 1281251820037723138762157 := by
  unfold tailWord_2495229
  simp only [CollatzResearch.WordTrace]
  refine ⟨91008478277218959030680741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60672318851479306020453827 91008478277218959030680741)
  ·
    refine ⟨17064089676978554818252639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91008478277218959030680741 17064089676978554818252639)
    ·
      refine ⟨25596134515467832227378959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17064089676978554818252639 25596134515467832227378959)
      ·
        refine ⟨38394201773201748341068439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25596134515467832227378959 38394201773201748341068439)
        ·
          refine ⟨57591302659802622511602659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38394201773201748341068439 57591302659802622511602659)
          ·
            refine ⟨86386953989703933767403989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57591302659802622511602659 86386953989703933767403989)
            ·
              refine ⟨2024694234133685947673531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86386953989703933767403989 2024694234133685947673531)
              ·
                refine ⟨3037041351200528921510297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024694234133685947673531 3037041351200528921510297)
                ·
                  refine ⟨2277781013400396691132723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037041351200528921510297 2277781013400396691132723)
                  ·
                    refine ⟨3416671520100595036699085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2277781013400396691132723 3416671520100595036699085)
                    ·
                      refine ⟨1281251820037723138762157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3416671520100595036699085 1281251820037723138762157)
                      ·
                        rfl

theorem cell23_2495229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_2495229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495229 prefixEnd_2495229 := by exact prefixLift 2495229
  have htrace : WordTrace (prefixWord ++ tailWord_2495229) baseStart_2495229 baseEnd_2495229 := by
    simpa [prefixWord, tailWord_2495229, baseEnd_2495229] using wordTrace_append hprefix tailTrace_2495229
  have hstable : (prefixWord ++ tailWord_2495229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495229).length < 2 ^ (prefixWord ++ tailWord_2495229).sum := by decide
  have hdescent : baseEnd_2495229 < baseStart_2495229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495239 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2495239 : Nat := 118140960795 + 2495239 * 2 ^ 59
def prefixEnd_2495239 : Nat := 4983230072969 + 3 ^ 40 * 2495239 * 2
def baseEnd_2495239 : Nat := 1281256954844268099637111

theorem tailTrace_2495239 : CollatzResearch.WordTrace tailWord_2495239 prefixEnd_2495239 1281256954844268099637111 := by
  unfold tailWord_2495239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91008843007182730738544771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60672562004788487159029847 91008843007182730738544771)
  ·
    refine ⟨136513264510774096107817157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91008843007182730738544771 136513264510774096107817157)
    ·
      refine ⟨25596237095770143020215717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136513264510774096107817157 25596237095770143020215717)
      ·
        refine ⟨4799294455456901816290447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25596237095770143020215717 4799294455456901816290447)
        ·
          refine ⟨7198941683185352724435671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799294455456901816290447 7198941683185352724435671)
          ·
            refine ⟨10798412524778029086653507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198941683185352724435671 10798412524778029086653507)
            ·
              refine ⟨16197618787167043629980261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798412524778029086653507 16197618787167043629980261)
              ·
                refine ⟨3037053522593820680621299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16197618787167043629980261 3037053522593820680621299)
                ·
                  refine ⟨4555580283890731020931949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037053522593820680621299 4555580283890731020931949)
                  ·
                    refine ⟨1708342606459024132849481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4555580283890731020931949 1708342606459024132849481)
                    ·
                      refine ⟨1281256954844268099637111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708342606459024132849481 1281256954844268099637111)
                      ·
                        rfl

theorem cell23_2495239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2495239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495239 prefixEnd_2495239 := by exact prefixLift 2495239
  have htrace : WordTrace (prefixWord ++ tailWord_2495239) baseStart_2495239 baseEnd_2495239 := by
    simpa [prefixWord, tailWord_2495239, baseEnd_2495239] using wordTrace_append hprefix tailTrace_2495239
  have hstable : (prefixWord ++ tailWord_2495239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495239).length < 2 ^ (prefixWord ++ tailWord_2495239).sum := by decide
  have hdescent : baseEnd_2495239 < baseStart_2495239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495269 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 2, 2, 2]
def baseStart_2495269 : Nat := 118140960795 + 2495269 * 2 ^ 59
def prefixEnd_2495269 : Nat := 4983230072969 + 3 ^ 40 * 2495269 * 2
def baseEnd_2495269 : Nat := 1281272359263902982261973

theorem tailTrace_2495269 : CollatzResearch.WordTrace tailWord_2495269 prefixEnd_2495269 1281272359263902982261973 := by
  unfold tailWord_2495269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91009937197074045862136861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60673291464716030574757907 91009937197074045862136861)
  ·
    refine ⟨34128726448902767198301323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91009937197074045862136861 34128726448902767198301323)
    ·
      refine ⟨51193089673354150797451985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34128726448902767198301323 51193089673354150797451985)
      ·
        refine ⟨38394817255015613098088989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51193089673354150797451985 38394817255015613098088989)
        ·
          refine ⟨14398056470630854911783371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38394817255015613098088989 14398056470630854911783371)
          ·
            refine ⟨21597084705946282367675057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14398056470630854911783371 21597084705946282367675057)
            ·
              refine ⟨16197813529459711775756293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21597084705946282367675057 16197813529459711775756293)
              ·
                refine ⟨3037090036773695957954305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16197813529459711775756293 3037090036773695957954305)
                ·
                  refine ⟨2277817527580271968465729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037090036773695957954305 2277817527580271968465729)
                  ·
                    refine ⟨1708363145685203976349297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2277817527580271968465729 1708363145685203976349297)
                    ·
                      refine ⟨1281272359263902982261973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708363145685203976349297 1281272359263902982261973)
                      ·
                        rfl

theorem cell23_2495269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_2495269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495269 prefixEnd_2495269 := by exact prefixLift 2495269
  have htrace : WordTrace (prefixWord ++ tailWord_2495269) baseStart_2495269 baseEnd_2495269 := by
    simpa [prefixWord, tailWord_2495269, baseEnd_2495269] using wordTrace_append hprefix tailTrace_2495269
  have hstable : (prefixWord ++ tailWord_2495269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495269).length < 2 ^ (prefixWord ++ tailWord_2495269).sum := by decide
  have hdescent : baseEnd_2495269 < baseStart_2495269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495305 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_2495305 : Nat := 118140960795 + 2495305 * 2 ^ 59
def prefixEnd_2495305 : Nat := 4983230072969 + 3 ^ 40 * 2495305 * 2
def baseEnd_2495305 : Nat := 427096948189154947137269

theorem tailTrace_2495305 : CollatzResearch.WordTrace tailWord_2495305 prefixEnd_2495305 427096948189154947137269 := by
  unfold tailWord_2495305
  simp only [CollatzResearch.WordTrace]
  refine ⟨91011250224943624010447369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60674166816629082673631579 91011250224943624010447369)
  ·
    refine ⟨68258437668707718007835527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91011250224943624010447369 68258437668707718007835527)
    ·
      refine ⟨102387656503061577011753291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68258437668707718007835527 102387656503061577011753291)
      ·
        refine ⟨153581484754592365517629937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102387656503061577011753291 153581484754592365517629937)
        ·
          refine ⟨115186113565944274138222453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153581484754592365517629937 115186113565944274138222453)
          ·
            refine ⟨10798698146807275700458355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115186113565944274138222453 10798698146807275700458355)
            ·
              refine ⟨16198047220210913550687533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798698146807275700458355 16198047220210913550687533)
              ·
                refine ⟨6074267707579092581507825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16198047220210913550687533 6074267707579092581507825)
                ·
                  refine ⟨4555700780684319436130869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6074267707579092581507825 4555700780684319436130869)
                  ·
                    refine ⟨427096948189154947137269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4555700780684319436130869 427096948189154947137269)
                    ·
                      rfl

theorem cell23_2495305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_2495305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495305 prefixEnd_2495305 := by exact prefixLift 2495305
  have htrace : WordTrace (prefixWord ++ tailWord_2495305) baseStart_2495305 baseEnd_2495305 := by
    simpa [prefixWord, tailWord_2495305, baseEnd_2495305] using wordTrace_append hprefix tailTrace_2495305
  have hstable : (prefixWord ++ tailWord_2495305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495305).length < 2 ^ (prefixWord ++ tailWord_2495305).sum := by decide
  have hdescent : baseEnd_2495305 < baseStart_2495305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495369 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 1, 4]
def baseStart_2495369 : Nat := 118140960795 + 2495369 * 2 ^ 59
def prefixEnd_2495369 : Nat := 4983230072969 + 3 ^ 40 * 2495369 * 2
def baseEnd_2495369 : Nat := 427107902443117530337171

theorem tailTrace_2495369 : CollatzResearch.WordTrace tailWord_2495369 prefixEnd_2495369 427107902443117530337171 := by
  unfold tailWord_2495369
  simp only [CollatzResearch.WordTrace]
  refine ⟨91013584496711762940777161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60675722997807841960518107 91013584496711762940777161)
  ·
    refine ⟨68260188372533822205582871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91013584496711762940777161 68260188372533822205582871)
    ·
      refine ⟨102390282558800733308374307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68260188372533822205582871 102390282558800733308374307)
      ·
        refine ⟨153585423838201099962561461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102390282558800733308374307 153585423838201099962561461)
        ·
          refine ⟨14398633484831353121490137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153585423838201099962561461 14398633484831353121490137)
          ·
            refine ⟨10798975113623514841117603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14398633484831353121490137 10798975113623514841117603)
            ·
              refine ⟨16198462670435272261676405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10798975113623514841117603 16198462670435272261676405)
              ·
                refine ⟨1518605875353306774532163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16198462670435272261676405 1518605875353306774532163)
                ·
                  refine ⟨2277908813029960161798245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518605875353306774532163 2277908813029960161798245)
                  ·
                    refine ⟨427107902443117530337171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277908813029960161798245 427107902443117530337171)
                    ·
                      rfl

theorem cell23_2495369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_2495369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495369 prefixEnd_2495369 := by exact prefixLift 2495369
  have htrace : WordTrace (prefixWord ++ tailWord_2495369) baseStart_2495369 baseEnd_2495369 := by
    simpa [prefixWord, tailWord_2495369, baseEnd_2495369] using wordTrace_append hprefix tailTrace_2495369
  have hstable : (prefixWord ++ tailWord_2495369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495369).length < 2 ^ (prefixWord ++ tailWord_2495369).sum := by decide
  have hdescent : baseEnd_2495369 < baseStart_2495369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495395 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 5, 5]
def baseStart_2495395 : Nat := 118140960795 + 2495395 * 2 ^ 59
def prefixEnd_2495395 : Nat := 4983230072969 + 3 ^ 40 * 2495395 * 2
def baseEnd_2495395 : Nat := 427112352608789829762131

theorem tailTrace_2495395 : CollatzResearch.WordTrace tailWord_2495395 prefixEnd_2495395 427112352608789829762131 := by
  unfold tailWord_2495395
  simp only [CollatzResearch.WordTrace]
  refine ⟨91014532794617569381223639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60676355196411712920815759 91014532794617569381223639)
  ·
    refine ⟨136521799191926354071835459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91014532794617569381223639 136521799191926354071835459)
    ·
      refine ⟨204782698787889531107753189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136521799191926354071835459 204782698787889531107753189)
      ·
        refine ⟨38396756022729287082703723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204782698787889531107753189 38396756022729287082703723)
        ·
          refine ⟨57595134034093930624055585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38396756022729287082703723 57595134034093930624055585)
          ·
            refine ⟨43196350525570447968041689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57595134034093930624055585 43196350525570447968041689)
            ·
              refine ⟨32397262894177835976031267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43196350525570447968041689 32397262894177835976031267)
              ·
                refine ⟨48595894341266753964046901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32397262894177835976031267 48595894341266753964046901)
                ·
                  refine ⟨4555865094493758184129397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48595894341266753964046901 4555865094493758184129397)
                  ·
                    refine ⟨427112352608789829762131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4555865094493758184129397 427112352608789829762131)
                    ·
                      rfl

theorem cell23_2495395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].length) (baseStart_2495395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495395 prefixEnd_2495395 := by exact prefixLift 2495395
  have htrace : WordTrace (prefixWord ++ tailWord_2495395) baseStart_2495395 baseEnd_2495395 := by
    simpa [prefixWord, tailWord_2495395, baseEnd_2495395] using wordTrace_append hprefix tailTrace_2495395
  have hstable : (prefixWord ++ tailWord_2495395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495395).length < 2 ^ (prefixWord ++ tailWord_2495395).sum := by decide
  have hdescent : baseEnd_2495395 < baseStart_2495395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495437 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2495437 : Nat := 118140960795 + 2495437 * 2 ^ 59
def prefixEnd_2495437 : Nat := 4983230072969 + 3 ^ 40 * 2495437 * 2
def baseEnd_2495437 : Nat := 427119541337952774987067

theorem tailTrace_2495437 : CollatzResearch.WordTrace tailWord_2495437 prefixEnd_2495437 427119541337952774987067 := by
  unfold tailWord_2495437
  simp only [CollatzResearch.WordTrace]
  refine ⟨91016064660465410554252565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60677376440310273702835043 91016064660465410554252565)
  ·
    refine ⟨4266378030959316119730589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91016064660465410554252565 4266378030959316119730589)
    ·
      refine ⟨1599891761609743544898971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4266378030959316119730589 1599891761609743544898971)
      ·
        refine ⟨2399837642414615317348457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599891761609743544898971 2399837642414615317348457)
        ·
          refine ⟨1799878231810961488011343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2399837642414615317348457 1799878231810961488011343)
          ·
            refine ⟨2699817347716442232017015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799878231810961488011343 2699817347716442232017015)
            ·
              refine ⟨4049726021574663348025523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699817347716442232017015 4049726021574663348025523)
              ·
                refine ⟨6074589032361995022038285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049726021574663348025523 6074589032361995022038285)
                ·
                  refine ⟨2277970887135748133264357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6074589032361995022038285 2277970887135748133264357)
                  ·
                    refine ⟨427119541337952774987067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277970887135748133264357 427119541337952774987067)
                    ·
                      rfl

theorem cell23_2495437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2495437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495437 prefixEnd_2495437 := by exact prefixLift 2495437
  have htrace : WordTrace (prefixWord ++ tailWord_2495437) baseStart_2495437 baseEnd_2495437 := by
    simpa [prefixWord, tailWord_2495437, baseEnd_2495437] using wordTrace_append hprefix tailTrace_2495437
  have hstable : (prefixWord ++ tailWord_2495437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495437).length < 2 ^ (prefixWord ++ tailWord_2495437).sum := by decide
  have hdescent : baseEnd_2495437 < baseStart_2495437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495459 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 2, 4]
def baseStart_2495459 : Nat := 118140960795 + 2495459 * 2 ^ 59
def prefixEnd_2495459 : Nat := 4983230072969 + 3 ^ 40 * 2495459 * 2
def baseEnd_2495459 : Nat := 427123306862752412962033

theorem tailTrace_2495459 : CollatzResearch.WordTrace tailWord_2495459 prefixEnd_2495459 427123306862752412962033 := by
  unfold tailWord_2495459
  simp only [CollatzResearch.WordTrace]
  refine ⟨91016867066385708311553431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60677911377590472207702287 91016867066385708311553431)
  ·
    refine ⟨136525300599578562467330147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91016867066385708311553431 136525300599578562467330147)
    ·
      refine ⟨204787950899367843700995221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136525300599578562467330147 204787950899367843700995221)
      ·
        refine ⟨9599435198407867673484151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 204787950899367843700995221 9599435198407867673484151)
        ·
          refine ⟨14399152797611801510226227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9599435198407867673484151 14399152797611801510226227)
          ·
            refine ⟨21598729196417702265339341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14399152797611801510226227 21598729196417702265339341)
            ·
              refine ⟨8099523448656638349502253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21598729196417702265339341 8099523448656638349502253)
              ·
                refine ⟨3037321293246239381063345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8099523448656638349502253 3037321293246239381063345)
                ·
                  refine ⟨2277990969934679535797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037321293246239381063345 2277990969934679535797509)
                  ·
                    refine ⟨427123306862752412962033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277990969934679535797509 427123306862752412962033)
                    ·
                      rfl

theorem cell23_2495459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 4].length) (baseStart_2495459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495459 prefixEnd_2495459 := by exact prefixLift 2495459
  have htrace : WordTrace (prefixWord ++ tailWord_2495459) baseStart_2495459 baseEnd_2495459 := by
    simpa [prefixWord, tailWord_2495459, baseEnd_2495459] using wordTrace_append hprefix tailTrace_2495459
  have hstable : (prefixWord ++ tailWord_2495459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495459).length < 2 ^ (prefixWord ++ tailWord_2495459).sum := by decide
  have hdescent : baseEnd_2495459 < baseStart_2495459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495466 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2495466 : Nat := 118140960795 + 2495466 * 2 ^ 59
def prefixEnd_2495466 : Nat := 4983230072969 + 3 ^ 40 * 2495466 * 2
def baseEnd_2495466 : Nat := 1281373514952838711498567

theorem tailTrace_2495466 : CollatzResearch.WordTrace tailWord_2495466 prefixEnd_2495466 1281373514952838711498567 := by
  unfold tailWord_2495466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22754280594340087126764563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60678081584906899004705501 22754280594340087126764563)
  ·
    refine ⟨34131420891510130690146845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22754280594340087126764563 34131420891510130690146845)
    ·
      refine ⟨12799282834316299008805067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34131420891510130690146845 12799282834316299008805067)
      ·
        refine ⟨19198924251474448513207601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12799282834316299008805067 19198924251474448513207601)
        ·
          refine ⟨14399193188605836384905701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19198924251474448513207601 14399193188605836384905701)
          ·
            refine ⟨2699848722863594322169819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14399193188605836384905701 2699848722863594322169819)
            ·
              refine ⟨4049773084295391483254729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699848722863594322169819 4049773084295391483254729)
              ·
                refine ⟨3037329813221543612441047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049773084295391483254729 3037329813221543612441047)
                ·
                  refine ⟨4555994719832315418661571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037329813221543612441047 4555994719832315418661571)
                  ·
                    refine ⟨6833992079748473127992357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4555994719832315418661571 6833992079748473127992357)
                    ·
                      refine ⟨1281373514952838711498567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6833992079748473127992357 1281373514952838711498567)
                      ·
                        rfl

theorem cell23_2495466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2495466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495466 prefixEnd_2495466 := by exact prefixLift 2495466
  have htrace : WordTrace (prefixWord ++ tailWord_2495466) baseStart_2495466 baseEnd_2495466 := by
    simpa [prefixWord, tailWord_2495466, baseEnd_2495466] using wordTrace_append hprefix tailTrace_2495466
  have hstable : (prefixWord ++ tailWord_2495466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495466).length < 2 ^ (prefixWord ++ tailWord_2495466).sum := by decide
  have hdescent : baseEnd_2495466 < baseStart_2495466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495500 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 1, 2, 2]
def baseStart_2495500 : Nat := 118140960795 + 2495500 * 2 ^ 59
def prefixEnd_2495500 : Nat := 4983230072969 + 3 ^ 40 * 2495500 * 2
def baseEnd_2495500 : Nat := 1281390973295091578473411

theorem tailTrace_2495500 : CollatzResearch.WordTrace tailWord_2495500 prefixEnd_2495500 1281390973295091578473411 := by
  unfold tailWord_2495500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45509181229618586156897977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60678908306158114875863969 45509181229618586156897977)
  ·
    refine ⟨34131885922213939617673483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45509181229618586156897977 34131885922213939617673483)
    ·
      refine ⟨51197828883320909426510225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34131885922213939617673483 51197828883320909426510225)
      ·
        refine ⟨38398371662490682069882669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51197828883320909426510225 38398371662490682069882669)
        ·
          refine ⟨14399389373434005776206001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38398371662490682069882669 14399389373434005776206001)
          ·
            refine ⟨10799542030075504332154501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14399389373434005776206001 10799542030075504332154501)
            ·
              refine ⟨2024914130639157062278969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10799542030075504332154501 2024914130639157062278969)
              ·
                refine ⟨1518685597979367796709227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024914130639157062278969 1518685597979367796709227)
                ·
                  refine ⟨2278028396969051695063841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518685597979367796709227 2278028396969051695063841)
                  ·
                    refine ⟨1708521297726788771297881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278028396969051695063841 1708521297726788771297881)
                    ·
                      refine ⟨1281390973295091578473411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708521297726788771297881 1281390973295091578473411)
                      ·
                        rfl

theorem cell23_2495500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_2495500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495500 prefixEnd_2495500 := by exact prefixLift 2495500
  have htrace : WordTrace (prefixWord ++ tailWord_2495500) baseStart_2495500 baseEnd_2495500 := by
    simpa [prefixWord, tailWord_2495500, baseEnd_2495500] using wordTrace_append hprefix tailTrace_2495500
  have hstable : (prefixWord ++ tailWord_2495500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495500).length < 2 ^ (prefixWord ++ tailWord_2495500).sum := by decide
  have hdescent : baseEnd_2495500 < baseStart_2495500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495502 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2495502 : Nat := 118140960795 + 2495502 * 2 ^ 59
def prefixEnd_2495502 : Nat := 4983230072969 + 3 ^ 40 * 2495502 * 2
def baseEnd_2495502 : Nat := 427130666752133523549467

theorem tailTrace_2495502 : CollatzResearch.WordTrace tailWord_2495502 prefixEnd_2495502 427130666752133523549467 := by
  unfold tailWord_2495502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377304425653740831921095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60678956936819951103579173 11377304425653740831921095)
  ·
    refine ⟨17065956638480611247881643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377304425653740831921095 17065956638480611247881643)
    ·
      refine ⟨25598934957720916871822465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17065956638480611247881643 25598934957720916871822465)
      ·
        refine ⟨19199201218290687653866849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25598934957720916871822465 19199201218290687653866849)
        ·
          refine ⟨14399400913718015740400137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19199201218290687653866849 14399400913718015740400137)
          ·
            refine ⟨10799550685288511805300103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14399400913718015740400137 10799550685288511805300103)
            ·
              refine ⟨16199326027932767707950155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10799550685288511805300103 16199326027932767707950155)
              ·
                refine ⟨24298989041899151561925233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16199326027932767707950155 24298989041899151561925233)
                ·
                  refine ⟨18224241781424363671443925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24298989041899151561925233 18224241781424363671443925)
                  ·
                    refine ⟨427130666752133523549467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18224241781424363671443925 427130666752133523549467)
                    ·
                      rfl

theorem cell23_2495502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2495502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495502 prefixEnd_2495502 := by exact prefixLift 2495502
  have htrace : WordTrace (prefixWord ++ tailWord_2495502) baseStart_2495502 baseEnd_2495502 := by
    simpa [prefixWord, tailWord_2495502, baseEnd_2495502] using wordTrace_append hprefix tailTrace_2495502
  have hstable : (prefixWord ++ tailWord_2495502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495502).length < 2 ^ (prefixWord ++ tailWord_2495502).sum := by decide
  have hdescent : baseEnd_2495502 < baseStart_2495502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495516 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2495516 : Nat := 118140960795 + 2495516 * 2 ^ 59
def prefixEnd_2495516 : Nat := 4983230072969 + 3 ^ 40 * 2495516 * 2
def baseEnd_2495516 : Nat := 1281399188985563515873337

theorem tailTrace_2495516 : CollatzResearch.WordTrace tailWord_2495516 prefixEnd_2495516 1281399188985563515873337 := by
  unfold tailWord_2495516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45509473013589603523189201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60679297351452804697585601 45509473013589603523189201)
  ·
    refine ⟨34132104760192202642391901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45509473013589603523189201 34132104760192202642391901)
    ·
      refine ⟨12799539285072075990896963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34132104760192202642391901 12799539285072075990896963)
      ·
        refine ⟨19199308927608113986345445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12799539285072075990896963 19199308927608113986345445)
        ·
          refine ⟨3599870423926521372439771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19199308927608113986345445 3599870423926521372439771)
          ·
            refine ⟨5399805635889782058659657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599870423926521372439771 5399805635889782058659657)
            ·
              refine ⟨4049854226917336543994743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5399805635889782058659657 4049854226917336543994743)
              ·
                refine ⟨6074781340376004815992115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049854226917336543994743 6074781340376004815992115)
                ·
                  refine ⟨9112172010564007223988173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6074781340376004815992115 9112172010564007223988173)
                  ·
                    refine ⟨3417064503961502708995565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9112172010564007223988173 3417064503961502708995565)
                    ·
                      refine ⟨1281399188985563515873337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417064503961502708995565 1281399188985563515873337)
                      ·
                        rfl

theorem cell23_2495516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2495516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495516 prefixEnd_2495516 := by exact prefixLift 2495516
  have htrace : WordTrace (prefixWord ++ tailWord_2495516) baseStart_2495516 baseEnd_2495516 := by
    simpa [prefixWord, tailWord_2495516, baseEnd_2495516] using wordTrace_append hprefix tailTrace_2495516
  have hstable : (prefixWord ++ tailWord_2495516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495516).length < 2 ^ (prefixWord ++ tailWord_2495516).sum := by decide
  have hdescent : baseEnd_2495516 < baseStart_2495516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495550 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2495550 : Nat := 118140960795 + 2495550 * 2 ^ 59
def prefixEnd_2495550 : Nat := 4983230072969 + 3 ^ 40 * 2495550 * 2
def baseEnd_2495550 : Nat := 1281416647327816382848181

theorem tailTrace_2495550 : CollatzResearch.WordTrace tailWord_2495550 prefixEnd_2495550 1281416647327816382848181 := by
  unfold tailWord_2495550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377523263632003856639513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60680124072704020568744069 11377523263632003856639513)
  ·
    refine ⟨8533142447724002892479635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11377523263632003856639513 8533142447724002892479635)
    ·
      refine ⟨12799713671586004338719453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8533142447724002892479635 12799713671586004338719453)
      ·
        refine ⟨4799892626844751627019795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12799713671586004338719453 4799892626844751627019795)
        ·
          refine ⟨7199838940267127440529693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799892626844751627019795 7199838940267127440529693)
          ·
            refine ⟨2699939602600172790198635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7199838940267127440529693 2699939602600172790198635)
            ·
              refine ⟨4049909403900259185297953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699939602600172790198635 4049909403900259185297953)
              ·
                refine ⟨3037432052925194388973465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049909403900259185297953 3037432052925194388973465)
                ·
                  refine ⟨2278074039693895791730099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037432052925194388973465 2278074039693895791730099)
                  ·
                    refine ⟨3417111059540843687595149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278074039693895791730099 3417111059540843687595149)
                    ·
                      refine ⟨1281416647327816382848181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417111059540843687595149 1281416647327816382848181)
                      ·
                        rfl

theorem cell23_2495550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2495550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495550 prefixEnd_2495550 := by exact prefixLift 2495550
  have htrace : WordTrace (prefixWord ++ tailWord_2495550) baseStart_2495550 baseEnd_2495550 := by
    simpa [prefixWord, tailWord_2495550, baseEnd_2495550] using wordTrace_append hprefix tailTrace_2495550
  have hstable : (prefixWord ++ tailWord_2495550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495550).length < 2 ^ (prefixWord ++ tailWord_2495550).sum := by decide
  have hdescent : baseEnd_2495550 < baseStart_2495550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495552 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2495552 : Nat := 118140960795 + 2495552 * 2 ^ 59
def prefixEnd_2495552 : Nat := 4983230072969 + 3 ^ 40 * 2495552 * 2
def baseEnd_2495552 : Nat := 1281417674289125375023171

theorem tailTrace_2495552 : CollatzResearch.WordTrace tailWord_2495552 prefixEnd_2495552 1281417674289125375023171 := by
  unfold tailWord_2495552
  simp only [CollatzResearch.WordTrace]
  refine ⟨45510129527524392597344455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60680172703365856796459273 45510129527524392597344455)
  ·
    refine ⟨68265194291286588896016683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45510129527524392597344455 68265194291286588896016683)
    ·
      refine ⟨102397791436929883344025025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68265194291286588896016683 102397791436929883344025025)
      ·
        refine ⟨76798343577697412508018769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102397791436929883344025025 76798343577697412508018769)
        ·
          refine ⟨57598757683273059381014077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76798343577697412508018769 57598757683273059381014077)
          ·
            refine ⟨21599534131227397267880279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57598757683273059381014077 21599534131227397267880279)
            ·
              refine ⟨32399301196841095901820419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21599534131227397267880279 32399301196841095901820419)
              ·
                refine ⟨48598951795261643852730629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32399301196841095901820419 48598951795261643852730629)
                ·
                  refine ⟨9112303461611558222386993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48598951795261643852730629 9112303461611558222386993)
                  ·
                    refine ⟨6834227596208668666790245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9112303461611558222386993 6834227596208668666790245)
                    ·
                      refine ⟨1281417674289125375023171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6834227596208668666790245 1281417674289125375023171)
                      ·
                        rfl

theorem cell23_2495552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2495552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495552 prefixEnd_2495552 := by exact prefixLift 2495552
  have htrace : WordTrace (prefixWord ++ tailWord_2495552) baseStart_2495552 baseEnd_2495552 := by
    simpa [prefixWord, tailWord_2495552, baseEnd_2495552] using wordTrace_append hprefix tailTrace_2495552
  have hstable : (prefixWord ++ tailWord_2495552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495552).length < 2 ^ (prefixWord ++ tailWord_2495552).sum := by decide
  have hdescent : baseEnd_2495552 < baseStart_2495552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495562 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_2495562 : Nat := 118140960795 + 2495562 * 2 ^ 59
def prefixEnd_2495562 : Nat := 4983230072969 + 3 ^ 40 * 2495562 * 2
def baseEnd_2495562 : Nat := 142380312121741148433125

theorem tailTrace_2495562 : CollatzResearch.WordTrace tailWord_2495562 prefixEnd_2495562 142380312121741148433125 := by
  unfold tailWord_2495562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22755155946253139225638235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60680415856675037935035293 22755155946253139225638235)
  ·
    refine ⟨34132733919379708838457353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22755155946253139225638235 34132733919379708838457353)
    ·
      refine ⟨25599550439534781628843015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34132733919379708838457353 25599550439534781628843015)
      ·
        refine ⟨38399325659302172443264523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25599550439534781628843015 38399325659302172443264523)
        ·
          refine ⟨57598988488953258664896785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38399325659302172443264523 57598988488953258664896785)
          ·
            refine ⟨43199241366714943998672589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57598988488953258664896785 43199241366714943998672589)
            ·
              refine ⟨16199715512518103999502221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43199241366714943998672589 16199715512518103999502221)
              ·
                refine ⟨6074893317194288999813333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16199715512518103999502221 6074893317194288999813333)
                ·
                  refine ⟨142380312121741148433125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6074893317194288999813333 142380312121741148433125)
                  ·
                    rfl

theorem cell23_2495562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_2495562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495562 prefixEnd_2495562 := by exact prefixLift 2495562
  have htrace : WordTrace (prefixWord ++ tailWord_2495562) baseStart_2495562 baseEnd_2495562 := by
    simpa [prefixWord, tailWord_2495562, baseEnd_2495562] using wordTrace_append hprefix tailTrace_2495562
  have hstable : (prefixWord ++ tailWord_2495562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495562).length < 2 ^ (prefixWord ++ tailWord_2495562).sum := by decide
  have hdescent : baseEnd_2495562 < baseStart_2495562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495624 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2495624 : Nat := 118140960795 + 2495624 * 2 ^ 59
def prefixEnd_2495624 : Nat := 4983230072969 + 3 ^ 40 * 2495624 * 2
def baseEnd_2495624 : Nat := 1281454644896249093322841

theorem tailTrace_2495624 : CollatzResearch.WordTrace tailWord_2495624 prefixEnd_2495624 1281454644896249093322841 := by
  unfold tailWord_2495624
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511442555393970745654963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60681923407191960994206617 45511442555393970745654963)
  ·
    refine ⟨68267163833090956118482445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45511442555393970745654963 68267163833090956118482445)
    ·
      refine ⟨25600186437409108544430917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68267163833090956118482445 25600186437409108544430917)
      ·
        refine ⟨4800034957014207852080797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25600186437409108544430917 4800034957014207852080797)
        ·
          refine ⟨1800013108880327944530299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4800034957014207852080797 1800013108880327944530299)
          ·
            refine ⟨2700019663320491916795449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800013108880327944530299 2700019663320491916795449)
            ·
              refine ⟨2025014747490368937596587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700019663320491916795449 2025014747490368937596587)
              ·
                refine ⟨3037522121235553406394881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025014747490368937596587 3037522121235553406394881)
                ·
                  refine ⟨2278141590926665054796161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037522121235553406394881 2278141590926665054796161)
                  ·
                    refine ⟨1708606193194998791097121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278141590926665054796161 1708606193194998791097121)
                    ·
                      refine ⟨1281454644896249093322841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708606193194998791097121 1281454644896249093322841)
                      ·
                        rfl

theorem cell23_2495624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2495624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495624 prefixEnd_2495624 := by exact prefixLift 2495624
  have htrace : WordTrace (prefixWord ++ tailWord_2495624) baseStart_2495624 baseEnd_2495624 := by
    simpa [prefixWord, tailWord_2495624, baseEnd_2495624] using wordTrace_append hprefix tailTrace_2495624
  have hstable : (prefixWord ++ tailWord_2495624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495624).length < 2 ^ (prefixWord ++ tailWord_2495624).sum := by decide
  have hdescent : baseEnd_2495624 < baseStart_2495624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495666 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2495666 : Nat := 118140960795 + 2495666 * 2 ^ 59
def prefixEnd_2495666 : Nat := 4983230072969 + 3 ^ 40 * 2495666 * 2
def baseEnd_2495666 : Nat := 1281476211083737928997647

theorem tailTrace_2495666 : CollatzResearch.WordTrace tailWord_2495666 prefixEnd_2495666 1281476211083737928997647 := by
  unfold tailWord_2495666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22756104244158945666084713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60682944651090521776225901 22756104244158945666084713)
  ·
    refine ⟨17067078183119209249563535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22756104244158945666084713 17067078183119209249563535)
    ·
      refine ⟨25600617274678813874345303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17067078183119209249563535 25600617274678813874345303)
      ·
        refine ⟨38400925912018220811517955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25600617274678813874345303 38400925912018220811517955)
        ·
          refine ⟨57601388868027331217276933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38400925912018220811517955 57601388868027331217276933)
          ·
            refine ⟨10800260412755124603239425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57601388868027331217276933 10800260412755124603239425)
            ·
              refine ⟨8100195309566343452429569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10800260412755124603239425 8100195309566343452429569)
              ·
                refine ⟨6075146482174757589322177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8100195309566343452429569 6075146482174757589322177)
                ·
                  refine ⟨4556359861631068191991633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6075146482174757589322177 4556359861631068191991633)
                  ·
                    refine ⟨3417269896223301143993725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4556359861631068191991633 3417269896223301143993725)
                    ·
                      refine ⟨1281476211083737928997647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417269896223301143993725 1281476211083737928997647)
                      ·
                        rfl

theorem cell23_2495666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2495666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495666 prefixEnd_2495666 := by exact prefixLift 2495666
  have htrace : WordTrace (prefixWord ++ tailWord_2495666) baseStart_2495666 baseEnd_2495666 := by
    simpa [prefixWord, tailWord_2495666, baseEnd_2495666] using wordTrace_append hprefix tailTrace_2495666
  have hstable : (prefixWord ++ tailWord_2495666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495666).length < 2 ^ (prefixWord ++ tailWord_2495666).sum := by decide
  have hdescent : baseEnd_2495666 < baseStart_2495666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495673 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 1, 4]
def baseStart_2495673 : Nat := 118140960795 + 2495673 * 2 ^ 59
def prefixEnd_2495673 : Nat := 4983230072969 + 3 ^ 40 * 2495673 * 2
def baseEnd_2495673 : Nat := 427159935149439800536705

theorem tailTrace_2495673 : CollatzResearch.WordTrace tailWord_2495673 prefixEnd_2495673 427159935149439800536705 := by
  unfold tailWord_2495673
  simp only [CollatzResearch.WordTrace]
  refine ⟨91024672287610422859843673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60683114858406948573229115 91024672287610422859843673)
  ·
    refine ⟨68268504215707817144882755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91024672287610422859843673 68268504215707817144882755)
    ·
      refine ⟨102402756323561725717324133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68268504215707817144882755 102402756323561725717324133)
      ·
        refine ⟨19200516810667823571998275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102402756323561725717324133 19200516810667823571998275)
        ·
          refine ⟨28800775216001735357997413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19200516810667823571998275 28800775216001735357997413)
          ·
            refine ⟨5400145353000325379624515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28800775216001735357997413 5400145353000325379624515)
            ·
              refine ⟨8100218029500488069436773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400145353000325379624515 8100218029500488069436773)
              ·
                refine ⟨1518790880531341513019395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8100218029500488069436773 1518790880531341513019395)
                ·
                  refine ⟨2278186320797012269529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518790880531341513019395 2278186320797012269529093)
                  ·
                    refine ⟨427159935149439800536705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2278186320797012269529093 427159935149439800536705)
                    ·
                      rfl

theorem cell23_2495673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_2495673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495673 prefixEnd_2495673 := by exact prefixLift 2495673
  have htrace : WordTrace (prefixWord ++ tailWord_2495673) baseStart_2495673 baseEnd_2495673 := by
    simpa [prefixWord, tailWord_2495673, baseEnd_2495673] using wordTrace_append hprefix tailTrace_2495673
  have hstable : (prefixWord ++ tailWord_2495673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495673).length < 2 ^ (prefixWord ++ tailWord_2495673).sum := by decide
  have hdescent : baseEnd_2495673 < baseStart_2495673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495730 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2495730 : Nat := 118140960795 + 2495730 * 2 ^ 59
def prefixEnd_2495730 : Nat := 4983230072969 + 3 ^ 40 * 2495730 * 2
def baseEnd_2495730 : Nat := 1281509073845625678597353

theorem tailTrace_2495730 : CollatzResearch.WordTrace tailWord_2495730 prefixEnd_2495730 1281509073845625678597353 := by
  unfold tailWord_2495730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22756687812100980398667161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60684500832269281063112429 22756687812100980398667161)
  ·
    refine ⟨17067515859075735299000371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22756687812100980398667161 17067515859075735299000371)
    ·
      refine ⟨25601273788613602948500557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17067515859075735299000371 25601273788613602948500557)
      ·
        refine ⟨9600477670730101105687709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25601273788613602948500557 9600477670730101105687709)
        ·
          refine ⟨3600179126523787914632891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9600477670730101105687709 3600179126523787914632891)
          ·
            refine ⟨5400268689785681871949337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600179126523787914632891 5400268689785681871949337)
            ·
              refine ⟨4050201517339261403962003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400268689785681871949337 4050201517339261403962003)
              ·
                refine ⟨6075302276008892105943005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050201517339261403962003 6075302276008892105943005)
                ·
                  refine ⟨2278238353503334539728627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6075302276008892105943005 2278238353503334539728627)
                  ·
                    refine ⟨3417357530255001809592941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278238353503334539728627 3417357530255001809592941)
                    ·
                      refine ⟨1281509073845625678597353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417357530255001809592941 1281509073845625678597353)
                      ·
                        rfl

theorem cell23_2495730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2495730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495730 prefixEnd_2495730 := by exact prefixLift 2495730
  have htrace : WordTrace (prefixWord ++ tailWord_2495730) baseStart_2495730 baseEnd_2495730 := by
    simpa [prefixWord, tailWord_2495730, baseEnd_2495730] using wordTrace_append hprefix tailTrace_2495730
  have hstable : (prefixWord ++ tailWord_2495730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495730).length < 2 ^ (prefixWord ++ tailWord_2495730).sum := by decide
  have hdescent : baseEnd_2495730 < baseStart_2495730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495749 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_2495749 : Nat := 118140960795 + 2495749 * 2 ^ 59
def prefixEnd_2495749 : Nat := 4983230072969 + 3 ^ 40 * 2495749 * 2
def baseEnd_2495749 : Nat := 1281518829978061104259765

theorem tailTrace_2495749 : CollatzResearch.WordTrace tailWord_2495749 prefixEnd_2495749 1281518829978061104259765 := by
  unfold tailWord_2495749
  simp only [CollatzResearch.WordTrace]
  refine ⟨91027444235335087839610301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60684962823556725226406867 91027444235335087839610301)
  ·
    refine ⟨34135291588250657939853863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91027444235335087839610301 34135291588250657939853863)
    ·
      refine ⟨51202937382375986909780795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34135291588250657939853863 51202937382375986909780795)
      ·
        refine ⟨76804406073563980364671193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51202937382375986909780795 76804406073563980364671193)
        ·
          refine ⟨57603304555172985273503395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76804406073563980364671193 57603304555172985273503395)
          ·
            refine ⟨86404956832759477910255093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57603304555172985273503395 86404956832759477910255093)
            ·
              refine ⟨8100464703071201054086415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86404956832759477910255093 8100464703071201054086415)
              ·
                refine ⟨12150697054606801581129623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100464703071201054086415 12150697054606801581129623)
                ·
                  refine ⟨18226045581910202371694435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12150697054606801581129623 18226045581910202371694435)
                  ·
                    refine ⟨27339068372865303557541653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18226045581910202371694435 27339068372865303557541653)
                    ·
                      refine ⟨1281518829978061104259765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27339068372865303557541653 1281518829978061104259765)
                      ·
                        rfl

theorem cell23_2495749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_2495749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495749 prefixEnd_2495749 := by exact prefixLift 2495749
  have htrace : WordTrace (prefixWord ++ tailWord_2495749) baseStart_2495749 baseEnd_2495749 := by
    simpa [prefixWord, tailWord_2495749, baseEnd_2495749] using wordTrace_append hprefix tailTrace_2495749
  have hstable : (prefixWord ++ tailWord_2495749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495749).length < 2 ^ (prefixWord ++ tailWord_2495749).sum := by decide
  have hdescent : baseEnd_2495749 < baseStart_2495749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495753 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 3, 2, 2]
def baseStart_2495753 : Nat := 118140960795 + 2495753 * 2 ^ 59
def prefixEnd_2495753 : Nat := 4983230072969 + 3 ^ 40 * 2495753 * 2
def baseEnd_2495753 : Nat := 1281520883900679088609747

theorem tailTrace_2495753 : CollatzResearch.WordTrace tailWord_2495753 prefixEnd_2495753 1281520883900679088609747 := by
  unfold tailWord_2495753
  simp only [CollatzResearch.WordTrace]
  refine ⟨91027590127320596522755913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60685060084880397681837275 91027590127320596522755913)
  ·
    refine ⟨68270692595490447392066935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91027590127320596522755913 68270692595490447392066935)
    ·
      refine ⟨102406038893235671088100403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68270692595490447392066935 102406038893235671088100403)
      ·
        refine ⟨153609058339853506632150605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102406038893235671088100403 153609058339853506632150605)
        ·
          refine ⟨57603396877445064987056477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153609058339853506632150605 57603396877445064987056477)
          ·
            refine ⟨21601273829041899370146179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57603396877445064987056477 21601273829041899370146179)
            ·
              refine ⟨32401910743562849055219269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21601273829041899370146179 32401910743562849055219269)
              ·
                refine ⟨6075358264418034197853613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32401910743562849055219269 6075358264418034197853613)
                ·
                  refine ⟨2278259349156762824195105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6075358264418034197853613 2278259349156762824195105)
                  ·
                    refine ⟨1708694511867572118146329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278259349156762824195105 1708694511867572118146329)
                    ·
                      refine ⟨1281520883900679088609747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708694511867572118146329 1281520883900679088609747)
                      ·
                        rfl

theorem cell23_2495753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2, 2].length) (baseStart_2495753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495753 prefixEnd_2495753 := by exact prefixLift 2495753
  have htrace : WordTrace (prefixWord ++ tailWord_2495753) baseStart_2495753 baseEnd_2495753 := by
    simpa [prefixWord, tailWord_2495753, baseEnd_2495753] using wordTrace_append hprefix tailTrace_2495753
  have hstable : (prefixWord ++ tailWord_2495753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495753).length < 2 ^ (prefixWord ++ tailWord_2495753).sum := by decide
  have hdescent : baseEnd_2495753 < baseStart_2495753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495773 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2495773 : Nat := 118140960795 + 2495773 * 2 ^ 59
def prefixEnd_2495773 : Nat := 4983230072969 + 3 ^ 40 * 2495773 * 2
def baseEnd_2495773 : Nat := 1281531153513769010359655

theorem tailTrace_2495773 : CollatzResearch.WordTrace tailWord_2495773 prefixEnd_2495773 1281531153513769010359655 := by
  unfold tailWord_2495773
  simp only [CollatzResearch.WordTrace]
  refine ⟨91028319587248139938483973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60685546391498759958989315 91028319587248139938483973)
  ·
    refine ⟨17067809922609026238465745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91028319587248139938483973 17067809922609026238465745)
    ·
      refine ⟨12800857441956769678849309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17067809922609026238465745 12800857441956769678849309)
      ·
        refine ⟨4800321540733788629568491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12800857441956769678849309 4800321540733788629568491)
        ·
          refine ⟨7200482311100682944352737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800321540733788629568491 7200482311100682944352737)
          ·
            refine ⟨5400361733325512208264553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7200482311100682944352737 5400361733325512208264553)
            ·
              refine ⟨4050271299994134156198415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400361733325512208264553 4050271299994134156198415)
              ·
                refine ⟨6075406949991201234297623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050271299994134156198415 6075406949991201234297623)
                ·
                  refine ⟨9113110424986801851446435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6075406949991201234297623 9113110424986801851446435)
                  ·
                    refine ⟨13669665637480202777169653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9113110424986801851446435 13669665637480202777169653)
                    ·
                      refine ⟨1281531153513769010359655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13669665637480202777169653 1281531153513769010359655)
                      ·
                        rfl

theorem cell23_2495773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2495773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495773 prefixEnd_2495773 := by exact prefixLift 2495773
  have htrace : WordTrace (prefixWord ++ tailWord_2495773) baseStart_2495773 baseEnd_2495773 := by
    simpa [prefixWord, tailWord_2495773, baseEnd_2495773] using wordTrace_append hprefix tailTrace_2495773
  have hstable : (prefixWord ++ tailWord_2495773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495773).length < 2 ^ (prefixWord ++ tailWord_2495773).sum := by decide
  have hdescent : baseEnd_2495773 < baseStart_2495773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495776 : List Nat := [2, 1, 1, 5, 3, 2, 9]
def baseStart_2495776 : Nat := 118140960795 + 2495776 * 2 ^ 59
def prefixEnd_2495776 : Nat := 4983230072969 + 3 ^ 40 * 2495776 * 2
def baseEnd_2495776 : Nat := 15821391283404104921261

theorem tailTrace_2495776 : CollatzResearch.WordTrace tailWord_2495776 prefixEnd_2495776 15821391283404104921261 := by
  unfold tailWord_2495776
  simp only [CollatzResearch.WordTrace]
  refine ⟨45514214503118635725421591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60685619337491514300562121 45514214503118635725421591)
  ·
    refine ⟨68271321754677953588132387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45514214503118635725421591 68271321754677953588132387)
    ·
      refine ⟨102406982632016930382198581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68271321754677953588132387 102406982632016930382198581)
      ·
        refine ⟨9600654621751587223331117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102406982632016930382198581 9600654621751587223331117)
        ·
          refine ⟨3600245483156845208749169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9600654621751587223331117 3600245483156845208749169)
          ·
            refine ⟨2700184112367633906561877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600245483156845208749169 2700184112367633906561877)
            ·
              refine ⟨15821391283404104921261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2700184112367633906561877 15821391283404104921261)
              ·
                rfl

theorem cell23_2495776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 9].length) (baseStart_2495776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495776 prefixEnd_2495776 := by exact prefixLift 2495776
  have htrace : WordTrace (prefixWord ++ tailWord_2495776) baseStart_2495776 baseEnd_2495776 := by
    simpa [prefixWord, tailWord_2495776, baseEnd_2495776] using wordTrace_append hprefix tailTrace_2495776
  have hstable : (prefixWord ++ tailWord_2495776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495776).length < 2 ^ (prefixWord ++ tailWord_2495776).sum := by decide
  have hdescent : baseEnd_2495776 < baseStart_2495776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495796 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2495796 : Nat := 118140960795 + 2495796 * 2 ^ 59
def prefixEnd_2495796 : Nat := 4983230072969 + 3 ^ 40 * 2495796 * 2
def baseEnd_2495796 : Nat := 1281542963568822420372049

theorem tailTrace_2495796 : CollatzResearch.WordTrace tailWord_2495796 prefixEnd_2495796 1281542963568822420372049 := by
  unfold tailWord_2495796
  simp only [CollatzResearch.WordTrace]
  refine ⟨45514579233082407433285621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60686105644109876577714161 45514579233082407433285621)
  ·
    refine ⟨4266991803101475696870527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45514579233082407433285621 4266991803101475696870527)
    ·
      refine ⟨6400487704652213545305791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4266991803101475696870527 6400487704652213545305791)
      ·
        refine ⟨9600731556978320317958687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6400487704652213545305791 9600731556978320317958687)
        ·
          refine ⟨14401097335467480476938031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9600731556978320317958687 14401097335467480476938031)
          ·
            refine ⟨21601646003201220715407047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14401097335467480476938031 21601646003201220715407047)
            ·
              refine ⟨32402469004801831073110571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21601646003201220715407047 32402469004801831073110571)
              ·
                refine ⟨48603703507202746609665857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32402469004801831073110571 48603703507202746609665857)
                ·
                  refine ⟨36452777630402059957249393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48603703507202746609665857 36452777630402059957249393)
                  ·
                    refine ⟨27339583222801544967937045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36452777630402059957249393 27339583222801544967937045)
                    ·
                      refine ⟨1281542963568822420372049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27339583222801544967937045 1281542963568822420372049)
                      ·
                        rfl

theorem cell23_2495796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2495796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495796 prefixEnd_2495796 := by exact prefixLift 2495796
  have htrace : WordTrace (prefixWord ++ tailWord_2495796) baseStart_2495796 baseEnd_2495796 := by
    simpa [prefixWord, tailWord_2495796, baseEnd_2495796] using wordTrace_append hprefix tailTrace_2495796
  have hstable : (prefixWord ++ tailWord_2495796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495796).length < 2 ^ (prefixWord ++ tailWord_2495796).sum := by decide
  have hdescent : baseEnd_2495796 < baseStart_2495796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495839 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_2495839 : Nat := 118140960795 + 2495839 * 2 ^ 59
def prefixEnd_2495839 : Nat := 4983230072969 + 3 ^ 40 * 2495839 * 2
def baseEnd_2495839 : Nat := 1281565043236965752134351

theorem tailTrace_2495839 : CollatzResearch.WordTrace tailWord_2495839 prefixEnd_2495839 1281565043236965752134351 := by
  unfold tailWord_2495839
  simp only [CollatzResearch.WordTrace]
  refine ⟨91030726805009033210386571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60687151203339355473591047 91030726805009033210386571)
  ·
    refine ⟨136546090207513549815579857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91030726805009033210386571 136546090207513549815579857)
    ·
      refine ⟨102409567655635162361684893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136546090207513549815579857 102409567655635162361684893)
      ·
        refine ⟨38403587870863185885631835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102409567655635162361684893 38403587870863185885631835)
        ·
          refine ⟨57605381806294778828447753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38403587870863185885631835 57605381806294778828447753)
          ·
            refine ⟨43204036354721084121335815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57605381806294778828447753 43204036354721084121335815)
            ·
              refine ⟨64806054532081626182003723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43204036354721084121335815 64806054532081626182003723)
              ·
                refine ⟨97209081798122439273005585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64806054532081626182003723 97209081798122439273005585)
                ·
                  refine ⟨72906811348591829454754189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97209081798122439273005585 72906811348591829454754189)
                  ·
                    refine ⟨27340054255721936045532821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72906811348591829454754189 27340054255721936045532821)
                    ·
                      refine ⟨1281565043236965752134351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27340054255721936045532821 1281565043236965752134351)
                      ·
                        rfl

theorem cell23_2495839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_2495839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495839 prefixEnd_2495839 := by exact prefixLift 2495839
  have htrace : WordTrace (prefixWord ++ tailWord_2495839) baseStart_2495839 baseEnd_2495839 := by
    simpa [prefixWord, tailWord_2495839, baseEnd_2495839] using wordTrace_append hprefix tailTrace_2495839
  have hstable : (prefixWord ++ tailWord_2495839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495839).length < 2 ^ (prefixWord ++ tailWord_2495839).sum := by decide
  have hdescent : baseEnd_2495839 < baseStart_2495839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495856 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_2495856 : Nat := 118140960795 + 2495856 * 2 ^ 59
def prefixEnd_2495856 : Nat := 4983230072969 + 3 ^ 40 * 2495856 * 2
def baseEnd_2495856 : Nat := 1281573772408092185621773

theorem tailTrace_2495856 : CollatzResearch.WordTrace tailWord_2495856 prefixEnd_2495856 1281573772408092185621773 := by
  unfold tailWord_2495856
  simp only [CollatzResearch.WordTrace]
  refine ⟨45515673422973722556877711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60687564563964963409170281 45515673422973722556877711)
  ·
    refine ⟨68273510134460583835316567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45515673422973722556877711 68273510134460583835316567)
    ·
      refine ⟨102410265201690875752974851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68273510134460583835316567 102410265201690875752974851)
      ·
        refine ⟨153615397802536313629462277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102410265201690875752974851 153615397802536313629462277)
        ·
          refine ⟨28802887087975558805524177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153615397802536313629462277 28802887087975558805524177)
          ·
            refine ⟨21602165315981669104143133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28802887087975558805524177 21602165315981669104143133)
            ·
              refine ⟨8100811993493125914053675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21602165315981669104143133 8100811993493125914053675)
              ·
                refine ⟨12151217990239688871080513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100811993493125914053675 12151217990239688871080513)
                ·
                  refine ⟨9113413492679766653310385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12151217990239688871080513 9113413492679766653310385)
                  ·
                    refine ⟨6835060119509824989982789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9113413492679766653310385 6835060119509824989982789)
                    ·
                      refine ⟨1281573772408092185621773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6835060119509824989982789 1281573772408092185621773)
                      ·
                        rfl

theorem cell23_2495856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_2495856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495856 prefixEnd_2495856 := by exact prefixLift 2495856
  have htrace : WordTrace (prefixWord ++ tailWord_2495856) baseStart_2495856 baseEnd_2495856 := by
    simpa [prefixWord, tailWord_2495856, baseEnd_2495856] using wordTrace_append hprefix tailTrace_2495856
  have hstable : (prefixWord ++ tailWord_2495856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495856).length < 2 ^ (prefixWord ++ tailWord_2495856).sum := by decide
  have hdescent : baseEnd_2495856 < baseStart_2495856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495883 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 5]
def baseStart_2495883 : Nat := 118140960795 + 2495883 * 2 ^ 59
def prefixEnd_2495883 : Nat := 4983230072969 + 3 ^ 40 * 2495883 * 2
def baseEnd_2495883 : Nat := 142398626265084842220461

theorem tailTrace_2495883 : CollatzResearch.WordTrace tailWord_2495883 prefixEnd_2495883 142398626265084842220461 := by
  unfold tailWord_2495883
  simp only [CollatzResearch.WordTrace]
  refine ⟨91032331616849628724988303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60688221077899752483325535 91032331616849628724988303)
  ·
    refine ⟨136548497425274443087482455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91032331616849628724988303 136548497425274443087482455)
    ·
      refine ⟨204822746137911664631223683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136548497425274443087482455 204822746137911664631223683)
      ·
        refine ⟨307234119206867496946835525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204822746137911664631223683 307234119206867496946835525)
        ·
          refine ⟨57606397351287655677531661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307234119206867496946835525 57606397351287655677531661)
          ·
            refine ⟨21602399006732870879074373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57606397351287655677531661 21602399006732870879074373)
            ·
              refine ⟨4050449813762413289826445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21602399006732870879074373 4050449813762413289826445)
              ·
                refine ⟨1518918680160904983684917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4050449813762413289826445 1518918680160904983684917)
                ·
                  refine ⟨142398626265084842220461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518918680160904983684917 142398626265084842220461)
                  ·
                    rfl

theorem cell23_2495883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 5].length) (baseStart_2495883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495883 prefixEnd_2495883 := by exact prefixLift 2495883
  have htrace : WordTrace (prefixWord ++ tailWord_2495883) baseStart_2495883 baseEnd_2495883 := by
    simpa [prefixWord, tailWord_2495883, baseEnd_2495883] using wordTrace_append hprefix tailTrace_2495883
  have hstable : (prefixWord ++ tailWord_2495883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495883).length < 2 ^ (prefixWord ++ tailWord_2495883).sum := by decide
  have hdescent : baseEnd_2495883 < baseStart_2495883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495900 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 7]
def baseStart_2495900 : Nat := 118140960795 + 2495900 * 2 ^ 59
def prefixEnd_2495900 : Nat := 4983230072969 + 3 ^ 40 * 2495900 * 2
def baseEnd_2495900 : Nat := 142399596172987779274619

theorem tailTrace_2495900 : CollatzResearch.WordTrace tailWord_2495900 prefixEnd_2495900 142399596172987779274619 := by
  unfold tailWord_2495900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45516475828894020314178577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60688634438525360418904769 45516475828894020314178577)
  ·
    refine ⟨34137356871670515235633933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45516475828894020314178577 34137356871670515235633933)
    ·
      refine ⟨12801508826876443213362725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34137356871670515235633933 12801508826876443213362725)
      ·
        refine ⟨2400282905039333102505511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12801508826876443213362725 2400282905039333102505511)
        ·
          refine ⟨3600424357558999653758267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400282905039333102505511 3600424357558999653758267)
          ·
            refine ⟨5400636536338499480637401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600424357558999653758267 5400636536338499480637401)
            ·
              refine ⟨4050477402253874610478051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400636536338499480637401 4050477402253874610478051)
              ·
                refine ⟨6075716103380811915717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050477402253874610478051 6075716103380811915717077)
                ·
                  refine ⟨142399596172987779274619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6075716103380811915717077 142399596172987779274619)
                  ·
                    rfl

theorem cell23_2495900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_2495900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495900 prefixEnd_2495900 := by exact prefixLift 2495900
  have htrace : WordTrace (prefixWord ++ tailWord_2495900) baseStart_2495900 baseEnd_2495900 := by
    simpa [prefixWord, tailWord_2495900, baseEnd_2495900] using wordTrace_append hprefix tailTrace_2495900
  have hstable : (prefixWord ++ tailWord_2495900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495900).length < 2 ^ (prefixWord ++ tailWord_2495900).sum := by decide
  have hdescent : baseEnd_2495900 < baseStart_2495900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495916 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2495916 : Nat := 118140960795 + 2495916 * 2 ^ 59
def prefixEnd_2495916 : Nat := 4983230072969 + 3 ^ 40 * 2495916 * 2
def baseEnd_2495916 : Nat := 1281604581247361950871497

theorem tailTrace_2495916 : CollatzResearch.WordTrace tailWord_2495916 prefixEnd_2495916 1281604581247361950871497 := by
  unfold tailWord_2495916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45516767612865037680469801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60689023483820050240626401 45516767612865037680469801)
  ·
    refine ⟨34137575709648778260352351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45516767612865037680469801 34137575709648778260352351)
    ·
      refine ⟨51206363564473167390528527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34137575709648778260352351 51206363564473167390528527)
      ·
        refine ⟨76809545346709751085792791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51206363564473167390528527 76809545346709751085792791)
        ·
          refine ⟨115214318020064626628689187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76809545346709751085792791 115214318020064626628689187)
          ·
            refine ⟨172821477030096939943033781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115214318020064626628689187 172821477030096939943033781)
            ·
              refine ⟨16202013471571588119659417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172821477030096939943033781 16202013471571588119659417)
              ·
                refine ⟨12151510103678691089744563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16202013471571588119659417 12151510103678691089744563)
                ·
                  refine ⟨18227265155518036634616845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12151510103678691089744563 18227265155518036634616845)
                  ·
                    refine ⟨6835224433319263737981317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18227265155518036634616845 6835224433319263737981317)
                    ·
                      refine ⟨1281604581247361950871497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6835224433319263737981317 1281604581247361950871497)
                      ·
                        rfl

theorem cell23_2495916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2495916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495916 prefixEnd_2495916 := by exact prefixLift 2495916
  have htrace : WordTrace (prefixWord ++ tailWord_2495916) baseStart_2495916 baseEnd_2495916 := by
    simpa [prefixWord, tailWord_2495916, baseEnd_2495916] using wordTrace_append hprefix tailTrace_2495916
  have hstable : (prefixWord ++ tailWord_2495916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495916).length < 2 ^ (prefixWord ++ tailWord_2495916).sum := by decide
  have hdescent : baseEnd_2495916 < baseStart_2495916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495933 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2495933 : Nat := 118140960795 + 2495933 * 2 ^ 59
def prefixEnd_2495933 : Nat := 4983230072969 + 3 ^ 40 * 2495933 * 2
def baseEnd_2495933 : Nat := 1281613310418488384358919

theorem tailTrace_2495933 : CollatzResearch.WordTrace tailWord_2495933 prefixEnd_2495933 1281613310418488384358919 := by
  unfold tailWord_2495933
  simp only [CollatzResearch.WordTrace]
  refine ⟨91034155266668487264308453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60689436844445658176205635 91034155266668487264308453)
  ·
    refine ⟨17068904112500341362057835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91034155266668487264308453 17068904112500341362057835)
    ·
      refine ⟨25603356168750512043086753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17068904112500341362057835 25603356168750512043086753)
      ·
        refine ⟨19202517126562884032315065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25603356168750512043086753 19202517126562884032315065)
        ·
          refine ⟨14401887844922163024236299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19202517126562884032315065 14401887844922163024236299)
          ·
            refine ⟨21602831767383244536354449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14401887844922163024236299 21602831767383244536354449)
            ·
              refine ⟨16202123825537433402265837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21602831767383244536354449 16202123825537433402265837)
              ·
                refine ⟨6075796434576537525849689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16202123825537433402265837 6075796434576537525849689)
                ·
                  refine ⟨4556847325932403144387267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6075796434576537525849689 4556847325932403144387267)
                  ·
                    refine ⟨6835270988898604716580901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4556847325932403144387267 6835270988898604716580901)
                    ·
                      refine ⟨1281613310418488384358919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6835270988898604716580901 1281613310418488384358919)
                      ·
                        rfl

theorem cell23_2495933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2495933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495933 prefixEnd_2495933 := by exact prefixLift 2495933
  have htrace : WordTrace (prefixWord ++ tailWord_2495933) baseStart_2495933 baseEnd_2495933 := by
    simpa [prefixWord, tailWord_2495933, baseEnd_2495933] using wordTrace_append hprefix tailTrace_2495933
  have hstable : (prefixWord ++ tailWord_2495933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495933).length < 2 ^ (prefixWord ++ tailWord_2495933).sum := by decide
  have hdescent : baseEnd_2495933 < baseStart_2495933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495960 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 1, 4]
def baseStart_2495960 : Nat := 118140960795 + 2495960 * 2 ^ 59
def prefixEnd_2495960 : Nat := 4983230072969 + 3 ^ 40 * 2495960 * 2
def baseEnd_2495960 : Nat := 427209058132053259573765

theorem tailTrace_2495960 : CollatzResearch.WordTrace tailWord_2495960 prefixEnd_2495960 427209058132053259573765 := by
  unfold tailWord_2495960
  simp only [CollatzResearch.WordTrace]
  refine ⟨45517570018785335437770667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60690093358380447250360889 45517570018785335437770667)
  ·
    refine ⟨68276355028178003156656001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45517570018785335437770667 68276355028178003156656001)
    ·
      refine ⟨51207266271133502367492001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68276355028178003156656001 51207266271133502367492001)
      ·
        refine ⟨38405449703350126775619001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51207266271133502367492001 38405449703350126775619001)
        ·
          refine ⟨28804087277512595081714251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38405449703350126775619001 28804087277512595081714251)
          ·
            refine ⟨43206130916268892622571377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28804087277512595081714251 43206130916268892622571377)
            ·
              refine ⟨32404598187201669466928533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43206130916268892622571377 32404598187201669466928533)
              ·
                refine ⟨1518965540025078256262275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32404598187201669466928533 1518965540025078256262275)
                ·
                  refine ⟨2278448310037617384393413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518965540025078256262275 2278448310037617384393413)
                  ·
                    refine ⟨427209058132053259573765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2278448310037617384393413 427209058132053259573765)
                    ·
                      rfl

theorem cell23_2495960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_2495960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2495960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2495960 prefixEnd_2495960 := by exact prefixLift 2495960
  have htrace : WordTrace (prefixWord ++ tailWord_2495960) baseStart_2495960 baseEnd_2495960 := by
    simpa [prefixWord, tailWord_2495960, baseEnd_2495960] using wordTrace_append hprefix tailTrace_2495960
  have hstable : (prefixWord ++ tailWord_2495960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495960).length < 2 ^ (prefixWord ++ tailWord_2495960).sum := by decide
  have hdescent : baseEnd_2495960 < baseStart_2495960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496011 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 1, 4]
def baseStart_2496011 : Nat := 118140960795 + 2496011 * 2 ^ 59
def prefixEnd_2496011 : Nat := 4983230072969 + 3 ^ 40 * 2496011 * 2
def baseEnd_2496011 : Nat := 427217787303179693061187

theorem tailTrace_2496011 : CollatzResearch.WordTrace tailWord_2496011 prefixEnd_2496011 427217787303179693061187 := by
  unfold tailWord_2496011
  simp only [CollatzResearch.WordTrace]
  refine ⟨91037000160385906585647887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60691333440257271057098591 91037000160385906585647887)
  ·
    refine ⟨136555500240578859878471831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91037000160385906585647887 136555500240578859878471831)
    ·
      refine ⟨204833250360868289817707747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136555500240578859878471831 204833250360868289817707747)
      ·
        refine ⟨307249875541302434726561621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204833250360868289817707747 307249875541302434726561621)
        ·
          refine ⟨1800292239499818953475947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 307249875541302434726561621 1800292239499818953475947)
          ·
            refine ⟨2700438359249728430213921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800292239499818953475947 2700438359249728430213921)
            ·
              refine ⟨2025328769437296322660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700438359249728430213921 2025328769437296322660441)
              ·
                refine ⟨1518996577077972241995331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025328769437296322660441 1518996577077972241995331)
                ·
                  refine ⟨2278494865616958362992997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518996577077972241995331 2278494865616958362992997)
                  ·
                    refine ⟨427217787303179693061187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2278494865616958362992997 427217787303179693061187)
                    ·
                      rfl

theorem cell23_2496011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 4].length) (baseStart_2496011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496011 prefixEnd_2496011 := by exact prefixLift 2496011
  have htrace : WordTrace (prefixWord ++ tailWord_2496011) baseStart_2496011 baseEnd_2496011 := by
    simpa [prefixWord, tailWord_2496011, baseEnd_2496011] using wordTrace_append hprefix tailTrace_2496011
  have hstable : (prefixWord ++ tailWord_2496011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496011).length < 2 ^ (prefixWord ++ tailWord_2496011).sum := by decide
  have hdescent : baseEnd_2496011 < baseStart_2496011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496017 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_2496017 : Nat := 118140960795 + 2496017 * 2 ^ 59
def prefixEnd_2496017 : Nat := 4983230072969 + 3 ^ 40 * 2496017 * 2
def baseEnd_2496017 : Nat := 1281656442793466055708533

theorem tailTrace_2496017 : CollatzResearch.WordTrace tailWord_2496017 prefixEnd_2496017 1281656442793466055708533 := by
  unfold tailWord_2496017
  simp only [CollatzResearch.WordTrace]
  refine ⟨91037218998364169610366305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60691479332242779740244203 91037218998364169610366305)
  ·
    refine ⟨68277914248773127207774729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91037218998364169610366305 68277914248773127207774729)
    ·
      refine ⟨51208435686579845405831047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68277914248773127207774729 51208435686579845405831047)
      ·
        refine ⟨76812653529869768108746571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51208435686579845405831047 76812653529869768108746571)
        ·
          refine ⟨115218980294804652163119857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76812653529869768108746571 115218980294804652163119857)
          ·
            refine ⟨86414235221103489122339893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115218980294804652163119857 86414235221103489122339893)
            ·
              refine ⟨8101334551978452105219365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86414235221103489122339893 8101334551978452105219365)
              ·
                refine ⟨1519000228495959769728631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8101334551978452105219365 1519000228495959769728631)
                ·
                  refine ⟨2278500342743939654592947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519000228495959769728631 2278500342743939654592947)
                  ·
                    refine ⟨3417750514115909481889421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278500342743939654592947 3417750514115909481889421)
                    ·
                      refine ⟨1281656442793466055708533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417750514115909481889421 1281656442793466055708533)
                      ·
                        rfl

theorem cell23_2496017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_2496017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496017 prefixEnd_2496017 := by exact prefixLift 2496017
  have htrace : WordTrace (prefixWord ++ tailWord_2496017) baseStart_2496017 baseEnd_2496017 := by
    simpa [prefixWord, tailWord_2496017, baseEnd_2496017] using wordTrace_append hprefix tailTrace_2496017
  have hstable : (prefixWord ++ tailWord_2496017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496017).length < 2 ^ (prefixWord ++ tailWord_2496017).sum := by decide
  have hdescent : baseEnd_2496017 < baseStart_2496017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496033 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_2496033 : Nat := 118140960795 + 2496033 * 2 ^ 59
def prefixEnd_2496033 : Nat := 4983230072969 + 3 ^ 40 * 2496033 * 2
def baseEnd_2496033 : Nat := 427221552827979331036153

theorem tailTrace_2496033 : CollatzResearch.WordTrace tailWord_2496033 prefixEnd_2496033 427221552827979331036153 := by
  unfold tailWord_2496033
  simp only [CollatzResearch.WordTrace]
  refine ⟨91037802566306204342948753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60691868377537469561965835 91037802566306204342948753)
  ·
    refine ⟨68278351924729653257211565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91037802566306204342948753 68278351924729653257211565)
    ·
      refine ⟨25604381971773619971454337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68278351924729653257211565 25604381971773619971454337)
      ·
        refine ⟨19203286478830214978590753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25604381971773619971454337 19203286478830214978590753)
        ·
          refine ⟨14402464859122661233943065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19203286478830214978590753 14402464859122661233943065)
          ·
            refine ⟨10801848644341995925457299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14402464859122661233943065 10801848644341995925457299)
            ·
              refine ⟨16202772966512993888185949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10801848644341995925457299 16202772966512993888185949)
              ·
                refine ⟨6076039862442372708069731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16202772966512993888185949 6076039862442372708069731)
                ·
                  refine ⟨9114059793663559062104597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6076039862442372708069731 9114059793663559062104597)
                  ·
                    refine ⟨427221552827979331036153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9114059793663559062104597 427221552827979331036153)
                    ·
                      rfl

theorem cell23_2496033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_2496033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496033 prefixEnd_2496033 := by exact prefixLift 2496033
  have htrace : WordTrace (prefixWord ++ tailWord_2496033) baseStart_2496033 baseEnd_2496033 := by
    simpa [prefixWord, tailWord_2496033, baseEnd_2496033] using wordTrace_append hprefix tailTrace_2496033
  have hstable : (prefixWord ++ tailWord_2496033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496033).length < 2 ^ (prefixWord ++ tailWord_2496033).sum := by decide
  have hdescent : baseEnd_2496033 < baseStart_2496033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496057 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2496057 : Nat := 118140960795 + 2496057 * 2 ^ 59
def prefixEnd_2496057 : Nat := 4983230072969 + 3 ^ 40 * 2496057 * 2
def baseEnd_2496057 : Nat := 1281676982019645899208349

theorem tailTrace_2496057 : CollatzResearch.WordTrace tailWord_2496057 prefixEnd_2496057 1281676982019645899208349 := by
  unfold tailWord_2496057
  simp only [CollatzResearch.WordTrace]
  refine ⟨91038677918219256441822425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60692451945479504294548283 91038677918219256441822425)
  ·
    refine ⟨68279008438664442331366819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91038677918219256441822425 68279008438664442331366819)
    ·
      refine ⟨102418512657996663497050229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68279008438664442331366819 102418512657996663497050229)
      ·
        refine ⟨9601735561687187202848459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102418512657996663497050229 9601735561687187202848459)
        ·
          refine ⟨14402603342530780804272689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9601735561687187202848459 14402603342530780804272689)
          ·
            refine ⟨10801952506898085603204517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14402603342530780804272689 10801952506898085603204517)
            ·
              refine ⟨2025366095043391050600847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10801952506898085603204517 2025366095043391050600847)
              ·
                refine ⟨3038049142565086575901271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025366095043391050600847 3038049142565086575901271)
                ·
                  refine ⟨4557073713847629863851907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038049142565086575901271 4557073713847629863851907)
                  ·
                    refine ⟨6835610570771444795777861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557073713847629863851907 6835610570771444795777861)
                    ·
                      refine ⟨1281676982019645899208349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6835610570771444795777861 1281676982019645899208349)
                      ·
                        rfl

theorem cell23_2496057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2496057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496057 prefixEnd_2496057 := by exact prefixLift 2496057
  have htrace : WordTrace (prefixWord ++ tailWord_2496057) baseStart_2496057 baseEnd_2496057 := by
    simpa [prefixWord, tailWord_2496057, baseEnd_2496057] using wordTrace_append hprefix tailTrace_2496057
  have hstable : (prefixWord ++ tailWord_2496057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496057).length < 2 ^ (prefixWord ++ tailWord_2496057).sum := by decide
  have hdescent : baseEnd_2496057 < baseStart_2496057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496073 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_2496073 : Nat := 118140960795 + 2496073 * 2 ^ 59
def prefixEnd_2496073 : Nat := 4983230072969 + 3 ^ 40 * 2496073 * 2
def baseEnd_2496073 : Nat := 1281685197710117836608275

theorem tailTrace_2496073 : CollatzResearch.WordTrace tailWord_2496073 prefixEnd_2496073 1281685197710117836608275 := by
  unfold tailWord_2496073
  simp only [CollatzResearch.WordTrace]
  refine ⟨91039261486161291174404873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60692840990774194116269915 91039261486161291174404873)
  ·
    refine ⟨68279446114620968380803655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91039261486161291174404873 68279446114620968380803655)
    ·
      refine ⟨102419169171931452571205483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68279446114620968380803655 102419169171931452571205483)
      ·
        refine ⟨153628753757897178856808225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102419169171931452571205483 153628753757897178856808225)
        ·
          refine ⟨115221565318422884142606169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153628753757897178856808225 115221565318422884142606169)
          ·
            refine ⟨86416173988817163106954627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115221565318422884142606169 86416173988817163106954627)
            ·
              refine ⟨129624260983225744660431941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86416173988817163106954627 129624260983225744660431941)
              ·
                refine ⟨24304548934354827123830989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129624260983225744660431941 24304548934354827123830989)
                ·
                  refine ⟨9114205850383060171436621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24304548934354827123830989 9114205850383060171436621)
                  ·
                    refine ⟨3417827193893647564288733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9114205850383060171436621 3417827193893647564288733)
                    ·
                      refine ⟨1281685197710117836608275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3417827193893647564288733 1281685197710117836608275)
                      ·
                        rfl

theorem cell23_2496073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_2496073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496073 prefixEnd_2496073 := by exact prefixLift 2496073
  have htrace : WordTrace (prefixWord ++ tailWord_2496073) baseStart_2496073 baseEnd_2496073 := by
    simpa [prefixWord, tailWord_2496073, baseEnd_2496073] using wordTrace_append hprefix tailTrace_2496073
  have hstable : (prefixWord ++ tailWord_2496073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496073).length < 2 ^ (prefixWord ++ tailWord_2496073).sum := by decide
  have hdescent : baseEnd_2496073 < baseStart_2496073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496074 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_2496074 : Nat := 118140960795 + 2496074 * 2 ^ 59
def prefixEnd_2496074 : Nat := 4983230072969 + 3 ^ 40 * 2496074 * 2
def baseEnd_2496074 : Nat := 1281685711190772332695771

theorem tailTrace_2496074 : CollatzResearch.WordTrace tailWord_2496074 prefixEnd_2496074 1281685711190772332695771 := by
  unfold tailWord_2496074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759824489789417086297819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60692865306105112230127517 22759824489789417086297819)
  ·
    refine ⟨34139736734684125629446729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759824489789417086297819 34139736734684125629446729)
    ·
      refine ⟨25604802551013094222085047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34139736734684125629446729 25604802551013094222085047)
      ·
        refine ⟨38407203826519641333127571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25604802551013094222085047 38407203826519641333127571)
        ·
          refine ⟨57610805739779461999691357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38407203826519641333127571 57610805739779461999691357)
          ·
            refine ⟨21604052152417298249884259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57610805739779461999691357 21604052152417298249884259)
            ·
              refine ⟨32406078228625947374826389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21604052152417298249884259 32406078228625947374826389)
              ·
                refine ⟨1519034916966841283194987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32406078228625947374826389 1519034916966841283194987)
                ·
                  refine ⟨2278552375450261924792481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519034916966841283194987 2278552375450261924792481)
                  ·
                    refine ⟨1708914281587696443594361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278552375450261924792481 1708914281587696443594361)
                    ·
                      refine ⟨1281685711190772332695771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708914281587696443594361 1281685711190772332695771)
                      ·
                        rfl

theorem cell23_2496074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_2496074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496074 prefixEnd_2496074 := by exact prefixLift 2496074
  have htrace : WordTrace (prefixWord ++ tailWord_2496074) baseStart_2496074 baseEnd_2496074 := by
    simpa [prefixWord, tailWord_2496074, baseEnd_2496074] using wordTrace_append hprefix tailTrace_2496074
  have hstable : (prefixWord ++ tailWord_2496074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496074).length < 2 ^ (prefixWord ++ tailWord_2496074).sum := by decide
  have hdescent : baseEnd_2496074 < baseStart_2496074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496077 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_2496077 : Nat := 118140960795 + 2496077 * 2 ^ 59
def prefixEnd_2496077 : Nat := 4983230072969 + 3 ^ 40 * 2496077 * 2
def baseEnd_2496077 : Nat := 1281687251632735820958257

theorem tailTrace_2496077 : CollatzResearch.WordTrace tailWord_2496077 prefixEnd_2496077 1281687251632735820958257 := by
  unfold tailWord_2496077
  simp only [CollatzResearch.WordTrace]
  refine ⟨91039407378146799857550485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60692938252097866571700323 91039407378146799857550485)
  ·
    refine ⟨4267472220850631243322679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91039407378146799857550485 4267472220850631243322679)
    ·
      refine ⟨6401208331275946864984019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267472220850631243322679 6401208331275946864984019)
      ·
        refine ⟨9601812496913920297476029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401208331275946864984019 9601812496913920297476029)
        ·
          refine ⟨3600679686342720111553511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9601812496913920297476029 3600679686342720111553511)
          ·
            refine ⟨5401019529514080167330267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600679686342720111553511 5401019529514080167330267)
            ·
              refine ⟨8101529294271120250995401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401019529514080167330267 8101529294271120250995401)
              ·
                refine ⟨6076146970703340188246551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8101529294271120250995401 6076146970703340188246551)
                ·
                  refine ⟨9114220456055010282369827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6076146970703340188246551 9114220456055010282369827)
                  ·
                    refine ⟨13671330684082515423554741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9114220456055010282369827 13671330684082515423554741)
                    ·
                      refine ⟨1281687251632735820958257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13671330684082515423554741 1281687251632735820958257)
                      ·
                        rfl

theorem cell23_2496077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_2496077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496077 prefixEnd_2496077 := by exact prefixLift 2496077
  have htrace : WordTrace (prefixWord ++ tailWord_2496077) baseStart_2496077 baseEnd_2496077 := by
    simpa [prefixWord, tailWord_2496077, baseEnd_2496077] using wordTrace_append hprefix tailTrace_2496077
  have hstable : (prefixWord ++ tailWord_2496077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496077).length < 2 ^ (prefixWord ++ tailWord_2496077).sum := by decide
  have hdescent : baseEnd_2496077 < baseStart_2496077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496103 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2496103 : Nat := 118140960795 + 2496103 * 2 ^ 59
def prefixEnd_2496103 : Nat := 4983230072969 + 3 ^ 40 * 2496103 * 2
def baseEnd_2496103 : Nat := 1281700602129752719233137

theorem tailTrace_2496103 : CollatzResearch.WordTrace tailWord_2496103 prefixEnd_2496103 1281700602129752719233137 := by
  unfold tailWord_2496103
  simp only [CollatzResearch.WordTrace]
  refine ⟨91040355676052606297996963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60693570450701737531997975 91040355676052606297996963)
  ·
    refine ⟨136560533514078909446995445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91040355676052606297996963 136560533514078909446995445)
    ·
      refine ⟨12802550016944897760655823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136560533514078909446995445 12802550016944897760655823)
      ·
        refine ⟨19203825025417346640983735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12802550016944897760655823 19203825025417346640983735)
        ·
          refine ⟨28805737538126019961475603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19203825025417346640983735 28805737538126019961475603)
          ·
            refine ⟨43208606307189029942213405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28805737538126019961475603 43208606307189029942213405)
            ·
              refine ⟨16203227365195886228330027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43208606307189029942213405 16203227365195886228330027)
              ·
                refine ⟨24304841047793829342495041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16203227365195886228330027 24304841047793829342495041)
                ·
                  refine ⟨18228630785845372006871281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24304841047793829342495041 18228630785845372006871281)
                  ·
                    refine ⟨13671473089384029005153461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18228630785845372006871281 13671473089384029005153461)
                    ·
                      refine ⟨1281700602129752719233137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13671473089384029005153461 1281700602129752719233137)
                      ·
                        rfl

theorem cell23_2496103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2496103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496103 prefixEnd_2496103 := by exact prefixLift 2496103
  have htrace : WordTrace (prefixWord ++ tailWord_2496103) baseStart_2496103 baseEnd_2496103 := by
    simpa [prefixWord, tailWord_2496103, baseEnd_2496103] using wordTrace_append hprefix tailTrace_2496103
  have hstable : (prefixWord ++ tailWord_2496103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496103).length < 2 ^ (prefixWord ++ tailWord_2496103).sum := by decide
  have hdescent : baseEnd_2496103 < baseStart_2496103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496133 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2496133 : Nat := 118140960795 + 2496133 * 2 ^ 59
def prefixEnd_2496133 : Nat := 4983230072969 + 3 ^ 40 * 2496133 * 2
def baseEnd_2496133 : Nat := 1281716006549387601857999

theorem tailTrace_2496133 : CollatzResearch.WordTrace tailWord_2496133 prefixEnd_2496133 1281716006549387601857999 := by
  unfold tailWord_2496133
  simp only [CollatzResearch.WordTrace]
  refine ⟨91041449865943921421589053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60694299910629280947726035 91041449865943921421589053)
  ·
    refine ⟨34140543699728970533095895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91041449865943921421589053 34140543699728970533095895)
    ·
      refine ⟨51210815549593455799643843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34140543699728970533095895 51210815549593455799643843)
      ·
        refine ⟨76816223324390183699465765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51210815549593455799643843 76816223324390183699465765)
        ·
          refine ⟨14403041873323159443649831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76816223324390183699465765 14403041873323159443649831)
          ·
            refine ⟨21604562809984739165474747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14403041873323159443649831 21604562809984739165474747)
            ·
              refine ⟨32406844214977108748212121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21604562809984739165474747 32406844214977108748212121)
              ·
                refine ⟨24305133161232831561159091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32406844214977108748212121 24305133161232831561159091)
                ·
                  refine ⟨36457699741849247341738637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24305133161232831561159091 36457699741849247341738637)
                  ·
                    refine ⟨13671637403193467753151989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36457699741849247341738637 13671637403193467753151989)
                    ·
                      refine ⟨1281716006549387601857999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13671637403193467753151989 1281716006549387601857999)
                      ·
                        rfl

theorem cell23_2496133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2496133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496133 prefixEnd_2496133 := by exact prefixLift 2496133
  have htrace : WordTrace (prefixWord ++ tailWord_2496133) baseStart_2496133 baseEnd_2496133 := by
    simpa [prefixWord, tailWord_2496133, baseEnd_2496133] using wordTrace_append hprefix tailTrace_2496133
  have hstable : (prefixWord ++ tailWord_2496133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496133).length < 2 ^ (prefixWord ++ tailWord_2496133).sum := by decide
  have hdescent : baseEnd_2496133 < baseStart_2496133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496198 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2496198 : Nat := 118140960795 + 2496198 * 2 ^ 59
def prefixEnd_2496198 : Nat := 4983230072969 + 3 ^ 40 * 2496198 * 2
def baseEnd_2496198 : Nat := 1281749382791929847545201

theorem tailTrace_2496198 : CollatzResearch.WordTrace tailWord_2496198 prefixEnd_2496198 1281749382791929847545201 := by
  unfold tailWord_2496198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845119394084638672584539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60695880407138958348470165 2845119394084638672584539)
  ·
    refine ⟨4267679091126958008876809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845119394084638672584539 4267679091126958008876809)
    ·
      refine ⟨3200759318345218506657607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4267679091126958008876809 3200759318345218506657607)
      ·
        refine ⟨4801138977517827759986411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200759318345218506657607 4801138977517827759986411)
        ·
          refine ⟨7201708466276741639979617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4801138977517827759986411 7201708466276741639979617)
          ·
            refine ⟨5401281349707556229984713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7201708466276741639979617 5401281349707556229984713)
            ·
              refine ⟨4050961012280667172488535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401281349707556229984713 4050961012280667172488535)
              ·
                refine ⟨6076441518421000758732803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050961012280667172488535 6076441518421000758732803)
                ·
                  refine ⟨9114662277631501138099205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6076441518421000758732803 9114662277631501138099205)
                  ·
                    refine ⟨1708999177055906463393601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9114662277631501138099205 1708999177055906463393601)
                    ·
                      refine ⟨1281749382791929847545201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1708999177055906463393601 1281749382791929847545201)
                      ·
                        rfl

theorem cell23_2496198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2496198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496198 prefixEnd_2496198 := by exact prefixLift 2496198
  have htrace : WordTrace (prefixWord ++ tailWord_2496198) baseStart_2496198 baseEnd_2496198 := by
    simpa [prefixWord, tailWord_2496198, baseEnd_2496198] using wordTrace_append hprefix tailTrace_2496198
  have hstable : (prefixWord ++ tailWord_2496198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496198).length < 2 ^ (prefixWord ++ tailWord_2496198).sum := by decide
  have hdescent : baseEnd_2496198 < baseStart_2496198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496217 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_2496217 : Nat := 118140960795 + 2496217 * 2 ^ 59
def prefixEnd_2496217 : Nat := 4983230072969 + 3 ^ 40 * 2496217 * 2
def baseEnd_2496217 : Nat := 427253046308121757735871

theorem tailTrace_2496217 : CollatzResearch.WordTrace tailWord_2496217 prefixEnd_2496217 427253046308121757735871 := by
  unfold tailWord_2496217
  simp only [CollatzResearch.WordTrace]
  refine ⟨91044513597639603767646905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60696342398426402511764603 91044513597639603767646905)
  ·
    refine ⟨68283385198229702825735179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91044513597639603767646905 68283385198229702825735179)
    ·
      refine ⟨102425077797344554238602769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68283385198229702825735179 102425077797344554238602769)
      ·
        refine ⟨76818808348008415678952077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102425077797344554238602769 76818808348008415678952077)
        ·
          refine ⟨28807053130503155879607029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76818808348008415678952077 28807053130503155879607029)
          ·
            refine ⟨2700661230984670863713159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28807053130503155879607029 2700661230984670863713159)
            ·
              refine ⟨4050991846477006295569739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700661230984670863713159 4050991846477006295569739)
              ·
                refine ⟨6076487769715509443354609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050991846477006295569739 6076487769715509443354609)
                ·
                  refine ⟨4557365827286632082515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6076487769715509443354609 4557365827286632082515957)
                  ·
                    refine ⟨427253046308121757735871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4557365827286632082515957 427253046308121757735871)
                    ·
                      rfl

theorem cell23_2496217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_2496217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496217 prefixEnd_2496217 := by exact prefixLift 2496217
  have htrace : WordTrace (prefixWord ++ tailWord_2496217) baseStart_2496217 baseEnd_2496217 := by
    simpa [prefixWord, tailWord_2496217, baseEnd_2496217] using wordTrace_append hprefix tailTrace_2496217
  have hstable : (prefixWord ++ tailWord_2496217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496217).length < 2 ^ (prefixWord ++ tailWord_2496217).sum := by decide
  have hdescent : baseEnd_2496217 < baseStart_2496217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496221 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 5]
def baseStart_2496221 : Nat := 118140960795 + 2496221 * 2 ^ 59
def prefixEnd_2496221 : Nat := 4983230072969 + 3 ^ 40 * 2496221 * 2
def baseEnd_2496221 : Nat := 142417910316331473061955

theorem tailTrace_2496221 : CollatzResearch.WordTrace tailWord_2496221 prefixEnd_2496221 142417910316331473061955 := by
  unfold tailWord_2496221
  simp only [CollatzResearch.WordTrace]
  refine ⟨91044659489625112450792517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60696439659750074967195011 91044659489625112450792517)
  ·
    refine ⟨17070873654304708584523597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91044659489625112450792517 17070873654304708584523597)
    ·
      refine ⟨6401577620364265719196349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17070873654304708584523597 6401577620364265719196349)
      ·
        refine ⟨2400591607636599644698631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6401577620364265719196349 2400591607636599644698631)
        ·
          refine ⟨3600887411454899467047947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400591607636599644698631 3600887411454899467047947)
          ·
            refine ⟨5401331117182349200571921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600887411454899467047947 5401331117182349200571921)
            ·
              refine ⟨4050998337886761900428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401331117182349200571921 4050998337886761900428941)
              ·
                refine ⟨1519124376707535712660853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4050998337886761900428941 1519124376707535712660853)
                ·
                  refine ⟨142417910316331473061955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519124376707535712660853 142417910316331473061955)
                  ·
                    rfl

theorem cell23_2496221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_2496221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496221 prefixEnd_2496221 := by exact prefixLift 2496221
  have htrace : WordTrace (prefixWord ++ tailWord_2496221) baseStart_2496221 baseEnd_2496221 := by
    simpa [prefixWord, tailWord_2496221, baseEnd_2496221] using wordTrace_append hprefix tailTrace_2496221
  have hstable : (prefixWord ++ tailWord_2496221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496221).length < 2 ^ (prefixWord ++ tailWord_2496221).sum := by decide
  have hdescent : baseEnd_2496221 < baseStart_2496221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496274 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2496274 : Nat := 118140960795 + 2496274 * 2 ^ 59
def prefixEnd_2496274 : Nat := 4983230072969 + 3 ^ 40 * 2496274 * 2
def baseEnd_2496274 : Nat := 1281788407321671550194851

theorem tailTrace_2496274 : CollatzResearch.WordTrace tailWord_2496274 prefixEnd_2496274 1281788407321671550194851 := by
  unfold tailWord_2496274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22761648139608275625617969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60697728372288735001647917 22761648139608275625617969)
  ·
    refine ⟨17071236104706206719213477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22761648139608275625617969 17071236104706206719213477)
    ·
      refine ⟨3200856769632413759852527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17071236104706206719213477 3200856769632413759852527)
      ·
        refine ⟨4801285154448620639778791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200856769632413759852527 4801285154448620639778791)
        ·
          refine ⟨7201927731672930959668187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4801285154448620639778791 7201927731672930959668187)
          ·
            refine ⟨10802891597509396439502281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7201927731672930959668187 10802891597509396439502281)
            ·
              refine ⟨8102168698132047329626711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10802891597509396439502281 8102168698132047329626711)
              ·
                refine ⟨12153253047198070994440067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8102168698132047329626711 12153253047198070994440067)
                ·
                  refine ⟨18229879570797106491660101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12153253047198070994440067 18229879570797106491660101)
                  ·
                    refine ⟨3418102419524457467186269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18229879570797106491660101 3418102419524457467186269)
                    ·
                      refine ⟨1281788407321671550194851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418102419524457467186269 1281788407321671550194851)
                      ·
                        rfl

theorem cell23_2496274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2496274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496274 prefixEnd_2496274 := by exact prefixLift 2496274
  have htrace : WordTrace (prefixWord ++ tailWord_2496274) baseStart_2496274 baseEnd_2496274 := by
    simpa [prefixWord, tailWord_2496274, baseEnd_2496274] using wordTrace_append hprefix tailTrace_2496274
  have hstable : (prefixWord ++ tailWord_2496274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496274).length < 2 ^ (prefixWord ++ tailWord_2496274).sum := by decide
  have hdescent : baseEnd_2496274 < baseStart_2496274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496327 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_2496327 : Nat := 118140960795 + 2496327 * 2 ^ 59
def prefixEnd_2496327 : Nat := 4983230072969 + 3 ^ 40 * 2496327 * 2
def baseEnd_2496327 : Nat := 1281815621796359842832107

theorem tailTrace_2496327 : CollatzResearch.WordTrace tailWord_2496327 prefixEnd_2496327 1281815621796359842832107 := by
  unfold tailWord_2496327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91048525627241092554151235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60699017084827395036100823 91048525627241092554151235)
  ·
    refine ⟨136572788440861638831226853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91048525627241092554151235 136572788440861638831226853)
    ·
      refine ⟨25607397832661557280855035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136572788440861638831226853 25607397832661557280855035)
      ·
        refine ⟨38411096748992335921282553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25607397832661557280855035 38411096748992335921282553)
        ·
          refine ⟨28808322561744251940961915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38411096748992335921282553 28808322561744251940961915)
          ·
            refine ⟨43212483842616377911442873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28808322561744251940961915 43212483842616377911442873)
            ·
              refine ⟨32409362881962283433582155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43212483842616377911442873 32409362881962283433582155)
              ·
                refine ⟨48614044322943425150373233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32409362881962283433582155 48614044322943425150373233)
                ·
                  refine ⟨36460533242207568862779925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48614044322943425150373233 36460533242207568862779925)
                  ·
                    refine ⟨1709087495728479790442809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36460533242207568862779925 1709087495728479790442809)
                    ·
                      refine ⟨1281815621796359842832107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709087495728479790442809 1281815621796359842832107)
                      ·
                        rfl

theorem cell23_2496327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_2496327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496327 prefixEnd_2496327 := by exact prefixLift 2496327
  have htrace : WordTrace (prefixWord ++ tailWord_2496327) baseStart_2496327 baseEnd_2496327 := by
    simpa [prefixWord, tailWord_2496327, baseEnd_2496327] using wordTrace_append hprefix tailTrace_2496327
  have hstable : (prefixWord ++ tailWord_2496327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496327).length < 2 ^ (prefixWord ++ tailWord_2496327).sum := by decide
  have hdescent : baseEnd_2496327 < baseStart_2496327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496337 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_2496337 : Nat := 118140960795 + 2496337 * 2 ^ 59
def prefixEnd_2496337 : Nat := 4983230072969 + 3 ^ 40 * 2496337 * 2
def baseEnd_2496337 : Nat := 427273585534301601235687

theorem tailTrace_2496337 : CollatzResearch.WordTrace tailWord_2496337 prefixEnd_2496337 427273585534301601235687 := by
  unfold tailWord_2496337
  simp only [CollatzResearch.WordTrace]
  refine ⟨91048890357204864262015265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60699260238136576174676843 91048890357204864262015265)
  ·
    refine ⟨68286667767903648196511449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91048890357204864262015265 68286667767903648196511449)
    ·
      refine ⟨51215000825927736147383587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68286667767903648196511449 51215000825927736147383587)
      ·
        refine ⟨76822501238891604221075381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51215000825927736147383587 76822501238891604221075381)
        ·
          refine ⟨7202109491146087895725817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76822501238891604221075381 7202109491146087895725817)
          ·
            refine ⟨5401582118359565921794363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7202109491146087895725817 5401582118359565921794363)
            ·
              refine ⟨8102373177539348882691545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401582118359565921794363 8102373177539348882691545)
              ·
                refine ⟨6076779883154511662018659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8102373177539348882691545 6076779883154511662018659)
                ·
                  refine ⟨9115169824731767493027989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6076779883154511662018659 9115169824731767493027989)
                  ·
                    refine ⟨427273585534301601235687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9115169824731767493027989 427273585534301601235687)
                    ·
                      rfl

theorem cell23_2496337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_2496337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496337 prefixEnd_2496337 := by exact prefixLift 2496337
  have htrace : WordTrace (prefixWord ++ tailWord_2496337) baseStart_2496337 baseEnd_2496337 := by
    simpa [prefixWord, tailWord_2496337, baseEnd_2496337] using wordTrace_append hprefix tailTrace_2496337
  have hstable : (prefixWord ++ tailWord_2496337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496337).length < 2 ^ (prefixWord ++ tailWord_2496337).sum := by decide
  have hdescent : baseEnd_2496337 < baseStart_2496337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496355 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 1, 1, 3]
def baseStart_2496355 : Nat := 118140960795 + 2496355 * 2 ^ 59
def prefixEnd_2496355 : Nat := 4983230072969 + 3 ^ 40 * 2496355 * 2
def baseEnd_2496355 : Nat := 1281829999254685733281979

theorem tailTrace_2496355 : CollatzResearch.WordTrace tailWord_2496355 prefixEnd_2496355 1281829999254685733281979 := by
  unfold tailWord_2496355
  simp only [CollatzResearch.WordTrace]
  refine ⟨91049546871139653336170519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60699697914093102224113679 91049546871139653336170519)
  ·
    refine ⟨136574320306709480004255779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91049546871139653336170519 136574320306709480004255779)
    ·
      refine ⟨204861480460064220006383669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136574320306709480004255779 204861480460064220006383669)
      ·
        refine ⟨19205763793131020625598469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204861480460064220006383669 19205763793131020625598469)
        ·
          refine ⟨3601080711212066367299713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19205763793131020625598469 3601080711212066367299713)
          ·
            refine ⟨2700810533409049775474785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601080711212066367299713 2700810533409049775474785)
            ·
              refine ⟨2025607900056787331606089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700810533409049775474785 2025607900056787331606089)
              ·
                refine ⟨1519205925042590498704567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025607900056787331606089 1519205925042590498704567)
                ·
                  refine ⟨2278808887563885748056851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519205925042590498704567 2278808887563885748056851)
                  ·
                    refine ⟨3418213331345828622085277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278808887563885748056851 3418213331345828622085277)
                    ·
                      refine ⟨1281829999254685733281979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418213331345828622085277 1281829999254685733281979)
                      ·
                        rfl

theorem cell23_2496355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_2496355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496355 prefixEnd_2496355 := by exact prefixLift 2496355
  have htrace : WordTrace (prefixWord ++ tailWord_2496355) baseStart_2496355 baseEnd_2496355 := by
    simpa [prefixWord, tailWord_2496355, baseEnd_2496355] using wordTrace_append hprefix tailTrace_2496355
  have hstable : (prefixWord ++ tailWord_2496355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496355).length < 2 ^ (prefixWord ++ tailWord_2496355).sum := by decide
  have hdescent : baseEnd_2496355 < baseStart_2496355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496398 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2496398 : Nat := 118140960795 + 2496398 * 2 ^ 59
def prefixEnd_2496398 : Nat := 4983230072969 + 3 ^ 40 * 2496398 * 2
def baseEnd_2496398 : Nat := 1281852078922829065044281

theorem tailTrace_2496398 : CollatzResearch.WordTrace tailWord_2496398 prefixEnd_2496398 1281852078922829065044281 := by
  unfold tailWord_2496398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11381389401247983959998231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60700743473322581119990565 11381389401247983959998231)
  ·
    refine ⟨17072084101871975939997347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11381389401247983959998231 17072084101871975939997347)
    ·
      refine ⟨25608126152807963909996021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17072084101871975939997347 25608126152807963909996021)
      ·
        refine ⟨2400761826825746616562127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25608126152807963909996021 2400761826825746616562127)
        ·
          refine ⟨3601142740238619924843191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400761826825746616562127 3601142740238619924843191)
          ·
            refine ⟨5401714110357929887264787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601142740238619924843191 5401714110357929887264787)
            ·
              refine ⟨8102571165536894830897181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401714110357929887264787 8102571165536894830897181)
              ·
                refine ⟨3038464187076335561586443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8102571165536894830897181 3038464187076335561586443)
                ·
                  refine ⟨4557696280614503342379665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038464187076335561586443 4557696280614503342379665)
                  ·
                    refine ⟨3418272210460877506784749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557696280614503342379665 3418272210460877506784749)
                    ·
                      refine ⟨1281852078922829065044281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418272210460877506784749 1281852078922829065044281)
                      ·
                        rfl

theorem cell23_2496398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2496398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496398 prefixEnd_2496398 := by exact prefixLift 2496398
  have htrace : WordTrace (prefixWord ++ tailWord_2496398) baseStart_2496398 baseEnd_2496398 := by
    simpa [prefixWord, tailWord_2496398, baseEnd_2496398] using wordTrace_append hprefix tailTrace_2496398
  have hstable : (prefixWord ++ tailWord_2496398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496398).length < 2 ^ (prefixWord ++ tailWord_2496398).sum := by decide
  have hdescent : baseEnd_2496398 < baseStart_2496398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496468 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2496468 : Nat := 118140960795 + 2496468 * 2 ^ 59
def prefixEnd_2496468 : Nat := 4983230072969 + 3 ^ 40 * 2496468 * 2
def baseEnd_2496468 : Nat := 1281888022568643791168959

theorem tailTrace_2496468 : CollatzResearch.WordTrace tailWord_2496468 prefixEnd_2496468 1281888022568643791168959 := by
  unfold tailWord_2496468
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526834159865136817517029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60702445546486849090022705 45526834159865136817517029)
  ·
    refine ⟨8536281404974713153284443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45526834159865136817517029 8536281404974713153284443)
    ·
      refine ⟨12804422107462069729926665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8536281404974713153284443 12804422107462069729926665)
      ·
        refine ⟨9603316580596552297444999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12804422107462069729926665 9603316580596552297444999)
        ·
          refine ⟨14404974870894828446167499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9603316580596552297444999 14404974870894828446167499)
          ·
            refine ⟨21607462306342242669251249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14404974870894828446167499 21607462306342242669251249)
            ·
              refine ⟨16205596729756682001938437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21607462306342242669251249 16205596729756682001938437)
              ·
                refine ⟨3038549386829377875363457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16205596729756682001938437 3038549386829377875363457)
                ·
                  refine ⟨2278912040122033406522593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038549386829377875363457 2278912040122033406522593)
                  ·
                    refine ⟨1709184030091525054891945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278912040122033406522593 1709184030091525054891945)
                    ·
                      refine ⟨1281888022568643791168959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709184030091525054891945 1281888022568643791168959)
                      ·
                        rfl

theorem cell23_2496468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2496468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496468 prefixEnd_2496468 := by exact prefixLift 2496468
  have htrace : WordTrace (prefixWord ++ tailWord_2496468) baseStart_2496468 baseEnd_2496468 := by
    simpa [prefixWord, tailWord_2496468, baseEnd_2496468] using wordTrace_append hprefix tailTrace_2496468
  have hstable : (prefixWord ++ tailWord_2496468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496468).length < 2 ^ (prefixWord ++ tailWord_2496468).sum := by decide
  have hdescent : baseEnd_2496468 < baseStart_2496468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496507 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_2496507 : Nat := 118140960795 + 2496507 * 2 ^ 59
def prefixEnd_2496507 : Nat := 4983230072969 + 3 ^ 40 * 2496507 * 2
def baseEnd_2496507 : Nat := 1281908048314169138581279

theorem tailTrace_2496507 : CollatzResearch.WordTrace tailWord_2496507 prefixEnd_2496507 1281908048314169138581279 := by
  unfold tailWord_2496507
  simp only [CollatzResearch.WordTrace]
  refine ⟨91055090766588983295703775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60703393844392655530469183 91055090766588983295703775)
  ·
    refine ⟨136582636149883474943555663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91055090766588983295703775 136582636149883474943555663)
    ·
      refine ⟨204873954224825212415333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136582636149883474943555663 204873954224825212415333495)
      ·
        refine ⟨307310931337237818623000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204873954224825212415333495 307310931337237818623000243)
        ·
          refine ⟨460966397005856727934500365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307310931337237818623000243 460966397005856727934500365)
          ·
            refine ⟨172862398877196272975437637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460966397005856727934500365 172862398877196272975437637)
            ·
              refine ⟨32411699789474301182894557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172862398877196272975437637 32411699789474301182894557)
              ·
                refine ⟨12154387421052862943585459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32411699789474301182894557 12154387421052862943585459)
                ·
                  refine ⟨18231581131579294415378189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12154387421052862943585459 18231581131579294415378189)
                  ·
                    refine ⟨6836842924342235405766821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18231581131579294415378189 6836842924342235405766821)
                    ·
                      refine ⟨1281908048314169138581279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6836842924342235405766821 1281908048314169138581279)
                      ·
                        rfl

theorem cell23_2496507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_2496507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496507 prefixEnd_2496507 := by exact prefixLift 2496507
  have htrace : WordTrace (prefixWord ++ tailWord_2496507) baseStart_2496507 baseEnd_2496507 := by
    simpa [prefixWord, tailWord_2496507, baseEnd_2496507] using wordTrace_append hprefix tailTrace_2496507
  have hstable : (prefixWord ++ tailWord_2496507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496507).length < 2 ^ (prefixWord ++ tailWord_2496507).sum := by decide
  have hdescent : baseEnd_2496507 < baseStart_2496507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496524 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2496524 : Nat := 118140960795 + 2496524 * 2 ^ 59
def prefixEnd_2496524 : Nat := 4983230072969 + 3 ^ 40 * 2496524 * 2
def baseEnd_2496524 : Nat := 1281916777485295572068701

theorem tailTrace_2496524 : CollatzResearch.WordTrace tailWord_2496524 prefixEnd_2496524 1281916777485295572068701 := by
  unfold tailWord_2496524
  simp only [CollatzResearch.WordTrace]
  refine ⟨45527855403763697599536313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60703807205018263466048417 45527855403763697599536313)
  ·
    refine ⟨34145891552822773199652235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45527855403763697599536313 34145891552822773199652235)
    ·
      refine ⟨51218837329234159799478353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34145891552822773199652235 51218837329234159799478353)
      ·
        refine ⟨38414127996925619849608765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51218837329234159799478353 38414127996925619849608765)
        ·
          refine ⟨14405297998847107443603287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38414127996925619849608765 14405297998847107443603287)
          ·
            refine ⟨21607946998270661165404931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14405297998847107443603287 21607946998270661165404931)
            ·
              refine ⟨32411920497405991748107397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21607946998270661165404931 32411920497405991748107397)
              ·
                refine ⟨6077235093263623452770137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32411920497405991748107397 6077235093263623452770137)
                ·
                  refine ⟨4557926319947717589577603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077235093263623452770137 4557926319947717589577603)
                  ·
                    refine ⟨6836889479921576384366405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557926319947717589577603 6836889479921576384366405)
                    ·
                      refine ⟨1281916777485295572068701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6836889479921576384366405 1281916777485295572068701)
                      ·
                        rfl

theorem cell23_2496524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2496524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496524 prefixEnd_2496524 := by exact prefixLift 2496524
  have htrace : WordTrace (prefixWord ++ tailWord_2496524) baseStart_2496524 baseEnd_2496524 := by
    simpa [prefixWord, tailWord_2496524, baseEnd_2496524] using wordTrace_append hprefix tailTrace_2496524
  have hstable : (prefixWord ++ tailWord_2496524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496524).length < 2 ^ (prefixWord ++ tailWord_2496524).sum := by decide
  have hdescent : baseEnd_2496524 < baseStart_2496524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496537 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_2496537 : Nat := 118140960795 + 2496537 * 2 ^ 59
def prefixEnd_2496537 : Nat := 4983230072969 + 3 ^ 40 * 2496537 * 2
def baseEnd_2496537 : Nat := 1281923452733804021206141

theorem tailTrace_2496537 : CollatzResearch.WordTrace tailWord_2496537 prefixEnd_2496537 1281923452733804021206141 := by
  unfold tailWord_2496537
  simp only [CollatzResearch.WordTrace]
  refine ⟨91056184956480298419295865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60704123304320198946197243 91056184956480298419295865)
  ·
    refine ⟨68292138717360223814471899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91056184956480298419295865 68292138717360223814471899)
    ·
      refine ⟨102438208076040335721707849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68292138717360223814471899 102438208076040335721707849)
      ·
        refine ⟨76828656057030251791280887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102438208076040335721707849 76828656057030251791280887)
        ·
          refine ⟨115242984085545377686921331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76828656057030251791280887 115242984085545377686921331)
          ·
            refine ⟨172864476128318066530381997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115242984085545377686921331 172864476128318066530381997)
            ·
              refine ⟨64824178548119274948893249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172864476128318066530381997 64824178548119274948893249)
              ·
                refine ⟨48618133911089456211669937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64824178548119274948893249 48618133911089456211669937)
                ·
                  refine ⟨36463600433317092158752453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48618133911089456211669937 36463600433317092158752453)
                  ·
                    refine ⟨6836925081246954779766085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36463600433317092158752453 6836925081246954779766085)
                    ·
                      refine ⟨1281923452733804021206141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6836925081246954779766085 1281923452733804021206141)
                      ·
                        rfl

theorem cell23_2496537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_2496537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496537 prefixEnd_2496537 := by exact prefixLift 2496537
  have htrace : WordTrace (prefixWord ++ tailWord_2496537) baseStart_2496537 baseEnd_2496537 := by
    simpa [prefixWord, tailWord_2496537, baseEnd_2496537] using wordTrace_append hprefix tailTrace_2496537
  have hstable : (prefixWord ++ tailWord_2496537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496537).length < 2 ^ (prefixWord ++ tailWord_2496537).sum := by decide
  have hdescent : baseEnd_2496537 < baseStart_2496537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496541 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_2496541 : Nat := 118140960795 + 2496541 * 2 ^ 59
def prefixEnd_2496541 : Nat := 4983230072969 + 3 ^ 40 * 2496541 * 2
def baseEnd_2496541 : Nat := 1281925506656422005556123

theorem tailTrace_2496541 : CollatzResearch.WordTrace tailWord_2496541 prefixEnd_2496541 1281925506656422005556123 := by
  unfold tailWord_2496541
  simp only [CollatzResearch.WordTrace]
  refine ⟨91056330848465807102441477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60704220565643871401627651 91056330848465807102441477)
  ·
    refine ⟨17073062034087338831707777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91056330848465807102441477 17073062034087338831707777)
    ·
      refine ⟨12804796525565504123780833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17073062034087338831707777 12804796525565504123780833)
      ·
        refine ⟨9603597394174128092835625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12804796525565504123780833 9603597394174128092835625)
        ·
          refine ⟨7202698045630596069626719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9603597394174128092835625 7202698045630596069626719)
          ·
            refine ⟨10804047068445894104440079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7202698045630596069626719 10804047068445894104440079)
            ·
              refine ⟨16206070602668841156660119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804047068445894104440079 16206070602668841156660119)
              ·
                refine ⟨24309105904003261734990179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16206070602668841156660119 24309105904003261734990179)
                ·
                  refine ⟨36463658856004892602485269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24309105904003261734990179 36463658856004892602485269)
                  ·
                    refine ⟨1709234008875229340741497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36463658856004892602485269 1709234008875229340741497)
                    ·
                      refine ⟨1281925506656422005556123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709234008875229340741497 1281925506656422005556123)
                      ·
                        rfl

theorem cell23_2496541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_2496541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496541 prefixEnd_2496541 := by exact prefixLift 2496541
  have htrace : WordTrace (prefixWord ++ tailWord_2496541) baseStart_2496541 baseEnd_2496541 := by
    simpa [prefixWord, tailWord_2496541, baseEnd_2496541] using wordTrace_append hprefix tailTrace_2496541
  have hstable : (prefixWord ++ tailWord_2496541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496541).length < 2 ^ (prefixWord ++ tailWord_2496541).sum := by decide
  have hdescent : baseEnd_2496541 < baseStart_2496541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496558 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2496558 : Nat := 118140960795 + 2496558 * 2 ^ 59
def prefixEnd_2496558 : Nat := 4983230072969 + 3 ^ 40 * 2496558 * 2
def baseEnd_2496558 : Nat := 1281934235827548439043545

theorem tailTrace_2496558 : CollatzResearch.WordTrace tailWord_2496558 prefixEnd_2496558 1281934235827548439043545 := by
  unfold tailWord_2496558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382118861175527375726291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60704633926269479337206885 11382118861175527375726291)
  ·
    refine ⟨17073178291763291063589437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11382118861175527375726291 17073178291763291063589437)
    ·
      refine ⟨6402441859411234148846039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17073178291763291063589437 6402441859411234148846039)
      ·
        refine ⟨9603662789116851223269059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6402441859411234148846039 9603662789116851223269059)
        ·
          refine ⟨14405494183675276834903589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9603662789116851223269059 14405494183675276834903589)
          ·
            refine ⟨2701030159439114406544423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14405494183675276834903589 2701030159439114406544423)
            ·
              refine ⟨4051545239158671609816635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701030159439114406544423 4051545239158671609816635)
              ·
                refine ⟨6077317858738007414724953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051545239158671609816635 6077317858738007414724953)
                ·
                  refine ⟨4557988394053505561043715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077317858738007414724953 4557988394053505561043715)
                  ·
                    refine ⟨6836982591080258341565573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557988394053505561043715 6836982591080258341565573)
                    ·
                      refine ⟨1281934235827548439043545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6836982591080258341565573 1281934235827548439043545)
                      ·
                        rfl

theorem cell23_2496558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2496558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496558 prefixEnd_2496558 := by exact prefixLift 2496558
  have htrace : WordTrace (prefixWord ++ tailWord_2496558) baseStart_2496558 baseEnd_2496558 := by
    simpa [prefixWord, tailWord_2496558, baseEnd_2496558] using wordTrace_append hprefix tailTrace_2496558
  have hstable : (prefixWord ++ tailWord_2496558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496558).length < 2 ^ (prefixWord ++ tailWord_2496558).sum := by decide
  have hdescent : baseEnd_2496558 < baseStart_2496558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496561 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2496561 : Nat := 118140960795 + 2496561 * 2 ^ 59
def prefixEnd_2496561 : Nat := 4983230072969 + 3 ^ 40 * 2496561 * 2
def baseEnd_2496561 : Nat := 1281935776269511927306031

theorem tailTrace_2496561 : CollatzResearch.WordTrace tailWord_2496561 prefixEnd_2496561 1281935776269511927306031 := by
  unfold tailWord_2496561
  simp only [CollatzResearch.WordTrace]
  refine ⟨91057060308393350518169537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60704706872262233678779691 91057060308393350518169537)
  ·
    refine ⟨68292795231295012888627153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91057060308393350518169537 68292795231295012888627153)
    ·
      refine ⟨51219596423471259666470365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68292795231295012888627153 51219596423471259666470365)
      ·
        refine ⟨19207348658801722374926387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51219596423471259666470365 19207348658801722374926387)
        ·
          refine ⟨28811022988202583562389581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19207348658801722374926387 28811022988202583562389581)
          ·
            refine ⟨10804133620575968835896093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28811022988202583562389581 10804133620575968835896093)
            ·
              refine ⟨4051550107715988313461035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10804133620575968835896093 4051550107715988313461035)
              ·
                refine ⟨6077325161573982470191553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051550107715988313461035 6077325161573982470191553)
                ·
                  refine ⟨4557993871180486852643665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077325161573982470191553 4557993871180486852643665)
                  ·
                    refine ⟨3418495403385365139482749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4557993871180486852643665 3418495403385365139482749)
                    ·
                      refine ⟨1281935776269511927306031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418495403385365139482749 1281935776269511927306031)
                      ·
                        rfl

theorem cell23_2496561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2496561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496561 prefixEnd_2496561 := by exact prefixLift 2496561
  have htrace : WordTrace (prefixWord ++ tailWord_2496561) baseStart_2496561 baseEnd_2496561 := by
    simpa [prefixWord, tailWord_2496561, baseEnd_2496561] using wordTrace_append hprefix tailTrace_2496561
  have hstable : (prefixWord ++ tailWord_2496561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496561).length < 2 ^ (prefixWord ++ tailWord_2496561).sum := by decide
  have hdescent : baseEnd_2496561 < baseStart_2496561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496587 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_2496587 : Nat := 118140960795 + 2496587 * 2 ^ 59
def prefixEnd_2496587 : Nat := 4983230072969 + 3 ^ 40 * 2496587 * 2
def baseEnd_2496587 : Nat := 1281949126766528825580911

theorem tailTrace_2496587 : CollatzResearch.WordTrace tailWord_2496587 prefixEnd_2496587 1281949126766528825580911 := by
  unfold tailWord_2496587
  simp only [CollatzResearch.WordTrace]
  refine ⟨91058008606299156958616015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60705339070866104639077343 91058008606299156958616015)
  ·
    refine ⟨136587012909448735437924023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91058008606299156958616015 136587012909448735437924023)
    ·
      refine ⟨204880519364173103156886035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136587012909448735437924023 204880519364173103156886035)
      ·
        refine ⟨307320779046259654735329053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204880519364173103156886035 307320779046259654735329053)
        ·
          refine ⟨115245292142347370525748395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307320779046259654735329053 115245292142347370525748395)
          ·
            refine ⟨172867938213521055788622593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115245292142347370525748395 172867938213521055788622593)
            ·
              refine ⟨129650953660140791841466945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172867938213521055788622593 129650953660140791841466945)
              ·
                refine ⟨97238215245105593881100209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129650953660140791841466945 97238215245105593881100209)
                ·
                  refine ⟨72928661433829195410825157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97238215245105593881100209 72928661433829195410825157)
                  ·
                    refine ⟨13674124018842974139529717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72928661433829195410825157 13674124018842974139529717)
                    ·
                      refine ⟨1281949126766528825580911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13674124018842974139529717 1281949126766528825580911)
                      ·
                        rfl

theorem cell23_2496587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_2496587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496587 prefixEnd_2496587 := by exact prefixLift 2496587
  have htrace : WordTrace (prefixWord ++ tailWord_2496587) baseStart_2496587 baseEnd_2496587 := by
    simpa [prefixWord, tailWord_2496587, baseEnd_2496587] using wordTrace_append hprefix tailTrace_2496587
  have hstable : (prefixWord ++ tailWord_2496587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496587).length < 2 ^ (prefixWord ++ tailWord_2496587).sum := by decide
  have hdescent : baseEnd_2496587 < baseStart_2496587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496631 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_2496631 : Nat := 118140960795 + 2496631 * 2 ^ 59
def prefixEnd_2496631 : Nat := 4983230072969 + 3 ^ 40 * 2496631 * 2
def baseEnd_2496631 : Nat := 1281971719915326653430709

theorem tailTrace_2496631 : CollatzResearch.WordTrace tailWord_2496631 prefixEnd_2496631 1281971719915326653430709 := by
  unfold tailWord_2496631
  simp only [CollatzResearch.WordTrace]
  refine ⟨91059613418139752473217747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60706408945426501648811831 91059613418139752473217747)
  ·
    refine ⟨136589420127209628709826621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91059613418139752473217747 136589420127209628709826621)
    ·
      refine ⟨51221032547703610766184983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136589420127209628709826621 51221032547703610766184983)
      ·
        refine ⟨76831548821555416149277475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51221032547703610766184983 76831548821555416149277475)
        ·
          refine ⟨115247323232333124223916213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76831548821555416149277475 115247323232333124223916213)
          ·
            refine ⟨10804436553031230395992145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115247323232333124223916213 10804436553031230395992145)
            ·
              refine ⟨8103327414773422796994109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10804436553031230395992145 8103327414773422796994109)
              ·
                refine ⟨3038747780540033548872791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8103327414773422796994109 3038747780540033548872791)
                ·
                  refine ⟨4558121670810050323309187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038747780540033548872791 4558121670810050323309187)
                  ·
                    refine ⟨6837182506215075484963781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558121670810050323309187 6837182506215075484963781)
                    ·
                      refine ⟨1281971719915326653430709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6837182506215075484963781 1281971719915326653430709)
                      ·
                        rfl

theorem cell23_2496631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_2496631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496631 prefixEnd_2496631 := by exact prefixLift 2496631
  have htrace : WordTrace (prefixWord ++ tailWord_2496631) baseStart_2496631 baseEnd_2496631 := by
    simpa [prefixWord, tailWord_2496631, baseEnd_2496631] using wordTrace_append hprefix tailTrace_2496631
  have hstable : (prefixWord ++ tailWord_2496631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496631).length < 2 ^ (prefixWord ++ tailWord_2496631).sum := by decide
  have hdescent : baseEnd_2496631 < baseStart_2496631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496644 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2496644 : Nat := 118140960795 + 2496644 * 2 ^ 59
def prefixEnd_2496644 : Nat := 4983230072969 + 3 ^ 40 * 2496644 * 2
def baseEnd_2496644 : Nat := 1281978395163835102568149

theorem tailTrace_2496644 : CollatzResearch.WordTrace tailWord_2496644 prefixEnd_2496644 1281978395163835102568149 := by
  unfold tailWord_2496644
  simp only [CollatzResearch.WordTrace]
  refine ⟨45530043783546327846720493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60706725044728437128960657 45530043783546327846720493)
  ·
    refine ⟨17073766418829872942520185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45530043783546327846720493 17073766418829872942520185)
    ·
      refine ⟨12805324814122404706890139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17073766418829872942520185 12805324814122404706890139)
      ·
        refine ⟨19207987221183607060335209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12805324814122404706890139 19207987221183607060335209)
        ·
          refine ⟨14405990415887705295251407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19207987221183607060335209 14405990415887705295251407)
          ·
            refine ⟨21608985623831557942877111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14405990415887705295251407 21608985623831557942877111)
            ·
              refine ⟨32413478435747336914315667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21608985623831557942877111 32413478435747336914315667)
              ·
                refine ⟨48620217653621005371473501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32413478435747336914315667 48620217653621005371473501)
                ·
                  refine ⟨18232581620107877014302563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48620217653621005371473501 18232581620107877014302563)
                  ·
                    refine ⟨27348872430161815521453845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18232581620107877014302563 27348872430161815521453845)
                    ·
                      refine ⟨1281978395163835102568149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27348872430161815521453845 1281978395163835102568149)
                      ·
                        rfl

theorem cell23_2496644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2496644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496644 prefixEnd_2496644 := by exact prefixLift 2496644
  have htrace : WordTrace (prefixWord ++ tailWord_2496644) baseStart_2496644 baseEnd_2496644 := by
    simpa [prefixWord, tailWord_2496644, baseEnd_2496644] using wordTrace_append hprefix tailTrace_2496644
  have hstable : (prefixWord ++ tailWord_2496644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496644).length < 2 ^ (prefixWord ++ tailWord_2496644).sum := by decide
  have hdescent : baseEnd_2496644 < baseStart_2496644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496658 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2496658 : Nat := 118140960795 + 2496658 * 2 ^ 59
def prefixEnd_2496658 : Nat := 4983230072969 + 3 ^ 40 * 2496658 * 2
def baseEnd_2496658 : Nat := 427328527964332682597695

theorem tailTrace_2496658 : CollatzResearch.WordTrace tailWord_2496658 prefixEnd_2496658 427328527964332682597695 := by
  unfold tailWord_2496658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22765149547260484021112657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60707065459361290722967085 22765149547260484021112657)
  ·
    refine ⟨17073862160445363015834493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22765149547260484021112657 17073862160445363015834493)
    ·
      refine ⟨6402698310167011130937935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17073862160445363015834493 6402698310167011130937935)
      ·
        refine ⟨9604047465250516696406903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6402698310167011130937935 9604047465250516696406903)
        ·
          refine ⟨14406071197875775044610355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9604047465250516696406903 14406071197875775044610355)
          ·
            refine ⟨21609106796813662566915533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14406071197875775044610355 21609106796813662566915533)
            ·
              refine ⟨8103415048805123462593325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21609106796813662566915533 8103415048805123462593325)
              ·
                refine ⟨3038780643301921298472497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8103415048805123462593325 3038780643301921298472497)
                ·
                  refine ⟨2279085482476440973854373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038780643301921298472497 2279085482476440973854373)
                  ·
                    refine ⟨427328527964332682597695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279085482476440973854373 427328527964332682597695)
                    ·
                      rfl

theorem cell23_2496658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2496658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496658 prefixEnd_2496658 := by exact prefixLift 2496658
  have htrace : WordTrace (prefixWord ++ tailWord_2496658) baseStart_2496658 baseEnd_2496658 := by
    simpa [prefixWord, tailWord_2496658, baseEnd_2496658] using wordTrace_append hprefix tailTrace_2496658
  have hstable : (prefixWord ++ tailWord_2496658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496658).length < 2 ^ (prefixWord ++ tailWord_2496658).sum := by decide
  have hdescent : baseEnd_2496658 < baseStart_2496658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496682 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2496682 : Nat := 118140960795 + 2496682 * 2 ^ 59
def prefixEnd_2496682 : Nat := 4983230072969 + 3 ^ 40 * 2496682 * 2
def baseEnd_2496682 : Nat := 1281997907428705953892975

theorem tailTrace_2496682 : CollatzResearch.WordTrace tailWord_2496682 prefixEnd_2496682 1281997907428705953892975 := by
  unfold tailWord_2496682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22765368385238747045831075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60707649027303325455549533 22765368385238747045831075)
  ·
    refine ⟨34148052577858120568746613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22765368385238747045831075 34148052577858120568746613)
    ·
      refine ⟨3201379929174198803319995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34148052577858120568746613 3201379929174198803319995)
      ·
        refine ⟨4802069893761298204979993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201379929174198803319995 4802069893761298204979993)
        ·
          refine ⟨3601552420320973653734995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4802069893761298204979993 3601552420320973653734995)
          ·
            refine ⟨5402328630481460480602493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601552420320973653734995 5402328630481460480602493)
            ·
              refine ⟨2025873236430547680225935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5402328630481460480602493 2025873236430547680225935)
              ·
                refine ⟨3038809854645821520338903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025873236430547680225935 3038809854645821520338903)
                ·
                  refine ⟨4558214781968732280508355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038809854645821520338903 4558214781968732280508355)
                  ·
                    refine ⟨6837322172953098420762533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558214781968732280508355 6837322172953098420762533)
                    ·
                      refine ⟨1281997907428705953892975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6837322172953098420762533 1281997907428705953892975)
                      ·
                        rfl

theorem cell23_2496682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2496682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496682 prefixEnd_2496682 := by exact prefixLift 2496682
  have htrace : WordTrace (prefixWord ++ tailWord_2496682) baseStart_2496682 baseEnd_2496682 := by
    simpa [prefixWord, tailWord_2496682, baseEnd_2496682] using wordTrace_append hprefix tailTrace_2496682
  have hstable : (prefixWord ++ tailWord_2496682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496682).length < 2 ^ (prefixWord ++ tailWord_2496682).sum := by decide
  have hdescent : baseEnd_2496682 < baseStart_2496682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496698 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_2496698 : Nat := 118140960795 + 2496698 * 2 ^ 59
def prefixEnd_2496698 : Nat := 4983230072969 + 3 ^ 40 * 2496698 * 2
def baseEnd_2496698 : Nat := 1282006123119177891292901

theorem tailTrace_2496698 : CollatzResearch.WordTrace tailWord_2496698 prefixEnd_2496698 1282006123119177891292901 := by
  unfold tailWord_2496698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22765514277224255728976687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60708038072598015277271165 22765514277224255728976687)
  ·
    refine ⟨34148271415836383593465031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22765514277224255728976687 34148271415836383593465031)
    ·
      refine ⟨51222407123754575390197547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34148271415836383593465031 51222407123754575390197547)
      ·
        refine ⟨76833610685631863085296321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51222407123754575390197547 76833610685631863085296321)
        ·
          refine ⟨57625208014223897313972241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76833610685631863085296321 57625208014223897313972241)
          ·
            refine ⟨43218906010667922985479181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57625208014223897313972241 43218906010667922985479181)
            ·
              refine ⟨16207089754000471119554693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43218906010667922985479181 16207089754000471119554693)
              ·
                refine ⟨3038829328875088334916505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16207089754000471119554693 3038829328875088334916505)
                ·
                  refine ⟨2279121996656316251187379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038829328875088334916505 2279121996656316251187379)
                  ·
                    refine ⟨3418682994984474376781069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279121996656316251187379 3418682994984474376781069)
                    ·
                      refine ⟨1282006123119177891292901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418682994984474376781069 1282006123119177891292901)
                      ·
                        rfl

theorem cell23_2496698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_2496698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496698 prefixEnd_2496698 := by exact prefixLift 2496698
  have htrace : WordTrace (prefixWord ++ tailWord_2496698) baseStart_2496698 baseEnd_2496698 := by
    simpa [prefixWord, tailWord_2496698, baseEnd_2496698] using wordTrace_append hprefix tailTrace_2496698
  have hstable : (prefixWord ++ tailWord_2496698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496698).length < 2 ^ (prefixWord ++ tailWord_2496698).sum := by decide
  have hdescent : baseEnd_2496698 < baseStart_2496698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496705 : List Nat := [1, 2, 6, 1, 3, 1, 1, 8]
def baseStart_2496705 : Nat := 118140960795 + 2496705 * 2 ^ 59
def prefixEnd_2496705 : Nat := 4983230072969 + 3 ^ 40 * 2496705 * 2
def baseEnd_2496705 : Nat := 47481841388287383848347

theorem tailTrace_2496705 : CollatzResearch.WordTrace tailWord_2496705 prefixEnd_2496705 47481841388287383848347 := by
  unfold tailWord_2496705
  simp only [CollatzResearch.WordTrace]
  refine ⟨91062312419871663111411569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60708208279914442074274379 91062312419871663111411569)
  ·
    refine ⟨68296734314903747333558677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91062312419871663111411569 68296734314903747333558677)
    ·
      refine ⟨3201409421011113156260563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68296734314903747333558677 3201409421011113156260563)
      ·
        refine ⟨4802114131516669734390845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201409421011113156260563 4802114131516669734390845)
        ·
          refine ⟨1800792799318751150396567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4802114131516669734390845 1800792799318751150396567)
          ·
            refine ⟨2701189198978126725594851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800792799318751150396567 2701189198978126725594851)
            ·
              refine ⟨4051783798467190088392277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701189198978126725594851 4051783798467190088392277)
              ·
                refine ⟨47481841388287383848347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4051783798467190088392277 47481841388287383848347)
                ·
                  rfl

theorem cell23_2496705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 8].length) (baseStart_2496705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496705 prefixEnd_2496705 := by exact prefixLift 2496705
  have htrace : WordTrace (prefixWord ++ tailWord_2496705) baseStart_2496705 baseEnd_2496705 := by
    simpa [prefixWord, tailWord_2496705, baseEnd_2496705] using wordTrace_append hprefix tailTrace_2496705
  have hstable : (prefixWord ++ tailWord_2496705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496705).length < 2 ^ (prefixWord ++ tailWord_2496705).sum := by decide
  have hdescent : baseEnd_2496705 < baseStart_2496705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496749 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2496749 : Nat := 118140960795 + 2496749 * 2 ^ 59
def prefixEnd_2496749 : Nat := 4983230072969 + 3 ^ 40 * 2496749 * 2
def baseEnd_2496749 : Nat := 1282032310632557191755167

theorem tailTrace_2496749 : CollatzResearch.WordTrace tailWord_2496749 prefixEnd_2496749 1282032310632557191755167 := by
  unfold tailWord_2496749
  simp only [CollatzResearch.WordTrace]
  refine ⟨91063917231712258626013301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60709278154474839084008867 91063917231712258626013301)
  ·
    refine ⟨8537242240473024246188747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91063917231712258626013301 8537242240473024246188747)
    ·
      refine ⟨12805863360709536369283121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8537242240473024246188747 12805863360709536369283121)
      ·
        refine ⟨9604397520532152276962341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12805863360709536369283121 9604397520532152276962341)
        ·
          refine ⟨1800824535099778551930439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9604397520532152276962341 1800824535099778551930439)
          ·
            refine ⟨2701236802649667827895659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800824535099778551930439 2701236802649667827895659)
            ·
              refine ⟨4051855203974501741843489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701236802649667827895659 4051855203974501741843489)
              ·
                refine ⟨3038891402980876306382617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4051855203974501741843489 3038891402980876306382617)
                ·
                  refine ⟨2279168552235657229786963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038891402980876306382617 2279168552235657229786963)
                  ·
                    refine ⟨3418752828353485844680445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279168552235657229786963 3418752828353485844680445)
                    ·
                      refine ⟨1282032310632557191755167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418752828353485844680445 1282032310632557191755167)
                      ·
                        rfl

theorem cell23_2496749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2496749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496749 prefixEnd_2496749 := by exact prefixLift 2496749
  have htrace : WordTrace (prefixWord ++ tailWord_2496749) baseStart_2496749 baseEnd_2496749 := by
    simpa [prefixWord, tailWord_2496749, baseEnd_2496749] using wordTrace_append hprefix tailTrace_2496749
  have hstable : (prefixWord ++ tailWord_2496749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496749).length < 2 ^ (prefixWord ++ tailWord_2496749).sum := by decide
  have hdescent : baseEnd_2496749 < baseStart_2496749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496751 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_2496751 : Nat := 118140960795 + 2496751 * 2 ^ 59
def prefixEnd_2496751 : Nat := 4983230072969 + 3 ^ 40 * 2496751 * 2
def baseEnd_2496751 : Nat := 1282033337593866183930157

theorem tailTrace_2496751 : CollatzResearch.WordTrace tailWord_2496751 prefixEnd_2496751 1282033337593866183930157 := by
  unfold tailWord_2496751
  simp only [CollatzResearch.WordTrace]
  refine ⟨91063990177705012967586107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60709326785136675311724071 91063990177705012967586107)
  ·
    refine ⟨136595985266557519451379161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91063990177705012967586107 136595985266557519451379161)
    ·
      refine ⟨102446988949918139588534371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136595985266557519451379161 102446988949918139588534371)
      ·
        refine ⟨153670483424877209382801557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102446988949918139588534371 153670483424877209382801557)
        ·
          refine ⟨7203303910541119189818823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153670483424877209382801557 7203303910541119189818823)
          ·
            refine ⟨10804955865811678784728235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203303910541119189818823 10804955865811678784728235)
            ·
              refine ⟨16207433798717518177092353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804955865811678784728235 16207433798717518177092353)
              ·
                refine ⟨12155575349038138632819265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16207433798717518177092353 12155575349038138632819265)
                ·
                  refine ⟨9116681511778603974614449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12155575349038138632819265 9116681511778603974614449)
                  ·
                    refine ⟨6837511133833952980960837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9116681511778603974614449 6837511133833952980960837)
                    ·
                      refine ⟨1282033337593866183930157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6837511133833952980960837 1282033337593866183930157)
                      ·
                        rfl

theorem cell23_2496751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_2496751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496751 prefixEnd_2496751 := by exact prefixLift 2496751
  have htrace : WordTrace (prefixWord ++ tailWord_2496751) baseStart_2496751 baseEnd_2496751 := by
    simpa [prefixWord, tailWord_2496751, baseEnd_2496751] using wordTrace_append hprefix tailTrace_2496751
  have hstable : (prefixWord ++ tailWord_2496751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496751).length < 2 ^ (prefixWord ++ tailWord_2496751).sum := by decide
  have hdescent : baseEnd_2496751 < baseStart_2496751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496771 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3]
def baseStart_2496771 : Nat := 118140960795 + 2496771 * 2 ^ 59
def prefixEnd_2496771 : Nat := 4983230072969 + 3 ^ 40 * 2496771 * 2
def baseEnd_2496771 : Nat := 1282043607206956105680065

theorem tailTrace_2496771 : CollatzResearch.WordTrace tailWord_2496771 prefixEnd_2496771 1282043607206956105680065 := by
  unfold tailWord_2496771
  simp only [CollatzResearch.WordTrace]
  refine ⟨91064719637632556383314167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60709813091755037588876111 91064719637632556383314167)
  ·
    refine ⟨136597079456448834574971251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91064719637632556383314167 136597079456448834574971251)
    ·
      refine ⟨204895619184673251862456877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136597079456448834574971251 204895619184673251862456877)
      ·
        refine ⟨76835857194252469448421329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204895619184673251862456877 76835857194252469448421329)
        ·
          refine ⟨57626892895689352086315997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76835857194252469448421329 57626892895689352086315997)
          ·
            refine ⟨21610084835883507032368499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57626892895689352086315997 21610084835883507032368499)
            ·
              refine ⟨32415127253825260548552749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21610084835883507032368499 32415127253825260548552749)
              ·
                refine ⟨12155672720184472705707281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32415127253825260548552749 12155672720184472705707281)
                ·
                  refine ⟨9116754540138354529280461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12155672720184472705707281 9116754540138354529280461)
                  ·
                    refine ⟨3418782952551882948480173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9116754540138354529280461 3418782952551882948480173)
                    ·
                      refine ⟨1282043607206956105680065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418782952551882948480173 1282043607206956105680065)
                      ·
                        rfl

theorem cell23_2496771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_2496771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496771 prefixEnd_2496771 := by exact prefixLift 2496771
  have htrace : WordTrace (prefixWord ++ tailWord_2496771) baseStart_2496771 baseEnd_2496771 := by
    simpa [prefixWord, tailWord_2496771, baseEnd_2496771] using wordTrace_append hprefix tailTrace_2496771
  have hstable : (prefixWord ++ tailWord_2496771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496771).length < 2 ^ (prefixWord ++ tailWord_2496771).sum := by decide
  have hdescent : baseEnd_2496771 < baseStart_2496771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496772 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_2496772 : Nat := 118140960795 + 2496772 * 2 ^ 59
def prefixEnd_2496772 : Nat := 4983230072969 + 3 ^ 40 * 2496772 * 2
def baseEnd_2496772 : Nat := 1282044120687610601767561

theorem tailTrace_2496772 : CollatzResearch.WordTrace tailWord_2496772 prefixEnd_2496772 1282044120687610601767561 := by
  unfold tailWord_2496772
  simp only [CollatzResearch.WordTrace]
  refine ⟨45532378055314466777050285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60709837407085955702733713 45532378055314466777050285)
  ·
    refine ⟨17074641770742925041393857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45532378055314466777050285 17074641770742925041393857)
    ·
      refine ⟨12805981328057193781045393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17074641770742925041393857 12805981328057193781045393)
      ·
        refine ⟨9604485996042895335784045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12805981328057193781045393 9604485996042895335784045)
        ·
          refine ⟨3601682248516085750919017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9604485996042895335784045 3601682248516085750919017)
          ·
            refine ⟨2701261686387064313189263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601682248516085750919017 2701261686387064313189263)
            ·
              refine ⟨4051892529580596469783895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701261686387064313189263 4051892529580596469783895)
              ·
                refine ⟨6077838794370894704675843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051892529580596469783895 6077838794370894704675843)
                ·
                  refine ⟨9116758191556342057013765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077838794370894704675843 9116758191556342057013765)
                  ·
                    refine ⟨1709392160916814135690081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9116758191556342057013765 1709392160916814135690081)
                    ·
                      refine ⟨1282044120687610601767561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709392160916814135690081 1282044120687610601767561)
                      ·
                        rfl

theorem cell23_2496772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_2496772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496772 prefixEnd_2496772 := by exact prefixLift 2496772
  have htrace : WordTrace (prefixWord ++ tailWord_2496772) baseStart_2496772 baseEnd_2496772 := by
    simpa [prefixWord, tailWord_2496772, baseEnd_2496772] using wordTrace_append hprefix tailTrace_2496772
  have hstable : (prefixWord ++ tailWord_2496772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496772).length < 2 ^ (prefixWord ++ tailWord_2496772).sum := by decide
  have hdescent : baseEnd_2496772 < baseStart_2496772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496791 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 7]
def baseStart_2496791 : Nat := 118140960795 + 2496791 * 2 ^ 59
def prefixEnd_2496791 : Nat := 4983230072969 + 3 ^ 40 * 2496791 * 2
def baseEnd_2496791 : Nat := 427351292273348675809991

theorem tailTrace_2496791 : CollatzResearch.WordTrace tailWord_2496791 prefixEnd_2496791 427351292273348675809991 := by
  unfold tailWord_2496791
  simp only [CollatzResearch.WordTrace]
  refine ⟨91065449097560099799042227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60710299398373399866028151 91065449097560099799042227)
  ·
    refine ⟨136598173646340149698563341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91065449097560099799042227 136598173646340149698563341)
    ·
      refine ⟨51224315117377556136961253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136598173646340149698563341 51224315117377556136961253)
      ·
        refine ⟨9604559084508291775680235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51224315117377556136961253 9604559084508291775680235)
        ·
          refine ⟨14406838626762437663520353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9604559084508291775680235 14406838626762437663520353)
          ·
            refine ⟨10805128970071828247640265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14406838626762437663520353 10805128970071828247640265)
            ·
              refine ⟨8103846727553871185730199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10805128970071828247640265 8103846727553871185730199)
              ·
                refine ⟨12155770091330806778595299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8103846727553871185730199 12155770091330806778595299)
                ·
                  refine ⟨18233655136996210167892949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12155770091330806778595299 18233655136996210167892949)
                  ·
                    refine ⟨427351292273348675809991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18233655136996210167892949 427351292273348675809991)
                    ·
                      rfl

theorem cell23_2496791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_2496791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496791 prefixEnd_2496791 := by exact prefixLift 2496791
  have htrace : WordTrace (prefixWord ++ tailWord_2496791) baseStart_2496791 baseEnd_2496791 := by
    simpa [prefixWord, tailWord_2496791, baseEnd_2496791] using wordTrace_append hprefix tailTrace_2496791
  have hstable : (prefixWord ++ tailWord_2496791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496791).length < 2 ^ (prefixWord ++ tailWord_2496791).sum := by decide
  have hdescent : baseEnd_2496791 < baseStart_2496791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496818 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2496818 : Nat := 118140960795 + 2496818 * 2 ^ 59
def prefixEnd_2496818 : Nat := 4983230072969 + 3 ^ 40 * 2496818 * 2
def baseEnd_2496818 : Nat := 1282067740797717421792349

theorem tailTrace_2496818 : CollatzResearch.WordTrace tailWord_2496818 prefixEnd_2496818 1282067740797717421792349 := by
  unfold tailWord_2496818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22766608467115570852568777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60710955912308188940183405 22766608467115570852568777)
  ·
    refine ⟨17074956350336678139426583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22766608467115570852568777 17074956350336678139426583)
    ·
      refine ⟨25612434525505017209139875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17074956350336678139426583 25612434525505017209139875)
      ·
        refine ⟨38418651788257525813709813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25612434525505017209139875 38418651788257525813709813)
        ·
          refine ⟨3601748605149143045035295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38418651788257525813709813 3601748605149143045035295)
          ·
            refine ⟨5402622907723714567552943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601748605149143045035295 5402622907723714567552943)
            ·
              refine ⟨8103934361585571851329415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402622907723714567552943 8103934361585571851329415)
              ·
                refine ⟨12155901542378357776994123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8103934361585571851329415 12155901542378357776994123)
                ·
                  refine ⟨18233852313567536665491185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12155901542378357776994123 18233852313567536665491185)
                  ·
                    refine ⟨13675389235175652499118389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18233852313567536665491185 13675389235175652499118389)
                    ·
                      refine ⟨1282067740797717421792349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13675389235175652499118389 1282067740797717421792349)
                      ·
                        rfl

theorem cell23_2496818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2496818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496818 prefixEnd_2496818 := by exact prefixLift 2496818
  have htrace : WordTrace (prefixWord ++ tailWord_2496818) baseStart_2496818 baseEnd_2496818 := by
    simpa [prefixWord, tailWord_2496818, baseEnd_2496818] using wordTrace_append hprefix tailTrace_2496818
  have hstable : (prefixWord ++ tailWord_2496818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496818).length < 2 ^ (prefixWord ++ tailWord_2496818).sum := by decide
  have hdescent : baseEnd_2496818 < baseStart_2496818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496828 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_2496828 : Nat := 118140960795 + 2496828 * 2 ^ 59
def prefixEnd_2496828 : Nat := 4983230072969 + 3 ^ 40 * 2496828 * 2
def baseEnd_2496828 : Nat := 1282072875604262382667303

theorem tailTrace_2496828 : CollatzResearch.WordTrace tailWord_2496828 prefixEnd_2496828 1282072875604262382667303 := by
  unfold tailWord_2496828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45533399299213027559069569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60711199065617370078759425 45533399299213027559069569)
  ·
    refine ⟨34150049474409770669302177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45533399299213027559069569 34150049474409770669302177)
    ·
      refine ⟨25612537105807328001976633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34150049474409770669302177 25612537105807328001976633)
      ·
        refine ⟨19209402829355496001482475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25612537105807328001976633 19209402829355496001482475)
        ·
          refine ⟨28814104244033244002223713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209402829355496001482475 28814104244033244002223713)
          ·
            refine ⟨21610578183024933001667785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28814104244033244002223713 21610578183024933001667785)
            ·
              refine ⟨16207933637268699751250839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21610578183024933001667785 16207933637268699751250839)
              ·
                refine ⟨24311900455903049626876259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16207933637268699751250839 24311900455903049626876259)
                ·
                  refine ⟨36467850683854574440314389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24311900455903049626876259 36467850683854574440314389)
                  ·
                    refine ⟨1709430500805683176889737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36467850683854574440314389 1709430500805683176889737)
                    ·
                      refine ⟨1282072875604262382667303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709430500805683176889737 1282072875604262382667303)
                      ·
                        rfl

theorem cell23_2496828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_2496828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496828 prefixEnd_2496828 := by exact prefixLift 2496828
  have htrace : WordTrace (prefixWord ++ tailWord_2496828) baseStart_2496828 baseEnd_2496828 := by
    simpa [prefixWord, tailWord_2496828, baseEnd_2496828] using wordTrace_append hprefix tailTrace_2496828
  have hstable : (prefixWord ++ tailWord_2496828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496828).length < 2 ^ (prefixWord ++ tailWord_2496828).sum := by decide
  have hdescent : baseEnd_2496828 < baseStart_2496828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496848 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_2496848 : Nat := 118140960795 + 2496848 * 2 ^ 59
def prefixEnd_2496848 : Nat := 4983230072969 + 3 ^ 40 * 2496848 * 2
def baseEnd_2496848 : Nat := 1282083145217352304417211

theorem tailTrace_2496848 : CollatzResearch.WordTrace tailWord_2496848 prefixEnd_2496848 1282083145217352304417211 := by
  unfold tailWord_2496848
  simp only [CollatzResearch.WordTrace]
  refine ⟨45533764029176799266933599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60711685372235732355911465 45533764029176799266933599)
  ·
    refine ⟨68300646043765198900400399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45533764029176799266933599 68300646043765198900400399)
    ·
      refine ⟨102450969065647798350600599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68300646043765198900400399 102450969065647798350600599)
      ·
        refine ⟨153676453598471697525900899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102450969065647798350600599 153676453598471697525900899)
        ·
          refine ⟨230514680397707546288851349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153676453598471697525900899 230514680397707546288851349)
          ·
            refine ⟨10805375643642541232289907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230514680397707546288851349 10805375643642541232289907)
            ·
              refine ⟨16208063465463811848434861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10805375643642541232289907 16208063465463811848434861)
              ·
                refine ⟨6078023799548929443163073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16208063465463811848434861 6078023799548929443163073)
                ·
                  refine ⟨4558517849661697082372305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078023799548929443163073 4558517849661697082372305)
                  ·
                    refine ⟨3418888387246272811779229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4558517849661697082372305 3418888387246272811779229)
                    ·
                      refine ⟨1282083145217352304417211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418888387246272811779229 1282083145217352304417211)
                      ·
                        rfl

theorem cell23_2496848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_2496848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496848 prefixEnd_2496848 := by exact prefixLift 2496848
  have htrace : WordTrace (prefixWord ++ tailWord_2496848) baseStart_2496848 baseEnd_2496848 := by
    simpa [prefixWord, tailWord_2496848, baseEnd_2496848] using wordTrace_append hprefix tailTrace_2496848
  have hstable : (prefixWord ++ tailWord_2496848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496848).length < 2 ^ (prefixWord ++ tailWord_2496848).sum := by decide
  have hdescent : baseEnd_2496848 < baseStart_2496848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496855 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 1, 4]
def baseStart_2496855 : Nat := 118140960795 + 2496855 * 2 ^ 59
def prefixEnd_2496855 : Nat := 4983230072969 + 3 ^ 40 * 2496855 * 2
def baseEnd_2496855 : Nat := 427362246527311259009893

theorem tailTrace_2496855 : CollatzResearch.WordTrace tailWord_2496855 prefixEnd_2496855 427362246527311259009893 := by
  unfold tailWord_2496855
  simp only [CollatzResearch.WordTrace]
  refine ⟨91067783369328238729372019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60711855579552159152914679 91067783369328238729372019)
  ·
    refine ⟨136601675053992358094058029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91067783369328238729372019 136601675053992358094058029)
    ·
      refine ⟨51225628145247134285271761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136601675053992358094058029 51225628145247134285271761)
      ·
        refine ⟨38419221108935350713953821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51225628145247134285271761 38419221108935350713953821)
        ·
          refine ⟨14407207915850756517732683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38419221108935350713953821 14407207915850756517732683)
          ·
            refine ⟨21610811873776134776599025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407207915850756517732683 21610811873776134776599025)
            ·
              refine ⟨16208108905332101082449269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21610811873776134776599025 16208108905332101082449269)
              ·
                refine ⟨1519510209874884476479619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16208108905332101082449269 1519510209874884476479619)
                ·
                  refine ⟨2279265314812326714719429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519510209874884476479619 2279265314812326714719429)
                  ·
                    refine ⟨427362246527311259009893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279265314812326714719429 427362246527311259009893)
                    ·
                      rfl

theorem cell23_2496855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_2496855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496855 prefixEnd_2496855 := by exact prefixLift 2496855
  have htrace : WordTrace (prefixWord ++ tailWord_2496855) baseStart_2496855 baseEnd_2496855 := by
    simpa [prefixWord, tailWord_2496855, baseEnd_2496855] using wordTrace_append hprefix tailTrace_2496855
  have hstable : (prefixWord ++ tailWord_2496855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496855).length < 2 ^ (prefixWord ++ tailWord_2496855).sum := by decide
  have hdescent : baseEnd_2496855 < baseStart_2496855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496868 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 6]
def baseStart_2496868 : Nat := 118140960795 + 2496868 * 2 ^ 59
def prefixEnd_2496868 : Nat := 4983230072969 + 3 ^ 40 * 2496868 * 2
def baseEnd_2496868 : Nat := 142454823870049136240791

theorem tailTrace_2496868 : CollatzResearch.WordTrace tailWord_2496868 prefixEnd_2496868 142454823870049136240791 := by
  unfold tailWord_2496868
  simp only [CollatzResearch.WordTrace]
  refine ⟨45534128759140570974797629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60712171678854094633063505 45534128759140570974797629)
  ·
    refine ⟨17075298284677714115549111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45534128759140570974797629 17075298284677714115549111)
    ·
      refine ⟨25612947427016571173323667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17075298284677714115549111 25612947427016571173323667)
      ·
        refine ⟨38419421140524856759985501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25612947427016571173323667 38419421140524856759985501)
        ·
          refine ⟨14407282927696821284994563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38419421140524856759985501 14407282927696821284994563)
          ·
            refine ⟨21610924391545231927491845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407282927696821284994563 21610924391545231927491845)
            ·
              refine ⟨4052048323414730986404721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21610924391545231927491845 4052048323414730986404721)
              ·
                refine ⟨3039036242561048239803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052048323414730986404721 3039036242561048239803541)
                ·
                  refine ⟨142454823870049136240791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3039036242561048239803541 142454823870049136240791)
                  ·
                    rfl

theorem cell23_2496868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_2496868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496868 prefixEnd_2496868 := by exact prefixLift 2496868
  have htrace : WordTrace (prefixWord ++ tailWord_2496868) baseStart_2496868 baseEnd_2496868 := by
    simpa [prefixWord, tailWord_2496868, baseEnd_2496868] using wordTrace_append hprefix tailTrace_2496868
  have hstable : (prefixWord ++ tailWord_2496868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496868).length < 2 ^ (prefixWord ++ tailWord_2496868).sum := by decide
  have hdescent : baseEnd_2496868 < baseStart_2496868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496872 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2496872 : Nat := 118140960795 + 2496872 * 2 ^ 59
def prefixEnd_2496872 : Nat := 4983230072969 + 3 ^ 40 * 2496872 * 2
def baseEnd_2496872 : Nat := 427365156251020070172367

theorem tailTrace_2496872 : CollatzResearch.WordTrace tailWord_2496872 prefixEnd_2496872 427365156251020070172367 := by
  unfold tailWord_2496872
  simp only [CollatzResearch.WordTrace]
  refine ⟨45534201705133325316370435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60712268940177767088493913 45534201705133325316370435)
  ·
    refine ⟨68301302557699987974555653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45534201705133325316370435 68301302557699987974555653)
    ·
      refine ⟨12806494229568747745229185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68301302557699987974555653 12806494229568747745229185)
      ·
        refine ⟨9604870672176560808921889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12806494229568747745229185 9604870672176560808921889)
        ·
          refine ⟨7203653004132420606691417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9604870672176560808921889 7203653004132420606691417)
          ·
            refine ⟨5402739753099315455018563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7203653004132420606691417 5402739753099315455018563)
            ·
              refine ⟨8104109629648973182527845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402739753099315455018563 8104109629648973182527845)
              ·
                refine ⟨1519520555559182471723971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8104109629648973182527845 1519520555559182471723971)
                ·
                  refine ⟨2279280833338773707585957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519520555559182471723971 2279280833338773707585957)
                  ·
                    refine ⟨427365156251020070172367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279280833338773707585957 427365156251020070172367)
                    ·
                      rfl

theorem cell23_2496872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2496872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496872 prefixEnd_2496872 := by exact prefixLift 2496872
  have htrace : WordTrace (prefixWord ++ tailWord_2496872) baseStart_2496872 baseEnd_2496872 := by
    simpa [prefixWord, tailWord_2496872, baseEnd_2496872] using wordTrace_append hprefix tailTrace_2496872
  have hstable : (prefixWord ++ tailWord_2496872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496872).length < 2 ^ (prefixWord ++ tailWord_2496872).sum := by decide
  have hdescent : baseEnd_2496872 < baseStart_2496872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496905 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 5, 2]
def baseStart_2496905 : Nat := 118140960795 + 2496905 * 2 ^ 59
def prefixEnd_2496905 : Nat := 4983230072969 + 3 ^ 40 * 2496905 * 2
def baseEnd_2496905 : Nat := 1282112413614658581404449

theorem tailTrace_2496905 : CollatzResearch.WordTrace tailWord_2496905 prefixEnd_2496905 1282112413614658581404449 := by
  unfold tailWord_2496905
  simp only [CollatzResearch.WordTrace]
  refine ⟨91069607019147097268692169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60713071346098064845794779 91069607019147097268692169)
  ·
    refine ⟨68302205264360322951519127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91069607019147097268692169 68302205264360322951519127)
    ·
      refine ⟨102453307896540484427278691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68302205264360322951519127 102453307896540484427278691)
      ·
        refine ⟨153679961844810726640918037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102453307896540484427278691 153679961844810726640918037)
        ·
          refine ⟨7203748211475502811293033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153679961844810726640918037 7203748211475502811293033)
          ·
            refine ⟨5402811158606627108469775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7203748211475502811293033 5402811158606627108469775)
            ·
              refine ⟨8104216737909940662704663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402811158606627108469775 8104216737909940662704663)
              ·
                refine ⟨12156325106864910994056995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8104216737909940662704663 12156325106864910994056995)
                ·
                  refine ⟨18234487660297366491085493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12156325106864910994056995 18234487660297366491085493)
                  ·
                    refine ⟨1709483218152878108539265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18234487660297366491085493 1709483218152878108539265)
                    ·
                      refine ⟨1282112413614658581404449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709483218152878108539265 1282112413614658581404449)
                      ·
                        rfl

theorem cell23_2496905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5, 2].length) (baseStart_2496905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496905 prefixEnd_2496905 := by exact prefixLift 2496905
  have htrace : WordTrace (prefixWord ++ tailWord_2496905) baseStart_2496905 baseEnd_2496905 := by
    simpa [prefixWord, tailWord_2496905, baseEnd_2496905] using wordTrace_append hprefix tailTrace_2496905
  have hstable : (prefixWord ++ tailWord_2496905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496905).length < 2 ^ (prefixWord ++ tailWord_2496905).sum := by decide
  have hdescent : baseEnd_2496905 < baseStart_2496905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496929 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2496929 : Nat := 118140960795 + 2496929 * 2 ^ 59
def prefixEnd_2496929 : Nat := 4983230072969 + 3 ^ 40 * 2496929 * 2
def baseEnd_2496929 : Nat := 1282124737150366487504339

theorem tailTrace_2496929 : CollatzResearch.WordTrace tailWord_2496929 prefixEnd_2496929 1282124737150366487504339 := by
  unfold tailWord_2496929
  simp only [CollatzResearch.WordTrace]
  refine ⟨91070482371060149367565841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60713654914040099578377227 91070482371060149367565841)
  ·
    refine ⟨68302861778295112025674381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91070482371060149367565841 68302861778295112025674381)
    ·
      refine ⟨25613573166860667009627893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68302861778295112025674381 25613573166860667009627893)
      ·
        refine ⟨2401272484393187532152615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25613573166860667009627893 2401272484393187532152615)
        ·
          refine ⟨3601908726589781298228923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401272484393187532152615 3601908726589781298228923)
          ·
            refine ⟨5402863089884671947343385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601908726589781298228923 5402863089884671947343385)
            ·
              refine ⟨4052147317413503960507539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5402863089884671947343385 4052147317413503960507539)
              ·
                refine ⟨6078220976120255940761309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052147317413503960507539 6078220976120255940761309)
                ·
                  refine ⟨2279332866045095977785491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6078220976120255940761309 2279332866045095977785491)
                  ·
                    refine ⟨3418999299067643966678237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279332866045095977785491 3418999299067643966678237)
                    ·
                      refine ⟨1282124737150366487504339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3418999299067643966678237 1282124737150366487504339)
                      ·
                        rfl

theorem cell23_2496929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2496929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496929 prefixEnd_2496929 := by exact prefixLift 2496929
  have htrace : WordTrace (prefixWord ++ tailWord_2496929) baseStart_2496929 baseEnd_2496929 := by
    simpa [prefixWord, tailWord_2496929, baseEnd_2496929] using wordTrace_append hprefix tailTrace_2496929
  have hstable : (prefixWord ++ tailWord_2496929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496929).length < 2 ^ (prefixWord ++ tailWord_2496929).sum := by decide
  have hdescent : baseEnd_2496929 < baseStart_2496929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496945 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_2496945 : Nat := 118140960795 + 2496945 * 2 ^ 59
def prefixEnd_2496945 : Nat := 4983230072969 + 3 ^ 40 * 2496945 * 2
def baseEnd_2496945 : Nat := 427377650946946141634755

theorem tailTrace_2496945 : CollatzResearch.WordTrace tailWord_2496945 prefixEnd_2496945 427377650946946141634755 := by
  unfold tailWord_2496945
  simp only [CollatzResearch.WordTrace]
  refine ⟨91071065939002184100148289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60714043959334789400098859 91071065939002184100148289)
  ·
    refine ⟨68303299454251638075111217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91071065939002184100148289 68303299454251638075111217)
    ·
      refine ⟨51227474590688728556333413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68303299454251638075111217 51227474590688728556333413)
      ·
        refine ⟨9605151485754136604312515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51227474590688728556333413 9605151485754136604312515)
        ·
          refine ⟨14407727228631204906468773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605151485754136604312515 14407727228631204906468773)
          ·
            refine ⟨2701448855368350919962895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14407727228631204906468773 2701448855368350919962895)
            ·
              refine ⟨4052173283052526379944343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701448855368350919962895 4052173283052526379944343)
              ·
                refine ⟨6078259924578789569916515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052173283052526379944343 6078259924578789569916515)
                ·
                  refine ⟨9117389886868184354874773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6078259924578789569916515 9117389886868184354874773)
                  ·
                    refine ⟨427377650946946141634755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9117389886868184354874773 427377650946946141634755)
                    ·
                      rfl

theorem cell23_2496945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_2496945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496945 prefixEnd_2496945 := by exact prefixLift 2496945
  have htrace : WordTrace (prefixWord ++ tailWord_2496945) baseStart_2496945 baseEnd_2496945 := by
    simpa [prefixWord, tailWord_2496945, baseEnd_2496945] using wordTrace_append hprefix tailTrace_2496945
  have hstable : (prefixWord ++ tailWord_2496945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496945).length < 2 ^ (prefixWord ++ tailWord_2496945).sum := by decide
  have hdescent : baseEnd_2496945 < baseStart_2496945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496969 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 1, 2, 2]
def baseStart_2496969 : Nat := 118140960795 + 2496969 * 2 ^ 59
def prefixEnd_2496969 : Nat := 4983230072969 + 3 ^ 40 * 2496969 * 2
def baseEnd_2496969 : Nat := 1282145276376546331004155

theorem tailTrace_2496969 : CollatzResearch.WordTrace tailWord_2496969 prefixEnd_2496969 1282145276376546331004155 := by
  unfold tailWord_2496969
  simp only [CollatzResearch.WordTrace]
  refine ⟨91071941290915236199021961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60714627527276824132681307 91071941290915236199021961)
  ·
    refine ⟨68303955968186427149266471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91071941290915236199021961 68303955968186427149266471)
    ·
      refine ⟨102455933952279640723899707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68303955968186427149266471 102455933952279640723899707)
      ·
        refine ⟨153683900928419461085849561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102455933952279640723899707 153683900928419461085849561)
        ·
          refine ⟨115262925696314595814387171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153683900928419461085849561 115262925696314595814387171)
          ·
            refine ⟨172894388544471893721580757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115262925696314595814387171 172894388544471893721580757)
            ·
              refine ⟨4052212231511060009099549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 172894388544471893721580757 4052212231511060009099549)
              ·
                refine ⟨1519579586816647503412331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4052212231511060009099549 1519579586816647503412331)
                ·
                  refine ⟨2279369380224971255118497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519579586816647503412331 2279369380224971255118497)
                  ·
                    refine ⟨1709527035168728441338873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2279369380224971255118497 1709527035168728441338873)
                    ·
                      refine ⟨1282145276376546331004155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709527035168728441338873 1282145276376546331004155)
                      ·
                        rfl

theorem cell23_2496969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 2, 2].length) (baseStart_2496969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496969 prefixEnd_2496969 := by exact prefixLift 2496969
  have htrace : WordTrace (prefixWord ++ tailWord_2496969) baseStart_2496969 baseEnd_2496969 := by
    simpa [prefixWord, tailWord_2496969, baseEnd_2496969] using wordTrace_append hprefix tailTrace_2496969
  have hstable : (prefixWord ++ tailWord_2496969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496969).length < 2 ^ (prefixWord ++ tailWord_2496969).sum := by decide
  have hdescent : baseEnd_2496969 < baseStart_2496969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496971 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 9]
def baseStart_2496971 : Nat := 118140960795 + 2496971 * 2 ^ 59
def prefixEnd_2496971 : Nat := 4983230072969 + 3 ^ 40 * 2496971 * 2
def baseEnd_2496971 : Nat := 427382101112618441059715

theorem tailTrace_2496971 : CollatzResearch.WordTrace tailWord_2496971 prefixEnd_2496971 427382101112618441059715 := by
  unfold tailWord_2496971
  simp only [CollatzResearch.WordTrace]
  refine ⟨91072014236907990540594767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60714676157938660360396511 91072014236907990540594767)
  ·
    refine ⟨136608021355361985810892151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91072014236907990540594767 136608021355361985810892151)
    ·
      refine ⟨204912032033042978716338227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136608021355361985810892151 204912032033042978716338227)
      ·
        refine ⟨307368048049564468074507341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204912032033042978716338227 307368048049564468074507341)
        ·
          refine ⟨115263018018586675527940253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307368048049564468074507341 115263018018586675527940253)
          ·
            refine ⟨43223631756970003322977595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115263018018586675527940253 43223631756970003322977595)
            ·
              refine ⟨64835447635455004984466393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43223631756970003322977595 64835447635455004984466393)
              ·
                refine ⟨48626585726591253738349795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64835447635455004984466393 48626585726591253738349795)
                ·
                  refine ⟨72939878589886880607524693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48626585726591253738349795 72939878589886880607524693)
                  ·
                    refine ⟨427382101112618441059715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 72939878589886880607524693 427382101112618441059715)
                    ·
                      rfl

theorem cell23_2496971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_2496971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496971 prefixEnd_2496971 := by exact prefixLift 2496971
  have htrace : WordTrace (prefixWord ++ tailWord_2496971) baseStart_2496971 baseEnd_2496971 := by
    simpa [prefixWord, tailWord_2496971, baseEnd_2496971] using wordTrace_append hprefix tailTrace_2496971
  have hstable : (prefixWord ++ tailWord_2496971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496971).length < 2 ^ (prefixWord ++ tailWord_2496971).sum := by decide
  have hdescent : baseEnd_2496971 < baseStart_2496971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496985 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 3]
def baseStart_2496985 : Nat := 118140960795 + 2496985 * 2 ^ 59
def prefixEnd_2496985 : Nat := 4983230072969 + 3 ^ 40 * 2496985 * 2
def baseEnd_2496985 : Nat := 1282153492067018268404081

theorem tailTrace_2496985 : CollatzResearch.WordTrace tailWord_2496985 prefixEnd_2496985 1282153492067018268404081 := by
  unfold tailWord_2496985
  simp only [CollatzResearch.WordTrace]
  refine ⟨91072524858857270931604409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60715016572571513954402939 91072524858857270931604409)
  ·
    refine ⟨68304393644142953198703307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91072524858857270931604409 68304393644142953198703307)
    ·
      refine ⟨102456590466214429798054961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68304393644142953198703307 102456590466214429798054961)
      ·
        refine ⟨76842442849660822348541221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102456590466214429798054961 76842442849660822348541221)
        ·
          refine ⟨14407958034311404190351479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76842442849660822348541221 14407958034311404190351479)
          ·
            refine ⟨21611937051467106285527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407958034311404190351479 21611937051467106285527219)
            ·
              refine ⟨32417905577200659428290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21611937051467106285527219 32417905577200659428290829)
              ·
                refine ⟨12156714591450247285609061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32417905577200659428290829 12156714591450247285609061)
                ·
                  refine ⟨2279383985896921366051699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12156714591450247285609061 2279383985896921366051699)
                  ·
                    refine ⟨3419075978845382049077549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279383985896921366051699 3419075978845382049077549)
                    ·
                      refine ⟨1282153492067018268404081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419075978845382049077549 1282153492067018268404081)
                      ·
                        rfl

theorem cell23_2496985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_2496985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496985 prefixEnd_2496985 := by exact prefixLift 2496985
  have htrace : WordTrace (prefixWord ++ tailWord_2496985) baseStart_2496985 baseEnd_2496985 := by
    simpa [prefixWord, tailWord_2496985, baseEnd_2496985] using wordTrace_append hprefix tailTrace_2496985
  have hstable : (prefixWord ++ tailWord_2496985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496985).length < 2 ^ (prefixWord ++ tailWord_2496985).sum := by decide
  have hdescent : baseEnd_2496985 < baseStart_2496985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496986 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_2496986 : Nat := 118140960795 + 2496986 * 2 ^ 59
def prefixEnd_2496986 : Nat := 4983230072969 + 3 ^ 40 * 2496986 * 2
def baseEnd_2496986 : Nat := 1282154005547672764491577

theorem tailTrace_2496986 : CollatzResearch.WordTrace tailWord_2496986 prefixEnd_2496986 1282154005547672764491577 := by
  unfold tailWord_2496986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768140332963412025597703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60715040887902432068260541 22768140332963412025597703)
  ·
    refine ⟨34152210499445118038396555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22768140332963412025597703 34152210499445118038396555)
    ·
      refine ⟨51228315749167677057594833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34152210499445118038396555 51228315749167677057594833)
      ·
        refine ⟨38421236811875757793196125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51228315749167677057594833 38421236811875757793196125)
        ·
          refine ⟨14407963804453409172448547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38421236811875757793196125 14407963804453409172448547)
          ·
            refine ⟨21611945706680113758672821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407963804453409172448547 21611945706680113758672821)
            ·
              refine ⟨2026119910001260664875577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21611945706680113758672821 2026119910001260664875577)
              ·
                refine ⟨1519589932500945498656683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026119910001260664875577 1519589932500945498656683)
                ·
                  refine ⟨2279384898751418247985025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519589932500945498656683 2279384898751418247985025)
                  ·
                    refine ⟨1709538674063563685988769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2279384898751418247985025 1709538674063563685988769)
                    ·
                      refine ⟨1282154005547672764491577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709538674063563685988769 1282154005547672764491577)
                      ·
                        rfl

theorem cell23_2496986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_2496986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2496986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2496986 prefixEnd_2496986 := by exact prefixLift 2496986
  have htrace : WordTrace (prefixWord ++ tailWord_2496986) baseStart_2496986 baseEnd_2496986 := by
    simpa [prefixWord, tailWord_2496986, baseEnd_2496986] using wordTrace_append hprefix tailTrace_2496986
  have hstable : (prefixWord ++ tailWord_2496986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496986).length < 2 ^ (prefixWord ++ tailWord_2496986).sum := by decide
  have hdescent : baseEnd_2496986 < baseStart_2496986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497037 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2497037 : Nat := 118140960795 + 2497037 * 2 ^ 59
def prefixEnd_2497037 : Nat := 4983230072969 + 3 ^ 40 * 2497037 * 2
def baseEnd_2497037 : Nat := 1282180193061052064953843

theorem tailTrace_2497037 : CollatzResearch.WordTrace tailWord_2497037 prefixEnd_2497037 1282180193061052064953843 := by
  unfold tailWord_2497037
  simp only [CollatzResearch.WordTrace]
  refine ⟨91074421454668883812497365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60716280969779255874998243 91074421454668883812497365)
  ·
    refine ⟨2134556752843801964355407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91074421454668883812497365 2134556752843801964355407)
    ·
      refine ⟨3201835129265702946533111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134556752843801964355407 3201835129265702946533111)
      ·
        refine ⟨4802752693898554419799667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201835129265702946533111 4802752693898554419799667)
        ·
          refine ⟨7204129040847831629699501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802752693898554419799667 7204129040847831629699501)
          ·
            refine ⟨2701548390317936861137313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7204129040847831629699501 2701548390317936861137313)
            ·
              refine ⟨2026161292738452645852985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701548390317936861137313 2026161292738452645852985)
              ·
                refine ⟨1519620969553839484389739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026161292738452645852985 1519620969553839484389739)
                ·
                  refine ⟨2279431454330759226584609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519620969553839484389739 2279431454330759226584609)
                  ·
                    refine ⟨1709573590748069419938457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2279431454330759226584609 1709573590748069419938457)
                    ·
                      refine ⟨1282180193061052064953843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709573590748069419938457 1282180193061052064953843)
                      ·
                        rfl

theorem cell23_2497037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2497037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497037 prefixEnd_2497037 := by exact prefixLift 2497037
  have htrace : WordTrace (prefixWord ++ tailWord_2497037) baseStart_2497037 baseEnd_2497037 := by
    simpa [prefixWord, tailWord_2497037, baseEnd_2497037] using wordTrace_append hprefix tailTrace_2497037
  have hstable : (prefixWord ++ tailWord_2497037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497037).length < 2 ^ (prefixWord ++ tailWord_2497037).sum := by decide
  have hdescent : baseEnd_2497037 < baseStart_2497037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497059 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 2, 2, 2]
def baseStart_2497059 : Nat := 118140960795 + 2497059 * 2 ^ 59
def prefixEnd_2497059 : Nat := 4983230072969 + 3 ^ 40 * 2497059 * 2
def baseEnd_2497059 : Nat := 1282191489635450978878741

theorem tailTrace_2497059 : CollatzResearch.WordTrace tailWord_2497059 prefixEnd_2497059 1282191489635450978878741 := by
  unfold tailWord_2497059
  simp only [CollatzResearch.WordTrace]
  refine ⟨91075223860589181569798231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60716815907059454379865487 91075223860589181569798231)
  ·
    refine ⟨136612835790883772354697347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91075223860589181569798231 136612835790883772354697347)
    ·
      refine ⟨204919253686325658532046021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136612835790883772354697347 204919253686325658532046021)
      ·
        refine ⟨38422360066186060974758629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204919253686325658532046021 38422360066186060974758629)
        ·
          refine ⟨7204192512409886432767243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38422360066186060974758629 7204192512409886432767243)
          ·
            refine ⟨10806288768614829649150865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7204192512409886432767243 10806288768614829649150865)
            ·
              refine ⟨8104716576461122236863149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10806288768614829649150865 8104716576461122236863149)
              ·
                refine ⟨3039268716172920838823681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8104716576461122236863149 3039268716172920838823681)
                ·
                  refine ⟨2279451537129690629117761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039268716172920838823681 2279451537129690629117761)
                  ·
                    refine ⟨1709588652847267971838321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2279451537129690629117761 1709588652847267971838321)
                    ·
                      refine ⟨1282191489635450978878741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709588652847267971838321 1282191489635450978878741)
                      ·
                        rfl

theorem cell23_2497059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_2497059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497059 prefixEnd_2497059 := by exact prefixLift 2497059
  have htrace : WordTrace (prefixWord ++ tailWord_2497059) baseStart_2497059 baseEnd_2497059 := by
    simpa [prefixWord, tailWord_2497059, baseEnd_2497059] using wordTrace_append hprefix tailTrace_2497059
  have hstable : (prefixWord ++ tailWord_2497059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497059).length < 2 ^ (prefixWord ++ tailWord_2497059).sum := by decide
  have hdescent : baseEnd_2497059 < baseStart_2497059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497082 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_2497082 : Nat := 118140960795 + 2497082 * 2 ^ 59
def prefixEnd_2497082 : Nat := 4983230072969 + 3 ^ 40 * 2497082 * 2
def baseEnd_2497082 : Nat := 142467033298944932099015

theorem tailTrace_2497082 : CollatzResearch.WordTrace tailWord_2497082 prefixEnd_2497082 142467033298944932099015 := by
  unfold tailWord_2497082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22769015684876464124471375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60717375159670570998590333 22769015684876464124471375)
  ·
    refine ⟨34153523527314696186707063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22769015684876464124471375 34153523527314696186707063)
    ·
      refine ⟨51230285290972044280060595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34153523527314696186707063 51230285290972044280060595)
      ·
        refine ⟨76845427936458066420090893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51230285290972044280060595 76845427936458066420090893)
        ·
          refine ⟨28817035476171774907534085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76845427936458066420090893 28817035476171774907534085)
          ·
            refine ⟨5403194151782207795162641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28817035476171774907534085 5403194151782207795162641)
            ·
              refine ⟨4052395613836655846371981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403194151782207795162641 4052395613836655846371981)
              ·
                refine ⟨1519648355188745942389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4052395613836655846371981 1519648355188745942389493)
                ·
                  refine ⟨142467033298944932099015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519648355188745942389493 142467033298944932099015)
                  ·
                    rfl

theorem cell23_2497082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_2497082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497082 prefixEnd_2497082 := by exact prefixLift 2497082
  have htrace : WordTrace (prefixWord ++ tailWord_2497082) baseStart_2497082 baseEnd_2497082 := by
    simpa [prefixWord, tailWord_2497082, baseEnd_2497082] using wordTrace_append hprefix tailTrace_2497082
  have hstable : (prefixWord ++ tailWord_2497082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497082).length < 2 ^ (prefixWord ++ tailWord_2497082).sum := by decide
  have hdescent : baseEnd_2497082 < baseStart_2497082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497088 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2497088 : Nat := 118140960795 + 2497088 * 2 ^ 59
def prefixEnd_2497088 : Nat := 4983230072969 + 3 ^ 40 * 2497088 * 2
def baseEnd_2497088 : Nat := 1282206380574431365416107

theorem tailTrace_2497088 : CollatzResearch.WordTrace tailWord_2497088 prefixEnd_2497088 1282206380574431365416107 := by
  unfold tailWord_2497088
  simp only [CollatzResearch.WordTrace]
  refine ⟨45538140788742059761301959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60717521051656079681735945 45538140788742059761301959)
  ·
    refine ⟨68307211183113089641952939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45538140788742059761301959 68307211183113089641952939)
    ·
      refine ⟨102460816774669634462929409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68307211183113089641952939 102460816774669634462929409)
      ·
        refine ⟨76845612581002225847197057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102460816774669634462929409 76845612581002225847197057)
        ·
          refine ⟨57634209435751669385397793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76845612581002225847197057 57634209435751669385397793)
          ·
            refine ⟨43225657076813752039048345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57634209435751669385397793 43225657076813752039048345)
            ·
              refine ⟨32419242807610314029286259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43225657076813752039048345 32419242807610314029286259)
              ·
                refine ⟨48628864211415471043929389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32419242807610314029286259 48628864211415471043929389)
                ·
                  refine ⟨18235824079280801641473521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48628864211415471043929389 18235824079280801641473521)
                  ·
                    refine ⟨13676868059460601231105141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18235824079280801641473521 13676868059460601231105141)
                    ·
                      refine ⟨1282206380574431365416107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13676868059460601231105141 1282206380574431365416107)
                      ·
                        rfl

theorem cell23_2497088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2497088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497088 prefixEnd_2497088 := by exact prefixLift 2497088
  have htrace : WordTrace (prefixWord ++ tailWord_2497088) baseStart_2497088 baseEnd_2497088 := by
    simpa [prefixWord, tailWord_2497088, baseEnd_2497088] using wordTrace_append hprefix tailTrace_2497088
  have hstable : (prefixWord ++ tailWord_2497088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497088).length < 2 ^ (prefixWord ++ tailWord_2497088).sum := by decide
  have hdescent : baseEnd_2497088 < baseStart_2497088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497135 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_2497135 : Nat := 118140960795 + 2497135 * 2 ^ 59
def prefixEnd_2497135 : Nat := 4983230072969 + 3 ^ 40 * 2497135 * 2
def baseEnd_2497135 : Nat := 1282230514165192681528391

theorem tailTrace_2497135 : CollatzResearch.WordTrace tailWord_2497135 prefixEnd_2497135 1282230514165192681528391 := by
  unfold tailWord_2497135
  simp only [CollatzResearch.WordTrace]
  refine ⟨91077995808313846549564859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60718663872209231033043239 91077995808313846549564859)
  ·
    refine ⟨136616993712470769824347289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91077995808313846549564859 136616993712470769824347289)
    ·
      refine ⟨102462745284353077368260467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136616993712470769824347289 102462745284353077368260467)
      ·
        refine ⟨153694117926529616052390701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102462745284353077368260467 153694117926529616052390701)
        ·
          refine ⟨57635294222448606019646513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153694117926529616052390701 57635294222448606019646513)
          ·
            refine ⟨43226470666836454514734885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57635294222448606019646513 43226470666836454514734885)
            ·
              refine ⟨8104963250031835221512791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43226470666836454514734885 8104963250031835221512791)
              ·
                refine ⟨12157444875047752832269187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8104963250031835221512791 12157444875047752832269187)
                ·
                  refine ⟨18236167312571629248403781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12157444875047752832269187 18236167312571629248403781)
                  ·
                    refine ⟨3419281371107180484075709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18236167312571629248403781 3419281371107180484075709)
                    ·
                      refine ⟨1282230514165192681528391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419281371107180484075709 1282230514165192681528391)
                      ·
                        rfl

theorem cell23_2497135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_2497135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497135 prefixEnd_2497135 := by exact prefixLift 2497135
  have htrace : WordTrace (prefixWord ++ tailWord_2497135) baseStart_2497135 baseEnd_2497135 := by
    simpa [prefixWord, tailWord_2497135, baseEnd_2497135] using wordTrace_append hprefix tailTrace_2497135
  have hstable : (prefixWord ++ tailWord_2497135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497135).length < 2 ^ (prefixWord ++ tailWord_2497135).sum := by decide
  have hdescent : baseEnd_2497135 < baseStart_2497135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497152 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_2497152 : Nat := 118140960795 + 2497152 * 2 ^ 59
def prefixEnd_2497152 : Nat := 4983230072969 + 3 ^ 40 * 2497152 * 2
def baseEnd_2497152 : Nat := 1282239243336319115015813

theorem tailTrace_2497152 : CollatzResearch.WordTrace tailWord_2497152 prefixEnd_2497152 1282239243336319115015813 := by
  unfold tailWord_2497152
  simp only [CollatzResearch.WordTrace]
  refine ⟨45539307924626129226466855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60719077232834838968622473 45539307924626129226466855)
  ·
    refine ⟨68308961886939193839700283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45539307924626129226466855 68308961886939193839700283)
    ·
      refine ⟨102463442830408790759550425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68308961886939193839700283 102463442830408790759550425)
      ·
        refine ⟨76847582122806593069662819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102463442830408790759550425 76847582122806593069662819)
        ·
          refine ⟨115271373184209889604494229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76847582122806593069662819 115271373184209889604494229)
          ·
            refine ⟨5403345618009838575210667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115271373184209889604494229 5403345618009838575210667)
            ·
              refine ⟨8105018427014757862816001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403345618009838575210667 8105018427014757862816001)
              ·
                refine ⟨6078763820261068397112001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8105018427014757862816001 6078763820261068397112001)
                ·
                  refine ⟨4559072865195801297834001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078763820261068397112001 4559072865195801297834001)
                  ·
                    refine ⟨3419304648896850973375501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4559072865195801297834001 3419304648896850973375501)
                    ·
                      refine ⟨1282239243336319115015813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419304648896850973375501 1282239243336319115015813)
                      ·
                        rfl

theorem cell23_2497152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_2497152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497152 prefixEnd_2497152 := by exact prefixLift 2497152
  have htrace : WordTrace (prefixWord ++ tailWord_2497152) baseStart_2497152 baseEnd_2497152 := by
    simpa [prefixWord, tailWord_2497152, baseEnd_2497152] using wordTrace_append hprefix tailTrace_2497152
  have hstable : (prefixWord ++ tailWord_2497152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497152).length < 2 ^ (prefixWord ++ tailWord_2497152).sum := by decide
  have hdescent : baseEnd_2497152 < baseStart_2497152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497168 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 11]
def baseStart_2497168 : Nat := 118140960795 + 2497168 * 2 ^ 59
def prefixEnd_2497168 : Nat := 4983230072969 + 3 ^ 40 * 2497168 * 2
def baseEnd_2497168 : Nat := 427415819675597017471913

theorem tailTrace_2497168 : CollatzResearch.WordTrace tailWord_2497168 prefixEnd_2497168 427415819675597017471913 := by
  unfold tailWord_2497168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45539599708597146592758079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60719466278129528790344105 45539599708597146592758079)
  ·
    refine ⟨68309399562895719889137119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45539599708597146592758079 68309399562895719889137119)
    ·
      refine ⟨102464099344343579833705679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68309399562895719889137119 102464099344343579833705679)
      ·
        refine ⟨153696149016515369750558519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102464099344343579833705679 153696149016515369750558519)
        ·
          refine ⟨230544223524773054625837779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153696149016515369750558519 230544223524773054625837779)
          ·
            refine ⟨345816335287159581938756669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230544223524773054625837779 345816335287159581938756669)
            ·
              refine ⟨129681125732684843227033751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345816335287159581938756669 129681125732684843227033751)
              ·
                refine ⟨194521688599027264840550627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129681125732684843227033751 194521688599027264840550627)
                ·
                  refine ⟨291782532898540897260825941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194521688599027264840550627 291782532898540897260825941)
                  ·
                    refine ⟨427415819675597017471913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 291782532898540897260825941 427415819675597017471913)
                    ·
                      rfl

theorem cell23_2497168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_2497168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497168 prefixEnd_2497168 := by exact prefixLift 2497168
  have htrace : WordTrace (prefixWord ++ tailWord_2497168) baseStart_2497168 baseEnd_2497168 := by
    simpa [prefixWord, tailWord_2497168, baseEnd_2497168] using wordTrace_append hprefix tailTrace_2497168
  have hstable : (prefixWord ++ tailWord_2497168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497168).length < 2 ^ (prefixWord ++ tailWord_2497168).sum := by decide
  have hdescent : baseEnd_2497168 < baseStart_2497168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497206 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2497206 : Nat := 118140960795 + 2497206 * 2 ^ 59
def prefixEnd_2497206 : Nat := 4983230072969 + 3 ^ 40 * 2497206 * 2
def baseEnd_2497206 : Nat := 142474107921295767082285

theorem tailTrace_2497206 : CollatzResearch.WordTrace tailWord_2497206 prefixEnd_2497206 142474107921295767082285 := by
  unfold tailWord_2497206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692536586941039104712467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60720390260704417116932981 5692536586941039104712467)
  ·
    refine ⟨8538804880411558657068701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5692536586941039104712467 8538804880411558657068701)
    ·
      refine ⟨3202051830154334496400763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8538804880411558657068701 3202051830154334496400763)
      ·
        refine ⟨4803077745231501744601145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202051830154334496400763 4803077745231501744601145)
        ·
          refine ⟨3602308308923626308450859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4803077745231501744601145 3602308308923626308450859)
          ·
            refine ⟨5403462463385439462676289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602308308923626308450859 5403462463385439462676289)
            ·
              refine ⟨4052596847539079597007217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403462463385439462676289 4052596847539079597007217)
              ·
                refine ⟨3039447635654309697755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052596847539079597007217 3039447635654309697755413)
                ·
                  refine ⟨142474107921295767082285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3039447635654309697755413 142474107921295767082285)
                  ·
                    rfl

theorem cell23_2497206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2497206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497206 prefixEnd_2497206 := by exact prefixLift 2497206
  have htrace : WordTrace (prefixWord ++ tailWord_2497206) baseStart_2497206 baseEnd_2497206 := by
    simpa [prefixWord, tailWord_2497206, baseEnd_2497206] using wordTrace_append hprefix tailTrace_2497206
  have hstable : (prefixWord ++ tailWord_2497206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497206).length < 2 ^ (prefixWord ++ tailWord_2497206).sum := by decide
  have hdescent : baseEnd_2497206 < baseStart_2497206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497216 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 1, 1, 3]
def baseStart_2497216 : Nat := 118140960795 + 2497216 * 2 ^ 59
def prefixEnd_2497216 : Nat := 4983230072969 + 3 ^ 40 * 2497216 * 2
def baseEnd_2497216 : Nat := 1282272106098206864615519

theorem tailTrace_2497216 : CollatzResearch.WordTrace tailWord_2497216 prefixEnd_2497216 1282272106098206864615519 := by
  unfold tailWord_2497216
  simp only [CollatzResearch.WordTrace]
  refine ⟨45540475060510198691631751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60720633414013598255509001 45540475060510198691631751)
  ·
    refine ⟨68310712590765298037447627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45540475060510198691631751 68310712590765298037447627)
    ·
      refine ⟨102466068886147947056171441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68310712590765298037447627 102466068886147947056171441)
      ·
        refine ⟨76849551664610960292128581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102466068886147947056171441 76849551664610960292128581)
        ·
          refine ⟨14409290937114555054774109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76849551664610960292128581 14409290937114555054774109)
          ·
            refine ⟨5403484101417958145540291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14409290937114555054774109 5403484101417958145540291)
            ·
              refine ⟨8105226152126937218310437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403484101417958145540291 8105226152126937218310437)
              ·
                refine ⟨1519729903523800728433207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8105226152126937218310437 1519729903523800728433207)
                ·
                  refine ⟨2279594855285701092649811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519729903523800728433207 2279594855285701092649811)
                  ·
                    refine ⟨3419392282928551638974717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279594855285701092649811 3419392282928551638974717)
                    ·
                      refine ⟨1282272106098206864615519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419392282928551638974717 1282272106098206864615519)
                      ·
                        rfl

theorem cell23_2497216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_2497216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497216 prefixEnd_2497216 := by exact prefixLift 2497216
  have htrace : WordTrace (prefixWord ++ tailWord_2497216) baseStart_2497216 baseEnd_2497216 := by
    simpa [prefixWord, tailWord_2497216, baseEnd_2497216] using wordTrace_append hprefix tailTrace_2497216
  have hstable : (prefixWord ++ tailWord_2497216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497216).length < 2 ^ (prefixWord ++ tailWord_2497216).sum := by decide
  have hdescent : baseEnd_2497216 < baseStart_2497216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497239 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_2497239 : Nat := 118140960795 + 2497239 * 2 ^ 59
def prefixEnd_2497239 : Nat := 4983230072969 + 3 ^ 40 * 2497239 * 2
def baseEnd_2497239 : Nat := 1282283916153260274627913

theorem tailTrace_2497239 : CollatzResearch.WordTrace tailWord_2497239 prefixEnd_2497239 1282283916153260274627913 := by
  unfold tailWord_2497239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91081788999937072311350771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60721192666624714874233847 91081788999937072311350771)
  ·
    refine ⟨136622683499905608467026157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91081788999937072311350771 136622683499905608467026157)
    ·
      refine ⟨51233506312464603175134809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136622683499905608467026157 51233506312464603175134809)
      ·
        refine ⟨38425129734348452381351107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51233506312464603175134809 38425129734348452381351107)
        ·
          refine ⟨57637694601522678572026661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38425129734348452381351107 57637694601522678572026661)
          ·
            refine ⟨10807067737785502232254999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57637694601522678572026661 10807067737785502232254999)
            ·
              refine ⟨16210601606678253348382499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807067737785502232254999 16210601606678253348382499)
              ·
                refine ⟨24315902410017380022573749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16210601606678253348382499 24315902410017380022573749)
                ·
                  refine ⟨2279615850939129377116289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24315902410017380022573749 2279615850939129377116289)
                  ·
                    refine ⟨1709711888204347032837217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2279615850939129377116289 1709711888204347032837217)
                    ·
                      refine ⟨1282283916153260274627913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709711888204347032837217 1282283916153260274627913)
                      ·
                        rfl

theorem cell23_2497239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_2497239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497239 prefixEnd_2497239 := by exact prefixLift 2497239
  have htrace : WordTrace (prefixWord ++ tailWord_2497239) baseStart_2497239 baseEnd_2497239 := by
    simpa [prefixWord, tailWord_2497239, baseEnd_2497239] using wordTrace_append hprefix tailTrace_2497239
  have hstable : (prefixWord ++ tailWord_2497239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497239).length < 2 ^ (prefixWord ++ tailWord_2497239).sum := by decide
  have hdescent : baseEnd_2497239 < baseStart_2497239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497242 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2497242 : Nat := 118140960795 + 2497242 * 2 ^ 59
def prefixEnd_2497242 : Nat := 4983230072969 + 3 ^ 40 * 2497242 * 2
def baseEnd_2497242 : Nat := 1282285456595223762890399

theorem tailTrace_2497242 : CollatzResearch.WordTrace tailWord_2497242 prefixEnd_2497242 1282285456595223762890399 := by
  unfold tailWord_2497242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22770474604731550955927495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60721265612617469215806653 22770474604731550955927495)
  ·
    refine ⟨34155711907097326433891243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22770474604731550955927495 34155711907097326433891243)
    ·
      refine ⟨51233567860645989650836865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34155711907097326433891243 51233567860645989650836865)
      ·
        refine ⟨38425175895484492238127649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51233567860645989650836865 38425175895484492238127649)
        ·
          refine ⟨28818881921613369178595737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38425175895484492238127649 28818881921613369178595737)
          ·
            refine ⟨21614161441210026883946803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28818881921613369178595737 21614161441210026883946803)
            ·
              refine ⟨32421242161815040325920205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614161441210026883946803 32421242161815040325920205)
              ·
                refine ⟨12157965810680640122220077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32421242161815040325920205 12157965810680640122220077)
                ·
                  refine ⟨4559237179005240045832529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12157965810680640122220077 4559237179005240045832529)
                  ·
                    refine ⟨3419427884253930034374397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4559237179005240045832529 3419427884253930034374397)
                    ·
                      refine ⟨1282285456595223762890399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419427884253930034374397 1282285456595223762890399)
                      ·
                        rfl

theorem cell23_2497242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2497242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497242 prefixEnd_2497242 := by exact prefixLift 2497242
  have htrace : WordTrace (prefixWord ++ tailWord_2497242) baseStart_2497242 baseEnd_2497242 := by
    simpa [prefixWord, tailWord_2497242, baseEnd_2497242] using wordTrace_append hprefix tailTrace_2497242
  have hstable : (prefixWord ++ tailWord_2497242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497242).length < 2 ^ (prefixWord ++ tailWord_2497242).sum := by decide
  have hdescent : baseEnd_2497242 < baseStart_2497242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497252 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_2497252 : Nat := 118140960795 + 2497252 * 2 ^ 59
def prefixEnd_2497252 : Nat := 4983230072969 + 3 ^ 40 * 2497252 * 2
def baseEnd_2497252 : Nat := 1282290591401768723765353

theorem tailTrace_2497252 : CollatzResearch.WordTrace tailWord_2497252 prefixEnd_2497252 1282290591401768723765353 := by
  unfold tailWord_2497252
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541131574444987765787005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60721508765926650354382673 45541131574444987765787005)
  ·
    refine ⟨17077924340416870412170127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45541131574444987765787005 17077924340416870412170127)
    ·
      refine ⟨25616886510625305618255191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17077924340416870412170127 25616886510625305618255191)
      ·
        refine ⟨38425329765937958427382787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25616886510625305618255191 38425329765937958427382787)
        ·
          refine ⟨57637994648906937641074181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38425329765937958427382787 57637994648906937641074181)
          ·
            refine ⟨10807123996670050807701409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57637994648906937641074181 10807123996670050807701409)
            ·
              refine ⟨8105342997502538105776057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10807123996670050807701409 8105342997502538105776057)
              ·
                refine ⟨6079007248126903579332043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8105342997502538105776057 6079007248126903579332043)
                ·
                  refine ⟨9118510872190355368998065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079007248126903579332043 9118510872190355368998065)
                  ·
                    refine ⟨6838883154142766526748549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9118510872190355368998065 6838883154142766526748549)
                    ·
                      refine ⟨1282290591401768723765353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6838883154142766526748549 1282290591401768723765353)
                      ·
                        rfl

theorem cell23_2497252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_2497252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497252 prefixEnd_2497252 := by exact prefixLift 2497252
  have htrace : WordTrace (prefixWord ++ tailWord_2497252) baseStart_2497252 baseEnd_2497252 := by
    simpa [prefixWord, tailWord_2497252, baseEnd_2497252] using wordTrace_append hprefix tailTrace_2497252
  have hstable : (prefixWord ++ tailWord_2497252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497252).length < 2 ^ (prefixWord ++ tailWord_2497252).sum := by decide
  have hdescent : baseEnd_2497252 < baseStart_2497252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497266 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_2497266 : Nat := 118140960795 + 2497266 * 2 ^ 59
def prefixEnd_2497266 : Nat := 4983230072969 + 3 ^ 40 * 2497266 * 2
def baseEnd_2497266 : Nat := 427432593376977222996763

theorem tailTrace_2497266 : CollatzResearch.WordTrace tailWord_2497266 prefixEnd_2497266 427432593376977222996763 := by
  unfold tailWord_2497266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22770693442709813980645913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60721849180559503948389101 22770693442709813980645913)
  ·
    refine ⟨17078020082032360485484435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22770693442709813980645913 17078020082032360485484435)
    ·
      refine ⟨25617030123048540728226653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17078020082032360485484435 25617030123048540728226653)
      ·
        refine ⟨9606386296143202773084995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25617030123048540728226653 9606386296143202773084995)
        ·
          refine ⟨14409579444214804159627493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9606386296143202773084995 14409579444214804159627493)
          ·
            refine ⟨2701796145790275779930155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14409579444214804159627493 2701796145790275779930155)
            ·
              refine ⟨4052694218685413669895233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701796145790275779930155 4052694218685413669895233)
              ·
                refine ⟨3039520664014060252421425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052694218685413669895233 3039520664014060252421425)
                ·
                  refine ⟨2279640498010545189316069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039520664014060252421425 2279640498010545189316069)
                  ·
                    refine ⟨427432593376977222996763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279640498010545189316069 427432593376977222996763)
                    ·
                      rfl

theorem cell23_2497266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_2497266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497266 prefixEnd_2497266 := by exact prefixLift 2497266
  have htrace : WordTrace (prefixWord ++ tailWord_2497266) baseStart_2497266 baseEnd_2497266 := by
    simpa [prefixWord, tailWord_2497266, baseEnd_2497266] using wordTrace_append hprefix tailTrace_2497266
  have hstable : (prefixWord ++ tailWord_2497266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497266).length < 2 ^ (prefixWord ++ tailWord_2497266).sum := by decide
  have hdescent : baseEnd_2497266 < baseStart_2497266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497285 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2497285 : Nat := 118140960795 + 2497285 * 2 ^ 59
def prefixEnd_2497285 : Nat := 4983230072969 + 3 ^ 40 * 2497285 * 2
def baseEnd_2497285 : Nat := 1282307536263367094652701

theorem tailTrace_2497285 : CollatzResearch.WordTrace tailWord_2497285 prefixEnd_2497285 1282307536263367094652701 := by
  unfold tailWord_2497285
  simp only [CollatzResearch.WordTrace]
  refine ⟨91083466757770422167525309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60722311171846948111683539 91083466757770422167525309)
  ·
    refine ⟨34156300034163908312821991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91083466757770422167525309 34156300034163908312821991)
    ·
      refine ⟨51234450051245862469232987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34156300034163908312821991 51234450051245862469232987)
      ·
        refine ⟨76851675076868793703849481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51234450051245862469232987 76851675076868793703849481)
        ·
          refine ⟨57638756307651595277887111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76851675076868793703849481 57638756307651595277887111)
          ·
            refine ⟨86458134461477392916830667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57638756307651595277887111 86458134461477392916830667)
            ·
              refine ⟨129687201692216089375246001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86458134461477392916830667 129687201692216089375246001)
              ·
                refine ⟨97265401269162067031434501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129687201692216089375246001 97265401269162067031434501)
                ·
                  refine ⟨18237262737967887568393969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97265401269162067031434501 18237262737967887568393969)
                  ·
                    refine ⟨13677947053475915676295477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18237262737967887568393969 13677947053475915676295477)
                    ·
                      refine ⟨1282307536263367094652701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13677947053475915676295477 1282307536263367094652701)
                      ·
                        rfl

theorem cell23_2497285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2497285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497285 prefixEnd_2497285 := by exact prefixLift 2497285
  have htrace : WordTrace (prefixWord ++ tailWord_2497285) baseStart_2497285 baseEnd_2497285 := by
    simpa [prefixWord, tailWord_2497285, baseEnd_2497285] using wordTrace_append hprefix tailTrace_2497285
  have hstable : (prefixWord ++ tailWord_2497285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497285).length < 2 ^ (prefixWord ++ tailWord_2497285).sum := by decide
  have hdescent : baseEnd_2497285 < baseStart_2497285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497289 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 3]
def baseStart_2497289 : Nat := 118140960795 + 2497289 * 2 ^ 59
def prefixEnd_2497289 : Nat := 4983230072969 + 3 ^ 40 * 2497289 * 2
def baseEnd_2497289 : Nat := 1282309590185985079002683

theorem tailTrace_2497289 : CollatzResearch.WordTrace tailWord_2497289 prefixEnd_2497289 1282309590185985079002683 := by
  unfold tailWord_2497289
  simp only [CollatzResearch.WordTrace]
  refine ⟨91083612649755930850670921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60722408433170620567113947 91083612649755930850670921)
  ·
    refine ⟨68312709487316948138003191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91083612649755930850670921 68312709487316948138003191)
    ·
      refine ⟨102469064230975422207004787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68312709487316948138003191 102469064230975422207004787)
      ·
        refine ⟨153703596346463133310507181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102469064230975422207004787 153703596346463133310507181)
        ·
          refine ⟨57638848629923674991440193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153703596346463133310507181 57638848629923674991440193)
          ·
            refine ⟨43229136472442756243580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57638848629923674991440193 43229136472442756243580145)
            ·
              refine ⟨32421852354332067182685109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43229136472442756243580145 32421852354332067182685109)
              ·
                refine ⟨3039548658218631298376729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32421852354332067182685109 3039548658218631298376729)
                ·
                  refine ⟨2279661493663973473782547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039548658218631298376729 2279661493663973473782547)
                  ·
                    refine ⟨3419492240495960210673821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279661493663973473782547 3419492240495960210673821)
                    ·
                      refine ⟨1282309590185985079002683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419492240495960210673821 1282309590185985079002683)
                      ·
                        rfl

theorem cell23_2497289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_2497289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497289 prefixEnd_2497289 := by exact prefixLift 2497289
  have htrace : WordTrace (prefixWord ++ tailWord_2497289) baseStart_2497289 baseEnd_2497289 := by
    simpa [prefixWord, tailWord_2497289, baseEnd_2497289] using wordTrace_append hprefix tailTrace_2497289
  have hstable : (prefixWord ++ tailWord_2497289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497289).length < 2 ^ (prefixWord ++ tailWord_2497289).sum := by decide
  have hdescent : baseEnd_2497289 < baseStart_2497289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497305 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_2497305 : Nat := 118140960795 + 2497305 * 2 ^ 59
def prefixEnd_2497305 : Nat := 4983230072969 + 3 ^ 40 * 2497305 * 2
def baseEnd_2497305 : Nat := 427439268625485672134203

theorem tailTrace_2497305 : CollatzResearch.WordTrace tailWord_2497305 prefixEnd_2497305 427439268625485672134203 := by
  unfold tailWord_2497305
  simp only [CollatzResearch.WordTrace]
  refine ⟨91084196217697965583253369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60722797478465310388835579 91084196217697965583253369)
  ·
    refine ⟨68313147163273474187440027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91084196217697965583253369 68313147163273474187440027)
    ·
      refine ⟨102469720744910211281160041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68313147163273474187440027 102469720744910211281160041)
      ·
        refine ⟨76852290558682658460870031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102469720744910211281160041 76852290558682658460870031)
        ·
          refine ⟨115278435838023987691305047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76852290558682658460870031 115278435838023987691305047)
          ·
            refine ⟨172917653757035981536957571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115278435838023987691305047 172917653757035981536957571)
            ·
              refine ⟨259376480635553972305436357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172917653757035981536957571 259376480635553972305436357)
              ·
                refine ⟨48633090119166369807269317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259376480635553972305436357 48633090119166369807269317)
                ·
                  refine ⟨9118704397343694338862997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48633090119166369807269317 9118704397343694338862997)
                  ·
                    refine ⟨427439268625485672134203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9118704397343694338862997 427439268625485672134203)
                    ·
                      rfl

theorem cell23_2497305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_2497305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497305 prefixEnd_2497305 := by exact prefixLift 2497305
  have htrace : WordTrace (prefixWord ++ tailWord_2497305) baseStart_2497305 baseEnd_2497305 := by
    simpa [prefixWord, tailWord_2497305, baseEnd_2497305] using wordTrace_append hprefix tailTrace_2497305
  have hstable : (prefixWord ++ tailWord_2497305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497305).length < 2 ^ (prefixWord ++ tailWord_2497305).sum := by decide
  have hdescent : baseEnd_2497305 < baseStart_2497305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497350 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2497350 : Nat := 118140960795 + 2497350 * 2 ^ 59
def prefixEnd_2497350 : Nat := 4983230072969 + 3 ^ 40 * 2497350 * 2
def baseEnd_2497350 : Nat := 1282340912505909340339903

theorem tailTrace_2497350 : CollatzResearch.WordTrace tailWord_2497350 prefixEnd_2497350 1282340912505909340339903 := by
  unfold tailWord_2497350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846432421954216820895047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60723891668356625512427669 2846432421954216820895047)
  ·
    refine ⟨4269648632931325231342571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2846432421954216820895047 4269648632931325231342571)
    ·
      refine ⟨6404472949396987847013857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269648632931325231342571 6404472949396987847013857)
      ·
        refine ⟨4803354712047740885260393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6404472949396987847013857 4803354712047740885260393)
        ·
          refine ⟨3602516034035805663945295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4803354712047740885260393 3602516034035805663945295)
          ·
            refine ⟨5403774051053708495917943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602516034035805663945295 5403774051053708495917943)
            ·
              refine ⟨8105661076580562743876915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403774051053708495917943 8105661076580562743876915)
              ·
                refine ⟨12158491614870844115815373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105661076580562743876915 12158491614870844115815373)
                ·
                  refine ⟨4559434355576566543430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12158491614870844115815373 4559434355576566543430765)
                  ·
                    refine ⟨1709787883341212453786537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4559434355576566543430765 1709787883341212453786537)
                    ·
                      refine ⟨1282340912505909340339903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709787883341212453786537 1282340912505909340339903)
                      ·
                        rfl

theorem cell23_2497350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2497350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497350 prefixEnd_2497350 := by exact prefixLift 2497350
  have htrace : WordTrace (prefixWord ++ tailWord_2497350) baseStart_2497350 baseEnd_2497350 := by
    simpa [prefixWord, tailWord_2497350, baseEnd_2497350] using wordTrace_append hprefix tailTrace_2497350
  have hstable : (prefixWord ++ tailWord_2497350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497350).length < 2 ^ (prefixWord ++ tailWord_2497350).sum := by decide
  have hdescent : baseEnd_2497350 < baseStart_2497350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497355 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_2497355 : Nat := 118140960795 + 2497355 * 2 ^ 59
def prefixEnd_2497355 : Nat := 4983230072969 + 3 ^ 40 * 2497355 * 2
def baseEnd_2497355 : Nat := 1282343479909181820777379

theorem tailTrace_2497355 : CollatzResearch.WordTrace tailWord_2497355 prefixEnd_2497355 1282343479909181820777379 := by
  unfold tailWord_2497355
  simp only [CollatzResearch.WordTrace]
  refine ⟨91086019867516824122573519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60724013245011216081715679 91086019867516824122573519)
  ·
    refine ⟨136629029801275236183860279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91086019867516824122573519 136629029801275236183860279)
    ·
      refine ⟨204943544701912854275790419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136629029801275236183860279 204943544701912854275790419)
      ·
        refine ⟨307415317052869281413685629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204943544701912854275790419 307415317052869281413685629)
        ·
          refine ⟨115280743894825980530132111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307415317052869281413685629 115280743894825980530132111)
          ·
            refine ⟨172921115842238970795198167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115280743894825980530132111 172921115842238970795198167)
            ·
              refine ⟨259381673763358456192797251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172921115842238970795198167 259381673763358456192797251)
              ·
                refine ⟨389072510645037684289195877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259381673763358456192797251 389072510645037684289195877)
                ·
                  refine ⟨72951095745944565804224227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389072510645037684289195877 72951095745944565804224227)
                  ·
                    refine ⟨109426643618916848706336341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72951095745944565804224227 109426643618916848706336341)
                    ·
                      refine ⟨1282343479909181820777379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 109426643618916848706336341 1282343479909181820777379)
                      ·
                        rfl

theorem cell23_2497355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_2497355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497355 prefixEnd_2497355 := by exact prefixLift 2497355
  have htrace : WordTrace (prefixWord ++ tailWord_2497355) baseStart_2497355 baseEnd_2497355 := by
    simpa [prefixWord, tailWord_2497355, baseEnd_2497355] using wordTrace_append hprefix tailTrace_2497355
  have hstable : (prefixWord ++ tailWord_2497355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497355).length < 2 ^ (prefixWord ++ tailWord_2497355).sum := by decide
  have hdescent : baseEnd_2497355 < baseStart_2497355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497392 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_2497392 : Nat := 118140960795 + 2497392 * 2 ^ 59
def prefixEnd_2497392 : Nat := 4983230072969 + 3 ^ 40 * 2497392 * 2
def baseEnd_2497392 : Nat := 1282362478693398176014709

theorem tailTrace_2497392 : CollatzResearch.WordTrace tailWord_2497392 prefixEnd_2497392 1282362478693398176014709 := by
  unfold tailWord_2497392
  simp only [CollatzResearch.WordTrace]
  refine ⟨45543684684191389720835215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60724912912255186294446953 45543684684191389720835215)
  ·
    refine ⟨68315527026287084581252823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45543684684191389720835215 68315527026287084581252823)
    ·
      refine ⟨102473290539430626871879235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68315527026287084581252823 102473290539430626871879235)
      ·
        refine ⟨153709935809145940307818853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102473290539430626871879235 153709935809145940307818853)
        ·
          refine ⟨28820612964214863807716035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153709935809145940307818853 28820612964214863807716035)
          ·
            refine ⟨43230919446322295711574053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28820612964214863807716035 43230919446322295711574053)
            ·
              refine ⟨8105797396185430445920135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43230919446322295711574053 8105797396185430445920135)
              ·
                refine ⟨12158696094278145668880203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105797396185430445920135 12158696094278145668880203)
                ·
                  refine ⟨18238044141417218503320305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158696094278145668880203 18238044141417218503320305)
                  ·
                    refine ⟨13678533106062913877490229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18238044141417218503320305 13678533106062913877490229)
                    ·
                      refine ⟨1282362478693398176014709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13678533106062913877490229 1282362478693398176014709)
                      ·
                        rfl

theorem cell23_2497392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_2497392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497392 prefixEnd_2497392 := by exact prefixLift 2497392
  have htrace : WordTrace (prefixWord ++ tailWord_2497392) baseStart_2497392 baseEnd_2497392 := by
    simpa [prefixWord, tailWord_2497392, baseEnd_2497392] using wordTrace_append hprefix tailTrace_2497392
  have hstable : (prefixWord ++ tailWord_2497392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497392).length < 2 ^ (prefixWord ++ tailWord_2497392).sum := by decide
  have hdescent : baseEnd_2497392 < baseStart_2497392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497402 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_2497402 : Nat := 118140960795 + 2497402 * 2 ^ 59
def prefixEnd_2497402 : Nat := 4983230072969 + 3 ^ 40 * 2497402 * 2
def baseEnd_2497402 : Nat := 1282367613499943136889663

theorem tailTrace_2497402 : CollatzResearch.WordTrace tailWord_2497402 prefixEnd_2497402 1282367613499943136889663 := by
  unfold tailWord_2497402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771933524586637787383615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60725156065564367433022973 22771933524586637787383615)
  ·
    refine ⟨34157900286879956681075423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771933524586637787383615 34157900286879956681075423)
    ·
      refine ⟨51236850430319935021613135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34157900286879956681075423 51236850430319935021613135)
      ·
        refine ⟨76855275645479902532419703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51236850430319935021613135 76855275645479902532419703)
        ·
          refine ⟨115282913468219853798629555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76855275645479902532419703 115282913468219853798629555)
          ·
            refine ⟨172924370202329780697944333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115282913468219853798629555 172924370202329780697944333)
            ·
              refine ⟨64846638825873667761729125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172924370202329780697944333 64846638825873667761729125)
              ·
                refine ⟨12158744779851312705324211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64846638825873667761729125 12158744779851312705324211)
                ·
                  refine ⟨18238117169776969057986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158744779851312705324211 18238117169776969057986317)
                  ·
                    refine ⟨6839293938666363396744869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18238117169776969057986317 6839293938666363396744869)
                    ·
                      refine ⟨1282367613499943136889663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6839293938666363396744869 1282367613499943136889663)
                      ·
                        rfl

theorem cell23_2497402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_2497402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497402 prefixEnd_2497402 := by exact prefixLift 2497402
  have htrace : WordTrace (prefixWord ++ tailWord_2497402) baseStart_2497402 baseEnd_2497402 := by
    simpa [prefixWord, tailWord_2497402, baseEnd_2497402] using wordTrace_append hprefix tailTrace_2497402
  have hstable : (prefixWord ++ tailWord_2497402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497402).length < 2 ^ (prefixWord ++ tailWord_2497402).sum := by decide
  have hdescent : baseEnd_2497402 < baseStart_2497402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497416 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_2497416 : Nat := 118140960795 + 2497416 * 2 ^ 59
def prefixEnd_2497416 : Nat := 4983230072969 + 3 ^ 40 * 2497416 * 2
def baseEnd_2497416 : Nat := 427458267409702027371533

theorem tailTrace_2497416 : CollatzResearch.WordTrace tailWord_2497416 prefixEnd_2497416 427458267409702027371533 := by
  unfold tailWord_2497416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45544122360147915770272051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60725496480197221027029401 45544122360147915770272051)
  ·
    refine ⟨68316183540221873655408077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45544122360147915770272051 68316183540221873655408077)
    ·
      refine ⟨25618568827583202620778029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68316183540221873655408077 25618568827583202620778029)
      ·
        refine ⟨9606963310343700982791761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25618568827583202620778029 9606963310343700982791761)
        ·
          refine ⟨7205222482757775737093821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9606963310343700982791761 7205222482757775737093821)
          ·
            refine ⟨2701958431034165901410183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7205222482757775737093821 2701958431034165901410183)
            ·
              refine ⟨4052937646551248852115275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701958431034165901410183 4052937646551248852115275)
              ·
                refine ⟨6079406469826873278172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052937646551248852115275 6079406469826873278172913)
                ·
                  refine ⟨4559554852370154958629685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079406469826873278172913 4559554852370154958629685)
                  ·
                    refine ⟨427458267409702027371533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559554852370154958629685 427458267409702027371533)
                    ·
                      rfl

theorem cell23_2497416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_2497416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497416 prefixEnd_2497416 := by exact prefixLift 2497416
  have htrace : WordTrace (prefixWord ++ tailWord_2497416) baseStart_2497416 baseEnd_2497416 := by
    simpa [prefixWord, tailWord_2497416, baseEnd_2497416] using wordTrace_append hprefix tailTrace_2497416
  have hstable : (prefixWord ++ tailWord_2497416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497416).length < 2 ^ (prefixWord ++ tailWord_2497416).sum := by decide
  have hdescent : baseEnd_2497416 < baseStart_2497416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497419 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4]
def baseStart_2497419 : Nat := 118140960795 + 2497419 * 2 ^ 59
def prefixEnd_2497419 : Nat := 4983230072969 + 3 ^ 40 * 2497419 * 2
def baseEnd_2497419 : Nat := 1282376342671069570377085

theorem tailTrace_2497419 : CollatzResearch.WordTrace tailWord_2497419 prefixEnd_2497419 1282376342671069570377085 := by
  unfold tailWord_2497419
  simp only [CollatzResearch.WordTrace]
  refine ⟨91088354139284963052903311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60725569426189975368602207 91088354139284963052903311)
  ·
    refine ⟨136632531208927444579354967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91088354139284963052903311 136632531208927444579354967)
    ·
      refine ⟨204948796813391166869032451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136632531208927444579354967 204948796813391166869032451)
      ·
        refine ⟨307423195220086750303548677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204948796813391166869032451 307423195220086750303548677)
        ·
          refine ⟨57641849103766265681915377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307423195220086750303548677 57641849103766265681915377)
          ·
            refine ⟨43231386827824699261436533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57641849103766265681915377 43231386827824699261436533)
            ·
              refine ⟨4052942515108565555759675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43231386827824699261436533 4052942515108565555759675)
              ·
                refine ⟨6079413772662848333639513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052942515108565555759675 6079413772662848333639513)
                ·
                  refine ⟨4559560329497136250229635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079413772662848333639513 4559560329497136250229635)
                  ·
                    refine ⟨6839340494245704375344453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559560329497136250229635 6839340494245704375344453)
                    ·
                      refine ⟨1282376342671069570377085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6839340494245704375344453 1282376342671069570377085)
                      ·
                        rfl

theorem cell23_2497419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].length) (baseStart_2497419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497419 prefixEnd_2497419 := by exact prefixLift 2497419
  have htrace : WordTrace (prefixWord ++ tailWord_2497419) baseStart_2497419 baseEnd_2497419 := by
    simpa [prefixWord, tailWord_2497419, baseEnd_2497419] using wordTrace_append hprefix tailTrace_2497419
  have hstable : (prefixWord ++ tailWord_2497419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497419).length < 2 ^ (prefixWord ++ tailWord_2497419).sum := by decide
  have hdescent : baseEnd_2497419 < baseStart_2497419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497480 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 1, 4]
def baseStart_2497480 : Nat := 118140960795 + 2497480 * 2 ^ 59
def prefixEnd_2497480 : Nat := 4983230072969 + 3 ^ 40 * 2497480 * 2
def baseEnd_2497480 : Nat := 427469221663664610571435

theorem tailTrace_2497480 : CollatzResearch.WordTrace tailWord_2497480 prefixEnd_2497480 427469221663664610571435 := by
  unfold tailWord_2497480
  simp only [CollatzResearch.WordTrace]
  refine ⟨45545289496031985235436947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60727052661375980313915929 45545289496031985235436947)
  ·
    refine ⟨68317934244047977853155421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45545289496031985235436947 68317934244047977853155421)
    ·
      refine ⟨25619225341517991694933283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68317934244047977853155421 25619225341517991694933283)
      ·
        refine ⟨38428838012276987542399925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25619225341517991694933283 38428838012276987542399925)
        ·
          refine ⟨3602703563650967582099993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38428838012276987542399925 3602703563650967582099993)
          ·
            refine ⟨2702027672738225686574995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3602703563650967582099993 2702027672738225686574995)
            ·
              refine ⟨4053041509107338529862493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702027672738225686574995 4053041509107338529862493)
              ·
                refine ⟨1519890565915251948698435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4053041509107338529862493 1519890565915251948698435)
                ·
                  refine ⟨2279835848872877923047653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519890565915251948698435 2279835848872877923047653)
                  ·
                    refine ⟨427469221663664610571435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279835848872877923047653 427469221663664610571435)
                    ·
                      rfl

theorem cell23_2497480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_2497480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497480 prefixEnd_2497480 := by exact prefixLift 2497480
  have htrace : WordTrace (prefixWord ++ tailWord_2497480) baseStart_2497480 baseEnd_2497480 := by
    simpa [prefixWord, tailWord_2497480, baseEnd_2497480] using wordTrace_append hprefix tailTrace_2497480
  have hstable : (prefixWord ++ tailWord_2497480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497480).length < 2 ^ (prefixWord ++ tailWord_2497480).sum := by decide
  have hdescent : baseEnd_2497480 < baseStart_2497480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497489 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_2497489 : Nat := 118140960795 + 2497489 * 2 ^ 59
def prefixEnd_2497489 : Nat := 4983230072969 + 3 ^ 40 * 2497489 * 2
def baseEnd_2497489 : Nat := 427470762105628098833921

theorem tailTrace_2497489 : CollatzResearch.WordTrace tailWord_2497489 prefixEnd_2497489 427470762105628098833921 := by
  unfold tailWord_2497489
  simp only [CollatzResearch.WordTrace]
  refine ⟨91090907249031365007951521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60727271499354243338634347 91090907249031365007951521)
  ·
    refine ⟨68318180436773523755963641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91090907249031365007951521 68318180436773523755963641)
    ·
      refine ⟨51238635327580142816972731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68318180436773523755963641 51238635327580142816972731)
      ·
        refine ⟨76857952991370214225459097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51238635327580142816972731 76857952991370214225459097)
        ·
          refine ⟨57643464743527660669094323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76857952991370214225459097 57643464743527660669094323)
          ·
            refine ⟨86465197115291491003641485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57643464743527660669094323 86465197115291491003641485)
            ·
              refine ⟨32424448918234309126365557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86465197115291491003641485 32424448918234309126365557)
              ·
                refine ⟨3039792086084466480596771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32424448918234309126365557 3039792086084466480596771)
                ·
                  refine ⟨4559688129126699720895157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039792086084466480596771 4559688129126699720895157)
                  ·
                    refine ⟨427470762105628098833921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559688129126699720895157 427470762105628098833921)
                    ·
                      rfl

theorem cell23_2497489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_2497489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497489 prefixEnd_2497489 := by exact prefixLift 2497489
  have htrace : WordTrace (prefixWord ++ tailWord_2497489) baseStart_2497489 baseEnd_2497489 := by
    simpa [prefixWord, tailWord_2497489, baseEnd_2497489] using wordTrace_append hprefix tailTrace_2497489
  have hstable : (prefixWord ++ tailWord_2497489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497489).length < 2 ^ (prefixWord ++ tailWord_2497489).sum := by decide
  have hdescent : baseEnd_2497489 < baseStart_2497489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497496 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2]
def baseStart_2497496 : Nat := 118140960795 + 2497496 * 2 ^ 59
def prefixEnd_2497496 : Nat := 4983230072969 + 3 ^ 40 * 2497496 * 2
def baseEnd_2497496 : Nat := 1282415880681465769114231

theorem tailTrace_2497496 : CollatzResearch.WordTrace tailWord_2497496 prefixEnd_2497496 1282415880681465769114231 := by
  unfold tailWord_2497496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45545581280003002601728171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60727441706670670135637561 45545581280003002601728171)
  ·
    refine ⟨68318371920004503902592257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45545581280003002601728171 68318371920004503902592257)
    ·
      refine ⟨51238778940003377926944193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68318371920004503902592257 51238778940003377926944193)
      ·
        refine ⟨38429084205002533445208145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51238778940003377926944193 38429084205002533445208145)
        ·
          refine ⟨28821813153751900083906109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38429084205002533445208145 28821813153751900083906109)
          ·
            refine ⟨10808179932656962531464791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28821813153751900083906109 10808179932656962531464791)
            ·
              refine ⟨16212269898985443797197187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10808179932656962531464791 16212269898985443797197187)
              ·
                refine ⟨24318404848478165695795781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16212269898985443797197187 24318404848478165695795781)
                ·
                  refine ⟨4559700909089656067961709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24318404848478165695795781 4559700909089656067961709)
                  ·
                    refine ⟨1709887840908621025485641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4559700909089656067961709 1709887840908621025485641)
                    ·
                      refine ⟨1282415880681465769114231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709887840908621025485641 1282415880681465769114231)
                      ·
                        rfl

theorem cell23_2497496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_2497496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497496 prefixEnd_2497496 := by exact prefixLift 2497496
  have htrace : WordTrace (prefixWord ++ tailWord_2497496) baseStart_2497496 baseEnd_2497496 := by
    simpa [prefixWord, tailWord_2497496, baseEnd_2497496] using wordTrace_append hprefix tailTrace_2497496
  have hstable : (prefixWord ++ tailWord_2497496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497496).length < 2 ^ (prefixWord ++ tailWord_2497496).sum := by decide
  have hdescent : baseEnd_2497496 < baseStart_2497496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497524 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2497524 : Nat := 118140960795 + 2497524 * 2 ^ 59
def prefixEnd_2497524 : Nat := 4983230072969 + 3 ^ 40 * 2497524 * 2
def baseEnd_2497524 : Nat := 1282430258139791659564103

theorem tailTrace_2497524 : CollatzResearch.WordTrace tailWord_2497524 prefixEnd_2497524 1282430258139791659564103 := by
  unfold tailWord_2497524
  simp only [CollatzResearch.WordTrace]
  refine ⟨45546091901952282992737813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60728122535936377323650417 45546091901952282992737813)
  ·
    refine ⟨2134973057904013265284585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45546091901952282992737813 2134973057904013265284585)
    ·
      refine ⟨1601229793428009948963439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2134973057904013265284585 1601229793428009948963439)
      ·
        refine ⟨2401844690142014923445159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601229793428009948963439 2401844690142014923445159)
        ·
          refine ⟨3602767035213022385167739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401844690142014923445159 3602767035213022385167739)
          ·
            refine ⟨5404150552819533577751609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602767035213022385167739 5404150552819533577751609)
            ·
              refine ⟨4053112914614650183313707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5404150552819533577751609 4053112914614650183313707)
              ·
                refine ⟨6079669371921975274970561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053112914614650183313707 6079669371921975274970561)
                ·
                  refine ⟨4559752028941481456227921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079669371921975274970561 4559752028941481456227921)
                  ·
                    refine ⟨3419814021706111092170941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4559752028941481456227921 3419814021706111092170941)
                    ·
                      refine ⟨1282430258139791659564103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3419814021706111092170941 1282430258139791659564103)
                      ·
                        rfl

theorem cell23_2497524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2497524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497524 prefixEnd_2497524 := by exact prefixLift 2497524
  have htrace : WordTrace (prefixWord ++ tailWord_2497524) baseStart_2497524 baseEnd_2497524 := by
    simpa [prefixWord, tailWord_2497524, baseEnd_2497524] using wordTrace_append hprefix tailTrace_2497524
  have hstable : (prefixWord ++ tailWord_2497524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497524).length < 2 ^ (prefixWord ++ tailWord_2497524).sum := by decide
  have hdescent : baseEnd_2497524 < baseStart_2497524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497543 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2497543 : Nat := 118140960795 + 2497543 * 2 ^ 59
def prefixEnd_2497543 : Nat := 4983230072969 + 3 ^ 40 * 2497543 * 2
def baseEnd_2497543 : Nat := 1282440014272227085226515

theorem tailTrace_2497543 : CollatzResearch.WordTrace tailWord_2497543 prefixEnd_2497543 1282440014272227085226515 := by
  unfold tailWord_2497543
  simp only [CollatzResearch.WordTrace]
  refine ⟨91092876790835732230417283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60728584527223821486944855 91092876790835732230417283)
  ·
    refine ⟨136639315186253598345625925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91092876790835732230417283 136639315186253598345625925)
    ·
      refine ⟨25619871597422549689804861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136639315186253598345625925 25619871597422549689804861)
      ·
        refine ⟨9607451849033456133676823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25619871597422549689804861 9607451849033456133676823)
        ·
          refine ⟨14411177773550184200515235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607451849033456133676823 14411177773550184200515235)
          ·
            refine ⟨21616766660325276300772853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14411177773550184200515235 21616766660325276300772853)
            ·
              refine ⟨2026571874405494653197455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21616766660325276300772853 2026571874405494653197455)
              ·
                refine ⟨3039857811608241979796183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2026571874405494653197455 3039857811608241979796183)
                ·
                  refine ⟨4559786717412362969694275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039857811608241979796183 4559786717412362969694275)
                  ·
                    refine ⟨6839680076118544454541413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559786717412362969694275 6839680076118544454541413)
                    ·
                      refine ⟨1282440014272227085226515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6839680076118544454541413 1282440014272227085226515)
                      ·
                        rfl

theorem cell23_2497543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2497543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497543 prefixEnd_2497543 := by exact prefixLift 2497543
  have htrace : WordTrace (prefixWord ++ tailWord_2497543) baseStart_2497543 baseEnd_2497543 := by
    simpa [prefixWord, tailWord_2497543, baseEnd_2497543] using wordTrace_append hprefix tailTrace_2497543
  have hstable : (prefixWord ++ tailWord_2497543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497543).length < 2 ^ (prefixWord ++ tailWord_2497543).sum := by decide
  have hdescent : baseEnd_2497543 < baseStart_2497543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497546 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2497546 : Nat := 118140960795 + 2497546 * 2 ^ 59
def prefixEnd_2497546 : Nat := 4983230072969 + 3 ^ 40 * 2497546 * 2
def baseEnd_2497546 : Nat := 1282441554714190573489001

theorem tailTrace_2497546 : CollatzResearch.WordTrace tailWord_2497546 prefixEnd_2497546 1282441554714190573489001 := by
  unfold tailWord_2497546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22773246552456215935694123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60728657473216575828517661 22773246552456215935694123)
  ·
    refine ⟨34159869828684323903541185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22773246552456215935694123 34159869828684323903541185)
    ·
      refine ⟨25619902371513242927655889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34159869828684323903541185 25619902371513242927655889)
      ·
        refine ⟨19214926778634932195741917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25619902371513242927655889 19214926778634932195741917)
        ·
          refine ⟨7205597541988099573403219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19214926778634932195741917 7205597541988099573403219)
          ·
            refine ⟨10808396312982149360104829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7205597541988099573403219 10808396312982149360104829)
            ·
              refine ⟨4053148617368306010039311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10808396312982149360104829 4053148617368306010039311)
              ·
                refine ⟨6079722926052459015058967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053148617368306010039311 6079722926052459015058967)
                ·
                  refine ⟨9119584389078688522588451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079722926052459015058967 9119584389078688522588451)
                  ·
                    refine ⟨13679376583618032783882677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9119584389078688522588451 13679376583618032783882677)
                    ·
                      refine ⟨1282441554714190573489001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13679376583618032783882677 1282441554714190573489001)
                      ·
                        rfl

theorem cell23_2497546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2497546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497546 prefixEnd_2497546 := by exact prefixLift 2497546
  have htrace : WordTrace (prefixWord ++ tailWord_2497546) baseStart_2497546 baseEnd_2497546 := by
    simpa [prefixWord, tailWord_2497546, baseEnd_2497546] using wordTrace_append hprefix tailTrace_2497546
  have hstable : (prefixWord ++ tailWord_2497546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497546).length < 2 ^ (prefixWord ++ tailWord_2497546).sum := by decide
  have hdescent : baseEnd_2497546 < baseStart_2497546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497589 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2497589 : Nat := 118140960795 + 2497589 * 2 ^ 59
def prefixEnd_2497589 : Nat := 4983230072969 + 3 ^ 40 * 2497589 * 2
def baseEnd_2497589 : Nat := 1282463634382333905251303

theorem tailTrace_2497589 : CollatzResearch.WordTrace tailWord_2497589 prefixEnd_2497589 1282463634382333905251303 := by
  unfold tailWord_2497589
  simp only [CollatzResearch.WordTrace]
  refine ⟨91094554548669082086591821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60729703032446054724394547 91094554548669082086591821)
  ·
    refine ⟨34160457955750905782471933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91094554548669082086591821 34160457955750905782471933)
    ·
      refine ⟨12810171733406589668426975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34160457955750905782471933 12810171733406589668426975)
      ·
        refine ⟨19215257600109884502640463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12810171733406589668426975 19215257600109884502640463)
        ·
          refine ⟨28822886400164826753960695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19215257600109884502640463 28822886400164826753960695)
          ·
            refine ⟨43234329600247240130941043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28822886400164826753960695 43234329600247240130941043)
            ·
              refine ⟨64851494400370860196411565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43234329600247240130941043 64851494400370860196411565)
              ·
                refine ⟨24319310400139072573654337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64851494400370860196411565 24319310400139072573654337)
                ·
                  refine ⟨18239482800104304430240753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24319310400139072573654337 18239482800104304430240753)
                  ·
                    refine ⟨13679612100078228322680565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18239482800104304430240753 13679612100078228322680565)
                    ·
                      refine ⟨1282463634382333905251303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13679612100078228322680565 1282463634382333905251303)
                      ·
                        rfl

theorem cell23_2497589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2497589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497589 prefixEnd_2497589 := by exact prefixLift 2497589
  have htrace : WordTrace (prefixWord ++ tailWord_2497589) baseStart_2497589 baseEnd_2497589 := by
    simpa [prefixWord, tailWord_2497589, baseEnd_2497589] using wordTrace_append hprefix tailTrace_2497589
  have hstable : (prefixWord ++ tailWord_2497589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497589).length < 2 ^ (prefixWord ++ tailWord_2497589).sum := by decide
  have hdescent : baseEnd_2497589 < baseStart_2497589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497603 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 1, 3, 2]
def baseStart_2497603 : Nat := 118140960795 + 2497603 * 2 ^ 59
def prefixEnd_2497603 : Nat := 4983230072969 + 3 ^ 40 * 2497603 * 2
def baseEnd_2497603 : Nat := 1282470823111496850476239

theorem tailTrace_2497603 : CollatzResearch.WordTrace tailWord_2497603 prefixEnd_2497603 1282470823111496850476239 := by
  unfold tailWord_2497603
  simp only [CollatzResearch.WordTrace]
  refine ⟨91095065170618362477601463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60730043447078908318400975 91095065170618362477601463)
  ·
    refine ⟨136642597755927543716402195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91095065170618362477601463 136642597755927543716402195)
    ·
      refine ⟨204963896633891315574603293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136642597755927543716402195 204963896633891315574603293)
      ·
        refine ⟨76861461237709243340476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204963896633891315574603293 76861461237709243340476235)
        ·
          refine ⟨115292191856563865010714353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76861461237709243340476235 115292191856563865010714353)
          ·
            refine ⟨86469143892422898758035765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115292191856563865010714353 86469143892422898758035765)
            ·
              refine ⟨8106482239914646758565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86469143892422898758035765 8106482239914646758565853)
              ·
                refine ⟨3039930839967992534462195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8106482239914646758565853 3039930839967992534462195)
                ·
                  refine ⟨4559896259951988801693293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039930839967992534462195 4559896259951988801693293)
                  ·
                    refine ⟨1709961097481995800634985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4559896259951988801693293 1709961097481995800634985)
                    ·
                      refine ⟨1282470823111496850476239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709961097481995800634985 1282470823111496850476239)
                      ·
                        rfl

theorem cell23_2497603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_2497603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497603 prefixEnd_2497603 := by exact prefixLift 2497603
  have htrace : WordTrace (prefixWord ++ tailWord_2497603) baseStart_2497603 baseEnd_2497603 := by
    simpa [prefixWord, tailWord_2497603, baseEnd_2497603] using wordTrace_append hprefix tailTrace_2497603
  have hstable : (prefixWord ++ tailWord_2497603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497603).length < 2 ^ (prefixWord ++ tailWord_2497603).sum := by decide
  have hdescent : baseEnd_2497603 < baseStart_2497603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497616 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2]
def baseStart_2497616 : Nat := 118140960795 + 2497616 * 2 ^ 59
def prefixEnd_2497616 : Nat := 4983230072969 + 3 ^ 40 * 2497616 * 2
def baseEnd_2497616 : Nat := 1282477498360005299613679

theorem tailTrace_2497616 : CollatzResearch.WordTrace tailWord_2497616 prefixEnd_2497616 1282477498360005299613679 := by
  unfold tailWord_2497616
  simp only [CollatzResearch.WordTrace]
  refine ⟨45547769659785632848912351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60730359546380843798549801 45547769659785632848912351)
  ·
    refine ⟨68321654489678449273368527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45547769659785632848912351 68321654489678449273368527)
    ·
      refine ⟨102482481734517673910052791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68321654489678449273368527 102482481734517673910052791)
      ·
        refine ⟨153723722601776510865079187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102482481734517673910052791 153723722601776510865079187)
        ·
          refine ⟨230585583902664766297618781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153723722601776510865079187 230585583902664766297618781)
          ·
            refine ⟨86469593963499287361607043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230585583902664766297618781 86469593963499287361607043)
            ·
              refine ⟨129704390945248931042410565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86469593963499287361607043 129704390945248931042410565)
              ·
                refine ⟨24319573302234174570451981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129704390945248931042410565 24319573302234174570451981)
                ·
                  refine ⟨9119839988337815463919493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24319573302234174570451981 9119839988337815463919493)
                  ·
                    refine ⟨1709969997813340399484905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9119839988337815463919493 1709969997813340399484905)
                    ·
                      refine ⟨1282477498360005299613679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709969997813340399484905 1282477498360005299613679)
                      ·
                        rfl

theorem cell23_2497616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 4, 2].length) (baseStart_2497616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497616 prefixEnd_2497616 := by exact prefixLift 2497616
  have htrace : WordTrace (prefixWord ++ tailWord_2497616) baseStart_2497616 baseEnd_2497616 := by
    simpa [prefixWord, tailWord_2497616, baseEnd_2497616] using wordTrace_append hprefix tailTrace_2497616
  have hstable : (prefixWord ++ tailWord_2497616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497616).length < 2 ^ (prefixWord ++ tailWord_2497616).sum := by decide
  have hdescent : baseEnd_2497616 < baseStart_2497616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497633 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_2497633 : Nat := 118140960795 + 2497633 * 2 ^ 59
def prefixEnd_2497633 : Nat := 4983230072969 + 3 ^ 40 * 2497633 * 2
def baseEnd_2497633 : Nat := 1282486227531131733101101

theorem tailTrace_2497633 : CollatzResearch.WordTrace tailWord_2497633 prefixEnd_2497633 1282486227531131733101101 := by
  unfold tailWord_2497633
  simp only [CollatzResearch.WordTrace]
  refine ⟨91096159360509677601193553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60730772907006451734129035 91096159360509677601193553)
  ·
    refine ⟨68322119520382258200895165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91096159360509677601193553 68322119520382258200895165)
    ·
      refine ⟨25620794820143346825335687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68322119520382258200895165 25620794820143346825335687)
      ·
        refine ⟨38431192230215020238003531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620794820143346825335687 38431192230215020238003531)
        ·
          refine ⟨57646788345322530357005297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38431192230215020238003531 57646788345322530357005297)
          ·
            refine ⟨43235091258991897767753973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57646788345322530357005297 43235091258991897767753973)
            ·
              refine ⟨4053289805530490415726935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43235091258991897767753973 4053289805530490415726935)
              ·
                refine ⟨6079934708295735623590403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053289805530490415726935 6079934708295735623590403)
                ·
                  refine ⟨9119902062443603435385605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6079934708295735623590403 9119902062443603435385605)
                  ·
                    refine ⟨1709981636708175644134801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9119902062443603435385605 1709981636708175644134801)
                    ·
                      refine ⟨1282486227531131733101101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1709981636708175644134801 1282486227531131733101101)
                      ·
                        rfl

theorem cell23_2497633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_2497633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497633 prefixEnd_2497633 := by exact prefixLift 2497633
  have htrace : WordTrace (prefixWord ++ tailWord_2497633) baseStart_2497633 baseEnd_2497633 := by
    simpa [prefixWord, tailWord_2497633, baseEnd_2497633] using wordTrace_append hprefix tailTrace_2497633
  have hstable : (prefixWord ++ tailWord_2497633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497633).length < 2 ^ (prefixWord ++ tailWord_2497633).sum := by decide
  have hdescent : baseEnd_2497633 < baseStart_2497633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497699 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 8]
def baseStart_2497699 : Nat := 118140960795 + 2497699 * 2 ^ 59
def prefixEnd_2497699 : Nat := 4983230072969 + 3 ^ 40 * 2497699 * 2
def baseEnd_2497699 : Nat := 427506705751442824958599

theorem tailTrace_2497699 : CollatzResearch.WordTrace tailWord_2497699 prefixEnd_2497699 427506705751442824958599 := by
  unfold tailWord_2497699
  simp only [CollatzResearch.WordTrace]
  refine ⟨91098566578270570873096151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60732377718847047248730767 91098566578270570873096151)
  ·
    refine ⟨136647849867405856309644227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91098566578270570873096151 136647849867405856309644227)
    ·
      refine ⟨204971774801108784464466341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136647849867405856309644227 204971774801108784464466341)
      ·
        refine ⟨38432207775207897087087439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204971774801108784464466341 38432207775207897087087439)
        ·
          refine ⟨57648311662811845630631159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38432207775207897087087439 57648311662811845630631159)
          ·
            refine ⟨86472467494217768445946739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57648311662811845630631159 86472467494217768445946739)
            ·
              refine ⟨129708701241326652668920109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86472467494217768445946739 129708701241326652668920109)
              ·
                refine ⟨48640762965497494750845041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129708701241326652668920109 48640762965497494750845041)
                ·
                  refine ⟨36480572224123121063133781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48640762965497494750845041 36480572224123121063133781)
                  ·
                    refine ⟨427506705751442824958599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36480572224123121063133781 427506705751442824958599)
                    ·
                      rfl

theorem cell23_2497699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_2497699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497699 prefixEnd_2497699 := by exact prefixLift 2497699
  have htrace : WordTrace (prefixWord ++ tailWord_2497699) baseStart_2497699 baseEnd_2497699 := by
    simpa [prefixWord, tailWord_2497699, baseEnd_2497699] using wordTrace_append hprefix tailTrace_2497699
  have hstable : (prefixWord ++ tailWord_2497699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497699).length < 2 ^ (prefixWord ++ tailWord_2497699).sum := by decide
  have hdescent : baseEnd_2497699 < baseStart_2497699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497703 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2497703 : Nat := 118140960795 + 2497703 * 2 ^ 59
def prefixEnd_2497703 : Nat := 4983230072969 + 3 ^ 40 * 2497703 * 2
def baseEnd_2497703 : Nat := 427507390392315486408593

theorem tailTrace_2497703 : CollatzResearch.WordTrace tailWord_2497703 prefixEnd_2497703 427507390392315486408593 := by
  unfold tailWord_2497703
  simp only [CollatzResearch.WordTrace]
  refine ⟨91098712470256079556241763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60732474980170719704161175 91098712470256079556241763)
  ·
    refine ⟨136648068705384119334362645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91098712470256079556241763 136648068705384119334362645)
    ·
      refine ⟨6405378220564880593798249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136648068705384119334362645 6405378220564880593798249)
      ·
        refine ⟨4804033665423660445348687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405378220564880593798249 4804033665423660445348687)
        ·
          refine ⟨7206050498135490668023031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804033665423660445348687 7206050498135490668023031)
          ·
            refine ⟨10809075747203236002034547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206050498135490668023031 10809075747203236002034547)
            ·
              refine ⟨16213613620804854003051821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10809075747203236002034547 16213613620804854003051821)
              ·
                refine ⟨6080105107801820251144433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16213613620804854003051821 6080105107801820251144433)
                ·
                  refine ⟨4560078830851365188358325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080105107801820251144433 4560078830851365188358325)
                  ·
                    refine ⟨427507390392315486408593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4560078830851365188358325 427507390392315486408593)
                    ·
                      rfl

theorem cell23_2497703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2497703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497703 prefixEnd_2497703 := by exact prefixLift 2497703
  have htrace : WordTrace (prefixWord ++ tailWord_2497703) baseStart_2497703 baseEnd_2497703 := by
    simpa [prefixWord, tailWord_2497703, baseEnd_2497703] using wordTrace_append hprefix tailTrace_2497703
  have hstable : (prefixWord ++ tailWord_2497703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497703).length < 2 ^ (prefixWord ++ tailWord_2497703).sum := by decide
  have hdescent : baseEnd_2497703 < baseStart_2497703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497734 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2497734 : Nat := 118140960795 + 2497734 * 2 ^ 59
def prefixEnd_2497734 : Nat := 4983230072969 + 3 ^ 40 * 2497734 * 2
def baseEnd_2497734 : Nat := 1282538089077235837938137

theorem tailTrace_2497734 : CollatzResearch.WordTrace tailWord_2497734 prefixEnd_2497734 1282538089077235837938137 := by
  unfold tailWord_2497734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846870097910742870331883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60733228755429181233746837 2846870097910742870331883)
  ·
    refine ⟨4270305146866114305497825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2846870097910742870331883 4270305146866114305497825)
    ·
      refine ⟨3202728860149585729123369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4270305146866114305497825 3202728860149585729123369)
      ·
        refine ⟨2402046645112189296842527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3202728860149585729123369 2402046645112189296842527)
        ·
          refine ⟨3603069967668283945263791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402046645112189296842527 3603069967668283945263791)
          ·
            refine ⟨5404604951502425917895687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603069967668283945263791 5404604951502425917895687)
            ·
              refine ⟨8106907427253638876843531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404604951502425917895687 8106907427253638876843531)
              ·
                refine ⟨12160361140880458315265297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8106907427253638876843531 12160361140880458315265297)
                ·
                  refine ⟨9120270855660343736448973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12160361140880458315265297 9120270855660343736448973)
                  ·
                    refine ⟨3420101570872628901168365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9120270855660343736448973 3420101570872628901168365)
                    ·
                      refine ⟨1282538089077235837938137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420101570872628901168365 1282538089077235837938137)
                      ·
                        rfl

theorem cell23_2497734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2497734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497734 prefixEnd_2497734 := by exact prefixLift 2497734
  have htrace : WordTrace (prefixWord ++ tailWord_2497734) baseStart_2497734 baseEnd_2497734 := by
    simpa [prefixWord, tailWord_2497734, baseEnd_2497734] using wordTrace_append hprefix tailTrace_2497734
  have hstable : (prefixWord ++ tailWord_2497734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497734).length < 2 ^ (prefixWord ++ tailWord_2497734).sum := by decide
  have hdescent : baseEnd_2497734 < baseStart_2497734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497757 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2497757 : Nat := 118140960795 + 2497757 * 2 ^ 59
def prefixEnd_2497757 : Nat := 4983230072969 + 3 ^ 40 * 2497757 * 2
def baseEnd_2497757 : Nat := 1282549899132289247950531

theorem tailTrace_2497757 : CollatzResearch.WordTrace tailWord_2497757 prefixEnd_2497757 1282549899132289247950531 := by
  unfold tailWord_2497757
  simp only [CollatzResearch.WordTrace]
  refine ⟨91100682012060446778707525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60733788008040297852471683 91100682012060446778707525)
  ·
    refine ⟨17081377877261333771007661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91100682012060446778707525 17081377877261333771007661)
    ·
      refine ⟨6405516703973000164127873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17081377877261333771007661 6405516703973000164127873)
      ·
        refine ⟨4804137527979750123095905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405516703973000164127873 4804137527979750123095905)
        ·
          refine ⟨3603103145984812592321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4804137527979750123095905 3603103145984812592321929)
          ·
            refine ⟨2702327359488609444241447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3603103145984812592321929 2702327359488609444241447)
            ·
              refine ⟨4053491039232914166362171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702327359488609444241447 4053491039232914166362171)
              ·
                refine ⟨6080236558849371249543257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053491039232914166362171 6080236558849371249543257)
                ·
                  refine ⟨4560177419137028437157443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080236558849371249543257 4560177419137028437157443)
                  ·
                    refine ⟨6840266128705542655736165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4560177419137028437157443 6840266128705542655736165)
                    ·
                      refine ⟨1282549899132289247950531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6840266128705542655736165 1282549899132289247950531)
                      ·
                        rfl

theorem cell23_2497757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2497757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497757 prefixEnd_2497757 := by exact prefixLift 2497757
  have htrace : WordTrace (prefixWord ++ tailWord_2497757) baseStart_2497757 baseEnd_2497757 := by
    simpa [prefixWord, tailWord_2497757, baseEnd_2497757] using wordTrace_append hprefix tailTrace_2497757
  have hstable : (prefixWord ++ tailWord_2497757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497757).length < 2 ^ (prefixWord ++ tailWord_2497757).sum := by decide
  have hdescent : baseEnd_2497757 < baseStart_2497757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497760 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_2497760 : Nat := 118140960795 + 2497760 * 2 ^ 59
def prefixEnd_2497760 : Nat := 4983230072969 + 3 ^ 40 * 2497760 * 2
def baseEnd_2497760 : Nat := 1282551439574252736213017

theorem tailTrace_2497760 : CollatzResearch.WordTrace tailWord_2497760 prefixEnd_2497760 1282551439574252736213017 := by
  unfold tailWord_2497760
  simp only [CollatzResearch.WordTrace]
  refine ⟨45550395715524789145533367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60733860954033052194044489 45550395715524789145533367)
  ·
    refine ⟨68325593573287183718300051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45550395715524789145533367 68325593573287183718300051)
    ·
      refine ⟨102488390359930775577450077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68325593573287183718300051 102488390359930775577450077)
      ·
        refine ⟨38433146384974040841543779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102488390359930775577450077 38433146384974040841543779)
        ·
          refine ⟨57649719577461061262315669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38433146384974040841543779 57649719577461061262315669)
          ·
            refine ⟨2702330605193487246671047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57649719577461061262315669 2702330605193487246671047)
            ·
              refine ⟨4053495907790230870006571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702330605193487246671047 4053495907790230870006571)
              ·
                refine ⟨6080243861685346305009857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053495907790230870006571 6080243861685346305009857)
                ·
                  refine ⟨4560182896264009728757393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080243861685346305009857 4560182896264009728757393)
                  ·
                    refine ⟨3420137172198007296568045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560182896264009728757393 3420137172198007296568045)
                    ·
                      refine ⟨1282551439574252736213017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420137172198007296568045 1282551439574252736213017)
                      ·
                        rfl

theorem cell23_2497760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_2497760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497760 prefixEnd_2497760 := by exact prefixLift 2497760
  have htrace : WordTrace (prefixWord ++ tailWord_2497760) baseStart_2497760 baseEnd_2497760 := by
    simpa [prefixWord, tailWord_2497760, baseEnd_2497760] using wordTrace_append hprefix tailTrace_2497760
  have hstable : (prefixWord ++ tailWord_2497760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497760).length < 2 ^ (prefixWord ++ tailWord_2497760).sum := by decide
  have hdescent : baseEnd_2497760 < baseStart_2497760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497813 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_2497813 : Nat := 118140960795 + 2497813 * 2 ^ 59
def prefixEnd_2497813 : Nat := 4983230072969 + 3 ^ 40 * 2497813 * 2
def baseEnd_2497813 : Nat := 1282578654048941028850273

theorem tailTrace_2497813 : CollatzResearch.WordTrace tailWord_2497813 prefixEnd_2497813 1282578654048941028850273 := by
  unfold tailWord_2497813
  simp only [CollatzResearch.WordTrace]
  refine ⟨91102724499857568342746093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60735149666571712228497395 91102724499857568342746093)
  ·
    refine ⟨34163521687446588128529785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91102724499857568342746093 34163521687446588128529785)
    ·
      refine ⟨25622641265584941096397339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34163521687446588128529785 25622641265584941096397339)
      ·
        refine ⟨38433961898377411644596009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25622641265584941096397339 38433961898377411644596009)
        ·
          refine ⟨28825471423783058733447007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38433961898377411644596009 28825471423783058733447007)
          ·
            refine ⟨43238207135674588100170511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28825471423783058733447007 43238207135674588100170511)
            ·
              refine ⟨64857310703511882150255767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43238207135674588100170511 64857310703511882150255767)
              ·
                refine ⟨97285966055267823225383651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64857310703511882150255767 97285966055267823225383651)
                ·
                  refine ⟨145928949082901734838075477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97285966055267823225383651 145928949082901734838075477)
                  ·
                    refine ⟨1710104872065254705133697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 145928949082901734838075477 1710104872065254705133697)
                    ·
                      refine ⟨1282578654048941028850273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710104872065254705133697 1282578654048941028850273)
                      ·
                        rfl

theorem cell23_2497813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_2497813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497813 prefixEnd_2497813 := by exact prefixLift 2497813
  have htrace : WordTrace (prefixWord ++ tailWord_2497813) baseStart_2497813 baseEnd_2497813 := by
    simpa [prefixWord, tailWord_2497813, baseEnd_2497813] using wordTrace_append hprefix tailTrace_2497813
  have hstable : (prefixWord ++ tailWord_2497813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497813).length < 2 ^ (prefixWord ++ tailWord_2497813).sum := by decide
  have hdescent : baseEnd_2497813 < baseStart_2497813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497856 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2497856 : Nat := 118140960795 + 2497856 * 2 ^ 59
def prefixEnd_2497856 : Nat := 4983230072969 + 3 ^ 40 * 2497856 * 2
def baseEnd_2497856 : Nat := 1282600733717084360612575

theorem tailTrace_2497856 : CollatzResearch.WordTrace tailWord_2497856 prefixEnd_2497856 1282600733717084360612575 := by
  unfold tailWord_2497856
  simp only [CollatzResearch.WordTrace]
  refine ⟨45552146419350893343280711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60736195225801191124374281 45552146419350893343280711)
  ·
    refine ⟨68328219629026340014921067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45552146419350893343280711 68328219629026340014921067)
    ·
      refine ⟨102492329443539510022381601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68328219629026340014921067 102492329443539510022381601)
      ·
        refine ⟨76869247082654632516786201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102492329443539510022381601 76869247082654632516786201)
        ·
          refine ⟨57651935311990974387589651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76869247082654632516786201 57651935311990974387589651)
          ·
            refine ⟨86477902967986461581384477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57651935311990974387589651 86477902967986461581384477)
            ·
              refine ⟨32429213612994923093019179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86477902967986461581384477 32429213612994923093019179)
              ·
                refine ⟨48643820419492384639528769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32429213612994923093019179 48643820419492384639528769)
                ·
                  refine ⟨36482865314619288479646577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48643820419492384639528769 36482865314619288479646577)
                  ·
                    refine ⟨27362148985964466359734933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36482865314619288479646577 27362148985964466359734933)
                    ·
                      refine ⟨1282600733717084360612575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27362148985964466359734933 1282600733717084360612575)
                      ·
                        rfl

theorem cell23_2497856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2497856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497856 prefixEnd_2497856 := by exact prefixLift 2497856
  have htrace : WordTrace (prefixWord ++ tailWord_2497856) baseStart_2497856 baseEnd_2497856 := by
    simpa [prefixWord, tailWord_2497856, baseEnd_2497856] using wordTrace_append hprefix tailTrace_2497856
  have hstable : (prefixWord ++ tailWord_2497856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497856).length < 2 ^ (prefixWord ++ tailWord_2497856).sum := by decide
  have hdescent : baseEnd_2497856 < baseStart_2497856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497857 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2497857 : Nat := 118140960795 + 2497857 * 2 ^ 59
def prefixEnd_2497857 : Nat := 4983230072969 + 3 ^ 40 * 2497857 * 2
def baseEnd_2497857 : Nat := 427533749065912952233357

theorem tailTrace_2497857 : CollatzResearch.WordTrace tailWord_2497857 prefixEnd_2497857 427533749065912952233357 := by
  unfold tailWord_2497857
  simp only [CollatzResearch.WordTrace]
  refine ⟨91104329311698163857347825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60736219541132109238231883 91104329311698163857347825)
  ·
    refine ⟨68328246983773622893010869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91104329311698163857347825 68328246983773622893010869)
    ·
      refine ⟨6405773154728777146219769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68328246983773622893010869 6405773154728777146219769)
      ·
        refine ⟨4804329866046582859664827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405773154728777146219769 4804329866046582859664827)
        ·
          refine ⟨7206494799069874289497241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804329866046582859664827 7206494799069874289497241)
          ·
            refine ⟨5404871099302405717122931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7206494799069874289497241 5404871099302405717122931)
            ·
              refine ⟨8107306648953608575684397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404871099302405717122931 8107306648953608575684397)
              ·
                refine ⟨3040239993357603215881649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8107306648953608575684397 3040239993357603215881649)
                ·
                  refine ⟨2280179995018202411911237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040239993357603215881649 2280179995018202411911237)
                  ·
                    refine ⟨427533749065912952233357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280179995018202411911237 427533749065912952233357)
                    ·
                      rfl

theorem cell23_2497857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2497857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497857 prefixEnd_2497857 := by exact prefixLift 2497857
  have htrace : WordTrace (prefixWord ++ tailWord_2497857) baseStart_2497857 baseEnd_2497857 := by
    simpa [prefixWord, tailWord_2497857, baseEnd_2497857] using wordTrace_append hprefix tailTrace_2497857
  have hstable : (prefixWord ++ tailWord_2497857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497857).length < 2 ^ (prefixWord ++ tailWord_2497857).sum := by decide
  have hdescent : baseEnd_2497857 < baseStart_2497857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497860 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2497860 : Nat := 118140960795 + 2497860 * 2 ^ 59
def prefixEnd_2497860 : Nat := 4983230072969 + 3 ^ 40 * 2497860 * 2
def baseEnd_2497860 : Nat := 1282602787639702344962557

theorem tailTrace_2497860 : CollatzResearch.WordTrace tailWord_2497860 prefixEnd_2497860 1282602787639702344962557 := by
  unfold tailWord_2497860
  simp only [CollatzResearch.WordTrace]
  refine ⟨45552219365343647684853517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60736292487124863579804689 45552219365343647684853517)
  ·
    refine ⟨17082082262003867881820069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45552219365343647684853517 17082082262003867881820069)
    ·
      refine ⟨3202890424125725227841263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17082082262003867881820069 3202890424125725227841263)
      ·
        refine ⟨4804335636188587841761895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202890424125725227841263 4804335636188587841761895)
        ·
          refine ⟨7206503454282881762642843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804335636188587841761895 7206503454282881762642843)
          ·
            refine ⟨10809755181424322643964265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206503454282881762642843 10809755181424322643964265)
            ·
              refine ⟨8107316386068241982973199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10809755181424322643964265 8107316386068241982973199)
              ·
                refine ⟨12160974579102362974459799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107316386068241982973199 12160974579102362974459799)
                ·
                  refine ⟨18241461868653544461689699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12160974579102362974459799 18241461868653544461689699)
                  ·
                    refine ⟨27362192802980316692534549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18241461868653544461689699 27362192802980316692534549)
                    ·
                      refine ⟨1282602787639702344962557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27362192802980316692534549 1282602787639702344962557)
                      ·
                        rfl

theorem cell23_2497860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2497860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497860 prefixEnd_2497860 := by exact prefixLift 2497860
  have htrace : WordTrace (prefixWord ++ tailWord_2497860) baseStart_2497860 baseEnd_2497860 := by
    simpa [prefixWord, tailWord_2497860, baseEnd_2497860] using wordTrace_append hprefix tailTrace_2497860
  have hstable : (prefixWord ++ tailWord_2497860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497860).length < 2 ^ (prefixWord ++ tailWord_2497860).sum := by decide
  have hdescent : baseEnd_2497860 < baseStart_2497860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497878 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2497878 : Nat := 118140960795 + 2497878 * 2 ^ 59
def prefixEnd_2497878 : Nat := 4983230072969 + 3 ^ 40 * 2497878 * 2
def baseEnd_2497878 : Nat := 427537343430494424845825

theorem tailTrace_2497878 : CollatzResearch.WordTrace tailWord_2497878 prefixEnd_2497878 427537343430494424845825 := by
  unfold tailWord_2497878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694068452788880277741393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60736730163081389629241525 5694068452788880277741393)
  ·
    refine ⟨4270551339591660208306045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5694068452788880277741393 4270551339591660208306045)
    ·
      refine ⟨1601456752346872578114767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4270551339591660208306045 1601456752346872578114767)
      ·
        refine ⟨2402185128520308867172151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601456752346872578114767 2402185128520308867172151)
        ·
          refine ⟨3603277692780463300758227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402185128520308867172151 3603277692780463300758227)
          ·
            refine ⟨5404916539170694951137341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603277692780463300758227 5404916539170694951137341)
            ·
              refine ⟨2026843702189010606676503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5404916539170694951137341 2026843702189010606676503)
              ·
                refine ⟨3040265553283515910014755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2026843702189010606676503 3040265553283515910014755)
                ·
                  refine ⟨4560398329925273865022133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040265553283515910014755 4560398329925273865022133)
                  ·
                    refine ⟨427537343430494424845825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4560398329925273865022133 427537343430494424845825)
                    ·
                      rfl

theorem cell23_2497878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2497878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497878 prefixEnd_2497878 := by exact prefixLift 2497878
  have htrace : WordTrace (prefixWord ++ tailWord_2497878) baseStart_2497878 baseEnd_2497878 := by
    simpa [prefixWord, tailWord_2497878, baseEnd_2497878] using wordTrace_append hprefix tailTrace_2497878
  have hstable : (prefixWord ++ tailWord_2497878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497878).length < 2 ^ (prefixWord ++ tailWord_2497878).sum := by decide
  have hdescent : baseEnd_2497878 < baseStart_2497878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497948 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2497948 : Nat := 118140960795 + 2497948 * 2 ^ 59
def prefixEnd_2497948 : Nat := 4983230072969 + 3 ^ 40 * 2497948 * 2
def baseEnd_2497948 : Nat := 1282647973937298000662153

theorem tailTrace_2497948 : CollatzResearch.WordTrace tailWord_2497948 prefixEnd_2497948 1282647973937298000662153 := by
  unfold tailWord_2497948
  simp only [CollatzResearch.WordTrace]
  refine ⟨45553824177184243199455249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60738432236245657599273665 45553824177184243199455249)
  ·
    refine ⟨34165368132888182399591437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45553824177184243199455249 34165368132888182399591437)
    ·
      refine ⟨12812013049833068399846789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34165368132888182399591437 12812013049833068399846789)
      ·
        refine ⟨2402252446843700324971273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12812013049833068399846789 2402252446843700324971273)
        ·
          refine ⟨1801689335132775243728455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402252446843700324971273 1801689335132775243728455)
          ·
            refine ⟨2702534002699162865592683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801689335132775243728455 2702534002699162865592683)
            ·
              refine ⟨4053801004048744298389025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702534002699162865592683 4053801004048744298389025)
              ·
                refine ⟨3040350753036558223791769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053801004048744298389025 3040350753036558223791769)
                ·
                  refine ⟨2280263064777418667843827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040350753036558223791769 2280263064777418667843827)
                  ·
                    refine ⟨3420394597166128001765741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2280263064777418667843827 3420394597166128001765741)
                    ·
                      refine ⟨1282647973937298000662153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420394597166128001765741 1282647973937298000662153)
                      ·
                        rfl

theorem cell23_2497948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2497948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497948 prefixEnd_2497948 := by exact prefixLift 2497948
  have htrace : WordTrace (prefixWord ++ tailWord_2497948) baseStart_2497948 baseEnd_2497948 := by
    simpa [prefixWord, tailWord_2497948, baseEnd_2497948] using wordTrace_append hprefix tailTrace_2497948
  have hstable : (prefixWord ++ tailWord_2497948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497948).length < 2 ^ (prefixWord ++ tailWord_2497948).sum := by decide
  have hdescent : baseEnd_2497948 < baseStart_2497948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497954 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_2497954 : Nat := 118140960795 + 2497954 * 2 ^ 59
def prefixEnd_2497954 : Nat := 4983230072969 + 3 ^ 40 * 2497954 * 2
def baseEnd_2497954 : Nat := 1282651054821224977187125

theorem tailTrace_2497954 : CollatzResearch.WordTrace tailWord_2497954 prefixEnd_2497954 1282651054821224977187125 := by
  unfold tailWord_2497954
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776966798086687355907229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60738578128231166282419277 22776966798086687355907229)
  ·
    refine ⟨8541362549282507758465211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22776966798086687355907229 8541362549282507758465211)
    ·
      refine ⟨12812043823923761637697817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541362549282507758465211 12812043823923761637697817)
      ·
        refine ⟨9609032867942821228273363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12812043823923761637697817 9609032867942821228273363)
        ·
          refine ⟨14413549301914231842410045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609032867942821228273363 14413549301914231842410045)
          ·
            refine ⟨5405080988217836940903767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14413549301914231842410045 5405080988217836940903767)
            ·
              refine ⟨8107621482326755411355651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405080988217836940903767 8107621482326755411355651)
              ·
                refine ⟨12161432223490133117033477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107621482326755411355651 12161432223490133117033477)
                ·
                  refine ⟨2280268541904399959443777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12161432223490133117033477 2280268541904399959443777)
                  ·
                    refine ⟨1710201406428299969582833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280268541904399959443777 1710201406428299969582833)
                    ·
                      refine ⟨1282651054821224977187125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710201406428299969582833 1282651054821224977187125)
                      ·
                        rfl

theorem cell23_2497954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_2497954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2497954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2497954 prefixEnd_2497954 := by exact prefixLift 2497954
  have htrace : WordTrace (prefixWord ++ tailWord_2497954) baseStart_2497954 baseEnd_2497954 := by
    simpa [prefixWord, tailWord_2497954, baseEnd_2497954] using wordTrace_append hprefix tailTrace_2497954
  have hstable : (prefixWord ++ tailWord_2497954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497954).length < 2 ^ (prefixWord ++ tailWord_2497954).sum := by decide
  have hdescent : baseEnd_2497954 < baseStart_2497954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498010 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2498010 : Nat := 118140960795 + 2498010 * 2 ^ 59
def prefixEnd_2498010 : Nat := 4983230072969 + 3 ^ 40 * 2498010 * 2
def baseEnd_2498010 : Nat := 1282679809737876758086867

theorem tailTrace_2498010 : CollatzResearch.WordTrace tailWord_2498010 prefixEnd_2498010 1282679809737876758086867 := by
  unfold tailWord_2498010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777477420035967746916871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60739939786762580658444989 22777477420035967746916871)
  ·
    refine ⟨34166216130053951620375307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22777477420035967746916871 34166216130053951620375307)
    ·
      refine ⟨51249324195080927430562961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34166216130053951620375307 51249324195080927430562961)
      ·
        refine ⟨38436993146310695572922221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51249324195080927430562961 38436993146310695572922221)
        ·
          refine ⟨14413872429866510839845833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38436993146310695572922221 14413872429866510839845833)
          ·
            refine ⟨10810404322399883129884375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14413872429866510839845833 10810404322399883129884375)
            ·
              refine ⟨16215606483599824694826563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10810404322399883129884375 16215606483599824694826563)
              ·
                refine ⟨24323409725399737042239845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16215606483599824694826563 24323409725399737042239845)
                ·
                  refine ⟨4560639323512450695419971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24323409725399737042239845 4560639323512450695419971)
                  ·
                    refine ⟨6840958985268676043129957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4560639323512450695419971 6840958985268676043129957)
                    ·
                      refine ⟨1282679809737876758086867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6840958985268676043129957 1282679809737876758086867)
                      ·
                        rfl

theorem cell23_2498010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2498010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498010 prefixEnd_2498010 := by exact prefixLift 2498010
  have htrace : WordTrace (prefixWord ++ tailWord_2498010) baseStart_2498010 baseEnd_2498010 := by
    simpa [prefixWord, tailWord_2498010, baseEnd_2498010] using wordTrace_append hprefix tailTrace_2498010
  have hstable : (prefixWord ++ tailWord_2498010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498010).length < 2 ^ (prefixWord ++ tailWord_2498010).sum := by decide
  have hdescent : baseEnd_2498010 < baseStart_2498010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498053 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2498053 : Nat := 118140960795 + 2498053 * 2 ^ 59
def prefixEnd_2498053 : Nat := 4983230072969 + 3 ^ 40 * 2498053 * 2
def baseEnd_2498053 : Nat := 1282701889406020089849169

theorem tailTrace_2498053 : CollatzResearch.WordTrace tailWord_2498053 prefixEnd_2498053 1282701889406020089849169 := by
  unfold tailWord_2498053
  simp only [CollatzResearch.WordTrace]
  refine ⟨91111478018988089331482813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60740985345992059554321875 91111478018988089331482813)
  ·
    refine ⟨34166804257120533499306055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91111478018988089331482813 34166804257120533499306055)
    ·
      refine ⟨51250206385680800248959083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34166804257120533499306055 51250206385680800248959083)
      ·
        refine ⟨76875309578521200373438625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51250206385680800248959083 76875309578521200373438625)
        ·
          refine ⟨57656482183890900280078969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76875309578521200373438625 57656482183890900280078969)
          ·
            refine ⟨43242361637918175210059227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57656482183890900280078969 43242361637918175210059227)
            ·
              refine ⟨64863542456877262815088841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43242361637918175210059227 64863542456877262815088841)
              ·
                refine ⟨48647656842657947111316631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64863542456877262815088841 48647656842657947111316631)
                ·
                  refine ⟨72971485263986920666974947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48647656842657947111316631 72971485263986920666974947)
                  ·
                    refine ⟨109457227895980381000462421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72971485263986920666974947 109457227895980381000462421)
                    ·
                      refine ⟨1282701889406020089849169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 109457227895980381000462421 1282701889406020089849169)
                      ·
                        rfl

theorem cell23_2498053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2498053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498053 prefixEnd_2498053 := by exact prefixLift 2498053
  have htrace : WordTrace (prefixWord ++ tailWord_2498053) baseStart_2498053 baseEnd_2498053 := by
    simpa [prefixWord, tailWord_2498053, baseEnd_2498053] using wordTrace_append hprefix tailTrace_2498053
  have hstable : (prefixWord ++ tailWord_2498053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498053).length < 2 ^ (prefixWord ++ tailWord_2498053).sum := by decide
  have hdescent : baseEnd_2498053 < baseStart_2498053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498073 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2498073 : Nat := 118140960795 + 2498073 * 2 ^ 59
def prefixEnd_2498073 : Nat := 4983230072969 + 3 ^ 40 * 2498073 * 2
def baseEnd_2498073 : Nat := 1282712159019110011599077

theorem tailTrace_2498073 : CollatzResearch.WordTrace tailWord_2498073 prefixEnd_2498073 1282712159019110011599077 := by
  unfold tailWord_2498073
  simp only [CollatzResearch.WordTrace]
  refine ⟨91112207478915632747210873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60741471652610421831473915 91112207478915632747210873)
  ·
    refine ⟨68334155609186724560408155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91112207478915632747210873 68334155609186724560408155)
    ·
      refine ⟨102501233413780086840612233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68334155609186724560408155 102501233413780086840612233)
      ·
        refine ⟨76875925060335065130459175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102501233413780086840612233 76875925060335065130459175)
        ·
          refine ⟨115313887590502597695688763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76875925060335065130459175 115313887590502597695688763)
          ·
            refine ⟨172970831385753896543533145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115313887590502597695688763 172970831385753896543533145)
            ·
              refine ⟨129728123539315422407649859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172970831385753896543533145 129728123539315422407649859)
              ·
                refine ⟨194592185308973133611474789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129728123539315422407649859 194592185308973133611474789)
                ·
                  refine ⟨36486034745432462552151523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194592185308973133611474789 36486034745432462552151523)
                  ·
                    refine ⟨54729052118148693828227285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36486034745432462552151523 54729052118148693828227285)
                    ·
                      refine ⟨1282712159019110011599077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54729052118148693828227285 1282712159019110011599077)
                      ·
                        rfl

theorem cell23_2498073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2498073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498073 prefixEnd_2498073 := by exact prefixLift 2498073
  have htrace : WordTrace (prefixWord ++ tailWord_2498073) baseStart_2498073 baseEnd_2498073 := by
    simpa [prefixWord, tailWord_2498073, baseEnd_2498073] using wordTrace_append hprefix tailTrace_2498073
  have hstable : (prefixWord ++ tailWord_2498073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498073).length < 2 ^ (prefixWord ++ tailWord_2498073).sum := by decide
  have hdescent : baseEnd_2498073 < baseStart_2498073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498090 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2498090 : Nat := 118140960795 + 2498090 * 2 ^ 59
def prefixEnd_2498090 : Nat := 4983230072969 + 3 ^ 40 * 2498090 * 2
def baseEnd_2498090 : Nat := 1282720888190236445086499

theorem tailTrace_2498090 : CollatzResearch.WordTrace tailWord_2498090 prefixEnd_2498090 1282720888190236445086499 := by
  unfold tailWord_2498090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778206879963511162644931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60741885013236029767053149 22778206879963511162644931)
  ·
    refine ⟨34167310319945266743967397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22778206879963511162644931 34167310319945266743967397)
    ·
      refine ⟨6406370684989737514493887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34167310319945266743967397 6406370684989737514493887)
      ·
        refine ⟨9609556027484606271740831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406370684989737514493887 9609556027484606271740831)
        ·
          refine ⟨14414334041226909407611247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609556027484606271740831 14414334041226909407611247)
          ·
            refine ⟨21621501061840364111416871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14414334041226909407611247 21621501061840364111416871)
            ·
              refine ⟨32432251592760546167125307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21621501061840364111416871 32432251592760546167125307)
              ·
                refine ⟨48648377389140819250687961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32432251592760546167125307 48648377389140819250687961)
                ·
                  refine ⟨36486283041855614438015971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48648377389140819250687961 36486283041855614438015971)
                  ·
                    refine ⟨54729424562783421657023957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36486283041855614438015971 54729424562783421657023957)
                    ·
                      refine ⟨1282720888190236445086499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54729424562783421657023957 1282720888190236445086499)
                      ·
                        rfl

theorem cell23_2498090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2498090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498090 prefixEnd_2498090 := by exact prefixLift 2498090
  have htrace : WordTrace (prefixWord ++ tailWord_2498090) baseStart_2498090 baseEnd_2498090 := by
    simpa [prefixWord, tailWord_2498090, baseEnd_2498090] using wordTrace_append hprefix tailTrace_2498090
  have hstable : (prefixWord ++ tailWord_2498090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498090).length < 2 ^ (prefixWord ++ tailWord_2498090).sum := by decide
  have hdescent : baseEnd_2498090 < baseStart_2498090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498094 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2498094 : Nat := 118140960795 + 2498094 * 2 ^ 59
def prefixEnd_2498094 : Nat := 4983230072969 + 3 ^ 40 * 2498094 * 2
def baseEnd_2498094 : Nat := 1282722942112854429436481

theorem tailTrace_2498094 : CollatzResearch.WordTrace tailWord_2498094 prefixEnd_2498094 1282722942112854429436481 := by
  unfold tailWord_2498094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389121676479944166715667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60741982274559702222483557 11389121676479944166715667)
  ·
    refine ⟨17083682514719916250073501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11389121676479944166715667 17083682514719916250073501)
    ·
      refine ⟨6406380943019968593777563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17083682514719916250073501 6406380943019968593777563)
      ·
        refine ⟨9609571414529952890666345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406380943019968593777563 9609571414529952890666345)
        ·
          refine ⟨7207178560897464667999759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9609571414529952890666345 7207178560897464667999759)
          ·
            refine ⟨10810767841346197001999639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207178560897464667999759 10810767841346197001999639)
            ·
              refine ⟨16216151762019295502999459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10810767841346197001999639 16216151762019295502999459)
              ·
                refine ⟨24324227643028943254499189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16216151762019295502999459 24324227643028943254499189)
                ·
                  refine ⟨2280396341533963430109299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24324227643028943254499189 2280396341533963430109299)
                  ·
                    refine ⟨3420594512300945145163949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2280396341533963430109299 3420594512300945145163949)
                    ·
                      refine ⟨1282722942112854429436481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420594512300945145163949 1282722942112854429436481)
                      ·
                        rfl

theorem cell23_2498094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2498094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498094 prefixEnd_2498094 := by exact prefixLift 2498094
  have htrace : WordTrace (prefixWord ++ tailWord_2498094) baseStart_2498094 baseEnd_2498094 := by
    simpa [prefixWord, tailWord_2498094, baseEnd_2498094] using wordTrace_append hprefix tailTrace_2498094
  have hstable : (prefixWord ++ tailWord_2498094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498094).length < 2 ^ (prefixWord ++ tailWord_2498094).sum := by decide
  have hdescent : baseEnd_2498094 < baseStart_2498094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498104 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_2498104 : Nat := 118140960795 + 2498104 * 2 ^ 59
def prefixEnd_2498104 : Nat := 4983230072969 + 3 ^ 40 * 2498104 * 2
def baseEnd_2498104 : Nat := 1282728076919399390311435

theorem tailTrace_2498104 : CollatzResearch.WordTrace tailWord_2498104 prefixEnd_2498104 1282728076919399390311435 := by
  unfold tailWord_2498104
  simp only [CollatzResearch.WordTrace]
  refine ⟨45556669070901662520794683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60742225427868883361059577 45556669070901662520794683)
  ·
    refine ⟨68335003606352493781192025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45556669070901662520794683 68335003606352493781192025)
    ·
      refine ⟨51251252704764370335894019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68335003606352493781192025 51251252704764370335894019)
      ·
        refine ⟨76876879057146555503841029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51251252704764370335894019 76876879057146555503841029)
        ·
          refine ⟨14414414823214979156970193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76876879057146555503841029 14414414823214979156970193)
          ·
            refine ⟨10810811117411234367727645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14414414823214979156970193 10810811117411234367727645)
            ·
              refine ⟨4054054169029212887897867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810811117411234367727645 4054054169029212887897867)
              ·
                refine ⟨6081081253543819331846801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054054169029212887897867 6081081253543819331846801)
                ·
                  refine ⟨4560810940157864498885101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6081081253543819331846801 4560810940157864498885101)
                  ·
                    refine ⟨1710304102559199187081913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4560810940157864498885101 1710304102559199187081913)
                    ·
                      refine ⟨1282728076919399390311435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710304102559199187081913 1282728076919399390311435)
                      ·
                        rfl

theorem cell23_2498104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_2498104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498104 prefixEnd_2498104 := by exact prefixLift 2498104
  have htrace : WordTrace (prefixWord ++ tailWord_2498104) baseStart_2498104 baseEnd_2498104 := by
    simpa [prefixWord, tailWord_2498104, baseEnd_2498104] using wordTrace_append hprefix tailTrace_2498104
  have hstable : (prefixWord ++ tailWord_2498104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498104).length < 2 ^ (prefixWord ++ tailWord_2498104).sum := by decide
  have hdescent : baseEnd_2498104 < baseStart_2498104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498111 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 1, 1, 3]
def baseStart_2498111 : Nat := 118140960795 + 2498111 * 2 ^ 59
def prefixEnd_2498111 : Nat := 4983230072969 + 3 ^ 40 * 2498111 * 2
def baseEnd_2498111 : Nat := 1282731671283980862923903

theorem tailTrace_2498111 : CollatzResearch.WordTrace tailWord_2498111 prefixEnd_2498111 1282731671283980862923903 := by
  unfold tailWord_2498111
  simp only [CollatzResearch.WordTrace]
  refine ⟨91113593452777965237094187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60742395635185310158062791 91113593452777965237094187)
  ·
    refine ⟨136670390179166947855641281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91113593452777965237094187 136670390179166947855641281)
    ·
      refine ⟨102502792634375210891730961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136670390179166947855641281 102502792634375210891730961)
      ·
        refine ⟨76877094475781408168798221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102502792634375210891730961 76877094475781408168798221)
        ·
          refine ⟨28828910428418028063299333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76877094475781408168798221 28828910428418028063299333)
          ·
            refine ⟨5405420705328380261868625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28828910428418028063299333 5405420705328380261868625)
            ·
              refine ⟨4054065528996285196401469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5405420705328380261868625 4054065528996285196401469)
              ·
                refine ⟨1520274573373606948650551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4054065528996285196401469 1520274573373606948650551)
                ·
                  refine ⟨2280411860060410422975827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520274573373606948650551 2280411860060410422975827)
                  ·
                    refine ⟨3420617790090615634463741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2280411860060410422975827 3420617790090615634463741)
                    ·
                      refine ⟨1282731671283980862923903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420617790090615634463741 1282731671283980862923903)
                      ·
                        rfl

theorem cell23_2498111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_2498111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498111 prefixEnd_2498111 := by exact prefixLift 2498111
  have htrace : WordTrace (prefixWord ++ tailWord_2498111) baseStart_2498111 baseEnd_2498111 := by
    simpa [prefixWord, tailWord_2498111, baseEnd_2498111] using wordTrace_append hprefix tailTrace_2498111
  have hstable : (prefixWord ++ tailWord_2498111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498111).length < 2 ^ (prefixWord ++ tailWord_2498111).sum := by decide
  have hdescent : baseEnd_2498111 < baseStart_2498111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498117 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 4]
def baseStart_2498117 : Nat := 118140960795 + 2498117 * 2 ^ 59
def prefixEnd_2498117 : Nat := 4983230072969 + 3 ^ 40 * 2498117 * 2
def baseEnd_2498117 : Nat := 1282734752167907839448875

theorem tailTrace_2498117 : CollatzResearch.WordTrace tailWord_2498117 prefixEnd_2498117 1282734752167907839448875 := by
  unfold tailWord_2498117
  simp only [CollatzResearch.WordTrace]
  refine ⟨91113812290756228261812605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60742541527170818841208403 91113812290756228261812605)
  ·
    refine ⟨34167679609033585598179727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91113812290756228261812605 34167679609033585598179727)
    ·
      refine ⟨51251519413550378397269591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34167679609033585598179727 51251519413550378397269591)
      ·
        refine ⟨76877279120325567595904387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51251519413550378397269591 76877279120325567595904387)
        ·
          refine ⟨115315918680488351393856581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76877279120325567595904387 115315918680488351393856581)
          ·
            refine ⟨21621734752591565886348109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115315918680488351393856581 21621734752591565886348109)
            ·
              refine ⟨8108150532221837207380541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21621734752591565886348109 8108150532221837207380541)
              ·
                refine ⟨3040556449583188952767703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8108150532221837207380541 3040556449583188952767703)
                ·
                  refine ⟨4560834674374783429151555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040556449583188952767703 4560834674374783429151555)
                  ·
                    refine ⟨6841252011562175143727333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4560834674374783429151555 6841252011562175143727333)
                    ·
                      refine ⟨1282734752167907839448875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6841252011562175143727333 1282734752167907839448875)
                      ·
                        rfl

theorem cell23_2498117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_2498117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498117 prefixEnd_2498117 := by exact prefixLift 2498117
  have htrace : WordTrace (prefixWord ++ tailWord_2498117) baseStart_2498117 baseEnd_2498117 := by
    simpa [prefixWord, tailWord_2498117, baseEnd_2498117] using wordTrace_append hprefix tailTrace_2498117
  have hstable : (prefixWord ++ tailWord_2498117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498117).length < 2 ^ (prefixWord ++ tailWord_2498117).sum := by decide
  have hdescent : baseEnd_2498117 < baseStart_2498117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498118 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2498118 : Nat := 118140960795 + 2498118 * 2 ^ 59
def prefixEnd_2498118 : Nat := 4983230072969 + 3 ^ 40 * 2498118 * 2
def baseEnd_2498118 : Nat := 142526140627618037281819

theorem tailTrace_2498118 : CollatzResearch.WordTrace tailWord_2498118 prefixEnd_2498118 142526140627618037281819 := by
  unfold tailWord_2498118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847307773867268919768719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60742565842501736955066005 2847307773867268919768719)
  ·
    refine ⟨4270961660800903379653079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847307773867268919768719 4270961660800903379653079)
    ·
      refine ⟨6406442491201355069479619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270961660800903379653079 6406442491201355069479619)
      ·
        refine ⟨9609663736802032604219429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406442491201355069479619 9609663736802032604219429)
        ·
          refine ⟨1801811950650381113291143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9609663736802032604219429 1801811950650381113291143)
          ·
            refine ⟨2702717925975571669936715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801811950650381113291143 2702717925975571669936715)
            ·
              refine ⟨4054076888963357504905073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702717925975571669936715 4054076888963357504905073)
              ·
                refine ⟨3040557666722518128678805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054076888963357504905073 3040557666722518128678805)
                ·
                  refine ⟨142526140627618037281819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3040557666722518128678805 142526140627618037281819)
                  ·
                    rfl

theorem cell23_2498118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2498118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498118 prefixEnd_2498118 := by exact prefixLift 2498118
  have htrace : WordTrace (prefixWord ++ tailWord_2498118) baseStart_2498118 baseEnd_2498118 := by
    simpa [prefixWord, tailWord_2498118, baseEnd_2498118] using wordTrace_append hprefix tailTrace_2498118
  have hstable : (prefixWord ++ tailWord_2498118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498118).length < 2 ^ (prefixWord ++ tailWord_2498118).sum := by decide
  have hdescent : baseEnd_2498118 < baseStart_2498118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498147 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2498147 : Nat := 118140960795 + 2498147 * 2 ^ 59
def prefixEnd_2498147 : Nat := 4983230072969 + 3 ^ 40 * 2498147 * 2
def baseEnd_2498147 : Nat := 1282750156587542722073737

theorem tailTrace_2498147 : CollatzResearch.WordTrace tailWord_2498147 prefixEnd_2498147 1282750156587542722073737 := by
  unfold tailWord_2498147
  simp only [CollatzResearch.WordTrace]
  refine ⟨91114906480647543385404695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60743270987098362256936463 91114906480647543385404695)
  ·
    refine ⟨136672359720971315078107043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91114906480647543385404695 136672359720971315078107043)
    ·
      refine ⟨205008539581456972617160565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136672359720971315078107043 205008539581456972617160565)
      ·
        refine ⟨19219550585761591182858803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205008539581456972617160565 19219550585761591182858803)
        ·
          refine ⟨28829325878642386774288205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19219550585761591182858803 28829325878642386774288205)
          ·
            refine ⟨10810997204490895040358077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28829325878642386774288205 10810997204490895040358077)
            ·
              refine ⟨4054123951684085640134279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810997204490895040358077 4054123951684085640134279)
              ·
                refine ⟨6081185927526128460201419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054123951684085640134279 6081185927526128460201419)
                ·
                  refine ⟨9121778891289192690302129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6081185927526128460201419 9121778891289192690302129)
                  ·
                    refine ⟨6841334168466894517726597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9121778891289192690302129 6841334168466894517726597)
                    ·
                      refine ⟨1282750156587542722073737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6841334168466894517726597 1282750156587542722073737)
                      ·
                        rfl

theorem cell23_2498147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2498147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498147 prefixEnd_2498147 := by exact prefixLift 2498147
  have htrace : WordTrace (prefixWord ++ tailWord_2498147) baseStart_2498147 baseEnd_2498147 := by
    simpa [prefixWord, tailWord_2498147, baseEnd_2498147] using wordTrace_append hprefix tailTrace_2498147
  have hstable : (prefixWord ++ tailWord_2498147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498147).length < 2 ^ (prefixWord ++ tailWord_2498147).sum := by decide
  have hdescent : baseEnd_2498147 < baseStart_2498147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498154 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2498154 : Nat := 118140960795 + 2498154 * 2 ^ 59
def prefixEnd_2498154 : Nat := 4983230072969 + 3 ^ 40 * 2498154 * 2
def baseEnd_2498154 : Nat := 1282753750952124194686205

theorem tailTrace_2498154 : CollatzResearch.WordTrace tailWord_2498154 prefixEnd_2498154 1282753750952124194686205 := by
  unfold tailWord_2498154
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778790447905545895227379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60743441194414789053939677 22778790447905545895227379)
  ·
    refine ⟨34168185671858318842841069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22778790447905545895227379 34168185671858318842841069)
    ·
      refine ⟨12813069626946869566065401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34168185671858318842841069 12813069626946869566065401)
      ·
        refine ⟨9609802220210152174549051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12813069626946869566065401 9609802220210152174549051)
        ·
          refine ⟨14414703330315228261823577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609802220210152174549051 14414703330315228261823577)
          ·
            refine ⟨10811027497736421196367683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14414703330315228261823577 10811027497736421196367683)
            ·
              refine ⟨16216541246604631794551525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10811027497736421196367683 16216541246604631794551525)
              ·
                refine ⟨3040601483738368461478411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16216541246604631794551525 3040601483738368461478411)
                ·
                  refine ⟨4560902225607552692217617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040601483738368461478411 4560902225607552692217617)
                  ·
                    refine ⟨3420676669205664519163213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560902225607552692217617 3420676669205664519163213)
                    ·
                      refine ⟨1282753750952124194686205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420676669205664519163213 1282753750952124194686205)
                      ·
                        rfl

theorem cell23_2498154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2498154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498154 prefixEnd_2498154 := by exact prefixLift 2498154
  have htrace : WordTrace (prefixWord ++ tailWord_2498154) baseStart_2498154 baseEnd_2498154 := by
    simpa [prefixWord, tailWord_2498154, baseEnd_2498154] using wordTrace_append hprefix tailTrace_2498154
  have hstable : (prefixWord ++ tailWord_2498154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498154).length < 2 ^ (prefixWord ++ tailWord_2498154).sum := by decide
  have hdescent : baseEnd_2498154 < baseStart_2498154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498157 : List Nat := [1, 5, 1, 1, 4, 1, 1, 9]
def baseStart_2498157 : Nat := 118140960795 + 2498157 * 2 ^ 59
def prefixEnd_2498157 : Nat := 4983230072969 + 3 ^ 40 * 2498157 * 2
def baseEnd_2498157 : Nat := 47509455236818062331433

theorem tailTrace_2498157 : CollatzResearch.WordTrace tailWord_2498157 prefixEnd_2498157 47509455236818062331433 := by
  unfold tailWord_2498157
  simp only [CollatzResearch.WordTrace]
  refine ⟨91115271210611315093268725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60743514140407543395512483 91115271210611315093268725)
  ·
    refine ⟨8542056675994810789993943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91115271210611315093268725 8542056675994810789993943)
    ·
      refine ⟨12813085013992216184990915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542056675994810789993943 12813085013992216184990915)
      ·
        refine ⟨19219627520988324277486373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12813085013992216184990915 19219627520988324277486373)
        ·
          refine ⟨3603680160185310802028695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19219627520988324277486373 3603680160185310802028695)
          ·
            refine ⟨5405520240277966203043043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603680160185310802028695 5405520240277966203043043)
            ·
              refine ⟨8108280360416949304564565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405520240277966203043043 8108280360416949304564565)
              ·
                refine ⟨47509455236818062331433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8108280360416949304564565 47509455236818062331433)
                ·
                  rfl

theorem cell23_2498157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 9].length) (baseStart_2498157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498157 prefixEnd_2498157 := by exact prefixLift 2498157
  have htrace : WordTrace (prefixWord ++ tailWord_2498157) baseStart_2498157 baseEnd_2498157 := by
    simpa [prefixWord, tailWord_2498157, baseEnd_2498157] using wordTrace_append hprefix tailTrace_2498157
  have hstable : (prefixWord ++ tailWord_2498157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498157).length < 2 ^ (prefixWord ++ tailWord_2498157).sum := by decide
  have hdescent : baseEnd_2498157 < baseStart_2498157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498224 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2]
def baseStart_2498224 : Nat := 118140960795 + 2498224 * 2 ^ 59
def prefixEnd_2498224 : Nat := 4983230072969 + 3 ^ 40 * 2498224 * 2
def baseEnd_2498224 : Nat := 1282789694597938920810883

theorem tailTrace_2498224 : CollatzResearch.WordTrace tailWord_2498224 prefixEnd_2498224 1282789694597938920810883 := by
  unfold tailWord_2498224
  simp only [CollatzResearch.WordTrace]
  refine ⟨45558857450684292767978863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60745143267579057023971817 45558857450684292767978863)
  ·
    refine ⟨68338286176026439151968295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45558857450684292767978863 68338286176026439151968295)
    ·
      refine ⟨102507429264039658727952443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68338286176026439151968295 102507429264039658727952443)
      ·
        refine ⟨153761143896059488091928665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102507429264039658727952443 153761143896059488091928665)
        ·
          refine ⟨115320857922044616068946499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153761143896059488091928665 115320857922044616068946499)
          ·
            refine ⟨172981286883066924103419749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115320857922044616068946499 172981286883066924103419749)
            ·
              refine ⟨32433991290575048269391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172981286883066924103419749 32433991290575048269391203)
              ·
                refine ⟨48650986935862572404086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32433991290575048269391203 48650986935862572404086805)
                ·
                  refine ⟨2280515012618558081441569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48650986935862572404086805 2280515012618558081441569)
                  ·
                    refine ⟨1710386259463918561081177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280515012618558081441569 1710386259463918561081177)
                    ·
                      refine ⟨1282789694597938920810883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710386259463918561081177 1282789694597938920810883)
                      ·
                        rfl

theorem cell23_2498224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 2, 2].length) (baseStart_2498224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498224 prefixEnd_2498224 := by exact prefixLift 2498224
  have htrace : WordTrace (prefixWord ++ tailWord_2498224) baseStart_2498224 baseEnd_2498224 := by
    simpa [prefixWord, tailWord_2498224, baseEnd_2498224] using wordTrace_append hprefix tailTrace_2498224
  have hstable : (prefixWord ++ tailWord_2498224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498224).length < 2 ^ (prefixWord ++ tailWord_2498224).sum := by decide
  have hdescent : baseEnd_2498224 < baseStart_2498224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498237 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2498237 : Nat := 118140960795 + 2498237 * 2 ^ 59
def prefixEnd_2498237 : Nat := 4983230072969 + 3 ^ 40 * 2498237 * 2
def baseEnd_2498237 : Nat := 1282796369846447369948323

theorem tailTrace_2498237 : CollatzResearch.WordTrace tailWord_2498237 prefixEnd_2498237 1282796369846447369948323 := by
  unfold tailWord_2498237
  simp only [CollatzResearch.WordTrace]
  refine ⟨91118189050321488756180965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60745459366880992504120643 91118189050321488756180965)
  ·
    refine ⟨17084660446935279141783931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91118189050321488756180965 17084660446935279141783931)
    ·
      refine ⟨25626990670402918712675897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17084660446935279141783931 25626990670402918712675897)
      ·
        refine ⟨19220243002802189034506923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25626990670402918712675897 19220243002802189034506923)
        ·
          refine ⟨28830364504203283551760385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19220243002802189034506923 28830364504203283551760385)
          ·
            refine ⟨21622773378152462663820289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28830364504203283551760385 21622773378152462663820289)
            ·
              refine ⟨16217080033614346997865217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21622773378152462663820289 16217080033614346997865217)
              ·
                refine ⟨12162810025210760248398913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16217080033614346997865217 12162810025210760248398913)
                ·
                  refine ⟨9122107518908070186299185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12162810025210760248398913 9122107518908070186299185)
                  ·
                    refine ⟨6841580639181052639724389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9122107518908070186299185 6841580639181052639724389)
                    ·
                      refine ⟨1282796369846447369948323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6841580639181052639724389 1282796369846447369948323)
                      ·
                        rfl

theorem cell23_2498237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2498237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498237 prefixEnd_2498237 := by exact prefixLift 2498237
  have htrace : WordTrace (prefixWord ++ tailWord_2498237) baseStart_2498237 baseEnd_2498237 := by
    simpa [prefixWord, tailWord_2498237, baseEnd_2498237] using wordTrace_append hprefix tailTrace_2498237
  have hstable : (prefixWord ++ tailWord_2498237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498237).length < 2 ^ (prefixWord ++ tailWord_2498237).sum := by decide
  have hdescent : baseEnd_2498237 < baseStart_2498237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498257 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_2498257 : Nat := 118140960795 + 2498257 * 2 ^ 59
def prefixEnd_2498257 : Nat := 4983230072969 + 3 ^ 40 * 2498257 * 2
def baseEnd_2498257 : Nat := 1282806639459537291698231

theorem tailTrace_2498257 : CollatzResearch.WordTrace tailWord_2498257 prefixEnd_2498257 1282806639459537291698231 := by
  unfold tailWord_2498257
  simp only [CollatzResearch.WordTrace]
  refine ⟨91118918510249032171909025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60745945673499354781272683 91118918510249032171909025)
  ·
    refine ⟨68339188882686774128931769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91118918510249032171909025 68339188882686774128931769)
    ·
      refine ⟨51254391662015080596698827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68339188882686774128931769 51254391662015080596698827)
      ·
        refine ⟨76881587493022620895048241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51254391662015080596698827 76881587493022620895048241)
        ·
          refine ⟨57661190619766965671286181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76881587493022620895048241 57661190619766965671286181)
          ·
            refine ⟨10811473241206306063366159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57661190619766965671286181 10811473241206306063366159)
            ·
              refine ⟨16217209861809459095049239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10811473241206306063366159 16217209861809459095049239)
              ·
                refine ⟨24325814792714188642573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16217209861809459095049239 24325814792714188642573859)
                ·
                  refine ⟨36488722189071282963860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24325814792714188642573859 36488722189071282963860789)
                  ·
                    refine ⟨3420817705225432777861949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36488722189071282963860789 3420817705225432777861949)
                    ·
                      refine ⟨1282806639459537291698231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420817705225432777861949 1282806639459537291698231)
                      ·
                        rfl

theorem cell23_2498257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_2498257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498257 prefixEnd_2498257 := by exact prefixLift 2498257
  have htrace : WordTrace (prefixWord ++ tailWord_2498257) baseStart_2498257 baseEnd_2498257 := by
    simpa [prefixWord, tailWord_2498257, baseEnd_2498257] using wordTrace_append hprefix tailTrace_2498257
  have hstable : (prefixWord ++ tailWord_2498257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498257).length < 2 ^ (prefixWord ++ tailWord_2498257).sum := by decide
  have hdescent : baseEnd_2498257 < baseStart_2498257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498258 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_2498258 : Nat := 118140960795 + 2498258 * 2 ^ 59
def prefixEnd_2498258 : Nat := 4983230072969 + 3 ^ 40 * 2498258 * 2
def baseEnd_2498258 : Nat := 1282807152940191787785727

theorem tailTrace_2498258 : CollatzResearch.WordTrace tailWord_2498258 prefixEnd_2498258 1282807152940191787785727 := by
  unfold tailWord_2498258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22779738745811352335673857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60745969988830272895130285 22779738745811352335673857)
  ·
    refine ⟨17084804059358514251755393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22779738745811352335673857 17084804059358514251755393)
    ·
      refine ⟨12813603044518885688816545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17084804059358514251755393 12813603044518885688816545)
      ·
        refine ⟨9610202283389164266612409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12813603044518885688816545 9610202283389164266612409)
        ·
          refine ⟨7207651712541873199959307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9610202283389164266612409 7207651712541873199959307)
          ·
            refine ⟨10811477568812809799938961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207651712541873199959307 10811477568812809799938961)
            ·
              refine ⟨8108608176609607349954221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10811477568812809799938961 8108608176609607349954221)
              ·
                refine ⟨3040728066228602756232833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8108608176609607349954221 3040728066228602756232833)
                ·
                  refine ⟨2280546049671452067174625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040728066228602756232833 2280546049671452067174625)
                  ·
                    refine ⟨1710409537253589050380969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280546049671452067174625 1710409537253589050380969)
                    ·
                      refine ⟨1282807152940191787785727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710409537253589050380969 1282807152940191787785727)
                      ·
                        rfl

theorem cell23_2498258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_2498258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498258 prefixEnd_2498258 := by exact prefixLift 2498258
  have htrace : WordTrace (prefixWord ++ tailWord_2498258) baseStart_2498258 baseEnd_2498258 := by
    simpa [prefixWord, tailWord_2498258, baseEnd_2498258] using wordTrace_append hprefix tailTrace_2498258
  have hstable : (prefixWord ++ tailWord_2498258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498258).length < 2 ^ (prefixWord ++ tailWord_2498258).sum := by decide
  have hdescent : baseEnd_2498258 < baseStart_2498258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498277 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_2498277 : Nat := 118140960795 + 2498277 * 2 ^ 59
def prefixEnd_2498277 : Nat := 4983230072969 + 3 ^ 40 * 2498277 * 2
def baseEnd_2498277 : Nat := 427605636357542404482713

theorem tailTrace_2498277 : CollatzResearch.WordTrace tailWord_2498277 prefixEnd_2498277 427605636357542404482713 := by
  unfold tailWord_2498277
  simp only [CollatzResearch.WordTrace]
  refine ⟨91119647970176575587637085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60746431980117717058424723 91119647970176575587637085)
  ·
    refine ⟨34169867988816215845363907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91119647970176575587637085 34169867988816215845363907)
    ·
      refine ⟨51254801983224323768045861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34169867988816215845363907 51254801983224323768045861)
      ·
        refine ⟨9610275371854560706508599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51254801983224323768045861 9610275371854560706508599)
        ·
          refine ⟨14415413057781841059762899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9610275371854560706508599 14415413057781841059762899)
          ·
            refine ⟨21623119586672761589644349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14415413057781841059762899 21623119586672761589644349)
            ·
              refine ⟨8108669845002285596116631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21623119586672761589644349 8108669845002285596116631)
              ·
                refine ⟨12163004767503428394174947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8108669845002285596116631 12163004767503428394174947)
                ·
                  refine ⟨18244507151255142591262421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12163004767503428394174947 18244507151255142591262421)
                  ·
                    refine ⟨427605636357542404482713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18244507151255142591262421 427605636357542404482713)
                    ·
                      rfl

theorem cell23_2498277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_2498277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498277 prefixEnd_2498277 := by exact prefixLift 2498277
  have htrace : WordTrace (prefixWord ++ tailWord_2498277) baseStart_2498277 baseEnd_2498277 := by
    simpa [prefixWord, tailWord_2498277, baseEnd_2498277] using wordTrace_append hprefix tailTrace_2498277
  have hstable : (prefixWord ++ tailWord_2498277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498277).length < 2 ^ (prefixWord ++ tailWord_2498277).sum := by decide
  have hdescent : baseEnd_2498277 < baseStart_2498277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498292 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2498292 : Nat := 118140960795 + 2498292 * 2 ^ 59
def prefixEnd_2498292 : Nat := 4983230072969 + 3 ^ 40 * 2498292 * 2
def baseEnd_2498292 : Nat := 1282824611282444654760571

theorem tailTrace_2498292 : CollatzResearch.WordTrace tailWord_2498292 prefixEnd_2498292 1282824611282444654760571 := by
  unfold tailWord_2498292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45560097532561116574716565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60746796710081488766288753 45560097532561116574716565)
  ·
    refine ⟨2135629571838802339439839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45560097532561116574716565 2135629571838802339439839)
    ·
      refine ⟨3203444357758203509159759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135629571838802339439839 3203444357758203509159759)
      ·
        refine ⟨4805166536637305263739639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203444357758203509159759 4805166536637305263739639)
        ·
          refine ⟨7207749804955957895609459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4805166536637305263739639 7207749804955957895609459)
          ·
            refine ⟨10811624707433936843414189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207749804955957895609459 10811624707433936843414189)
            ·
              refine ⟨4054359265287726316280321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10811624707433936843414189 4054359265287726316280321)
              ·
                refine ⟨3040769448965794737210241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054359265287726316280321 3040769448965794737210241)
                ·
                  refine ⟨2280577086724346052907681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040769448965794737210241 2280577086724346052907681)
                  ·
                    refine ⟨1710432815043259539680761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280577086724346052907681 1710432815043259539680761)
                    ·
                      refine ⟨1282824611282444654760571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710432815043259539680761 1282824611282444654760571)
                      ·
                        rfl

theorem cell23_2498292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2498292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498292 prefixEnd_2498292 := by exact prefixLift 2498292
  have htrace : WordTrace (prefixWord ++ tailWord_2498292) baseStart_2498292 baseEnd_2498292 := by
    simpa [prefixWord, tailWord_2498292, baseEnd_2498292] using wordTrace_append hprefix tailTrace_2498292
  have hstable : (prefixWord ++ tailWord_2498292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498292).length < 2 ^ (prefixWord ++ tailWord_2498292).sum := by decide
  have hdescent : baseEnd_2498292 < baseStart_2498292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498337 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 8]
def baseStart_2498337 : Nat := 118140960795 + 2498337 * 2 ^ 59
def prefixEnd_2498337 : Nat := 4983230072969 + 3 ^ 40 * 2498337 * 2
def baseEnd_2498337 : Nat := 142538635323544108744207

theorem tailTrace_2498337 : CollatzResearch.WordTrace tailWord_2498337 prefixEnd_2498337 142538635323544108744207 := by
  unfold tailWord_2498337
  simp only [CollatzResearch.WordTrace]
  refine ⟨91121836349959205834821265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60747890899972803889880843 91121836349959205834821265)
  ·
    refine ⟨68341377262469404376115949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91121836349959205834821265 68341377262469404376115949)
    ·
      refine ⟨25628016473426026641043481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68341377262469404376115949 25628016473426026641043481)
      ·
        refine ⟨19221012355069519980782611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25628016473426026641043481 19221012355069519980782611)
        ·
          refine ⟨28831518532604279971173917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19221012355069519980782611 28831518532604279971173917)
          ·
            refine ⟨10811819449726604989190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28831518532604279971173917 10811819449726604989190219)
            ·
              refine ⟨16217729174589907483785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10811819449726604989190219 16217729174589907483785329)
              ·
                refine ⟨12163296880942430612838997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16217729174589907483785329 12163296880942430612838997)
                ·
                  refine ⟨142538635323544108744207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12163296880942430612838997 142538635323544108744207)
                  ·
                    rfl

theorem cell23_2498337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_2498337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498337 prefixEnd_2498337 := by exact prefixLift 2498337
  have htrace : WordTrace (prefixWord ++ tailWord_2498337) baseStart_2498337 baseEnd_2498337 := by
    simpa [prefixWord, tailWord_2498337, baseEnd_2498337] using wordTrace_append hprefix tailTrace_2498337
  have hstable : (prefixWord ++ tailWord_2498337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498337).length < 2 ^ (prefixWord ++ tailWord_2498337).sum := by decide
  have hdescent : baseEnd_2498337 < baseStart_2498337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498347 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3]
def baseStart_2498347 : Nat := 118140960795 + 2498347 * 2 ^ 59
def prefixEnd_2498347 : Nat := 4983230072969 + 3 ^ 40 * 2498347 * 2
def baseEnd_2498347 : Nat := 1282852852718441939572817

theorem tailTrace_2498347 : CollatzResearch.WordTrace tailWord_2498347 prefixEnd_2498347 1282852852718441939572817 := by
  unfold tailWord_2498347
  simp only [CollatzResearch.WordTrace]
  refine ⟨91122201079922977542685295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60748134053281985028456863 91122201079922977542685295)
  ·
    refine ⟨136683301619884466314027943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91122201079922977542685295 136683301619884466314027943)
    ·
      refine ⟨205024952429826699471041915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136683301619884466314027943 205024952429826699471041915)
      ·
        refine ⟨307537428644740049206562873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205024952429826699471041915 307537428644740049206562873)
        ·
          refine ⟨230653071483555036904922155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307537428644740049206562873 230653071483555036904922155)
          ·
            refine ⟨345979607225332555357383233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230653071483555036904922155 345979607225332555357383233)
            ·
              refine ⟨259484705418999416518037425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345979607225332555357383233 259484705418999416518037425)
              ·
                refine ⟨194613529064249562388528069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259484705418999416518037425 194613529064249562388528069)
                ·
                  refine ⟨36490036699546792947849013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194613529064249562388528069 36490036699546792947849013)
                  ·
                    refine ⟨3420940940582511838860845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36490036699546792947849013 3420940940582511838860845)
                    ·
                      refine ⟨1282852852718441939572817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3420940940582511838860845 1282852852718441939572817)
                      ·
                        rfl

theorem cell23_2498347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].length) (baseStart_2498347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498347 prefixEnd_2498347 := by exact prefixLift 2498347
  have htrace : WordTrace (prefixWord ++ tailWord_2498347) baseStart_2498347 baseEnd_2498347 := by
    simpa [prefixWord, tailWord_2498347, baseEnd_2498347] using wordTrace_append hprefix tailTrace_2498347
  have hstable : (prefixWord ++ tailWord_2498347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498347).length < 2 ^ (prefixWord ++ tailWord_2498347).sum := by decide
  have hdescent : baseEnd_2498347 < baseStart_2498347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498358 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2498358 : Nat := 118140960795 + 2498358 * 2 ^ 59
def prefixEnd_2498358 : Nat := 4983230072969 + 3 ^ 40 * 2498358 * 2
def baseEnd_2498358 : Nat := 427619500335213798845089

theorem tailTrace_2498358 : CollatzResearch.WordTrace tailWord_2498358 prefixEnd_2498358 427619500335213798845089 := by
  unfold tailWord_2498358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695162642680195401333483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60748401521922084280890485 5695162642680195401333483)
  ·
    refine ⟨8542743964020293102000225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5695162642680195401333483 8542743964020293102000225)
    ·
      refine ⟨6407057973015219826500169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8542743964020293102000225 6407057973015219826500169)
      ·
        refine ⟨4805293479761414869875127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6407057973015219826500169 4805293479761414869875127)
        ·
          refine ⟨7207940219642122304812691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4805293479761414869875127 7207940219642122304812691)
          ·
            refine ⟨10811910329463183457219037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207940219642122304812691 10811910329463183457219037)
            ·
              refine ⟨4054466373548693796457139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10811910329463183457219037 4054466373548693796457139)
              ·
                refine ⟨6081699560323040694685709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054466373548693796457139 6081699560323040694685709)
                ·
                  refine ⟨2280637335121140260507141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6081699560323040694685709 2280637335121140260507141)
                  ·
                    refine ⟨427619500335213798845089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280637335121140260507141 427619500335213798845089)
                    ·
                      rfl

theorem cell23_2498358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2498358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498358 prefixEnd_2498358 := by exact prefixLift 2498358
  have htrace : WordTrace (prefixWord ++ tailWord_2498358) baseStart_2498358 baseEnd_2498358 := by
    simpa [prefixWord, tailWord_2498358, baseEnd_2498358] using wordTrace_append hprefix tailTrace_2498358
  have hstable : (prefixWord ++ tailWord_2498358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498358).length < 2 ^ (prefixWord ++ tailWord_2498358).sum := by decide
  have hdescent : baseEnd_2498358 < baseStart_2498358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498371 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 6]
def baseStart_2498371 : Nat := 118140960795 + 2498371 * 2 ^ 59
def prefixEnd_2498371 : Nat := 4983230072969 + 3 ^ 40 * 2498371 * 2
def baseEnd_2498371 : Nat := 142540575139349982852523

theorem tailTrace_2498371 : CollatzResearch.WordTrace tailWord_2498371 prefixEnd_2498371 142540575139349982852523 := by
  unfold tailWord_2498371
  simp only [CollatzResearch.WordTrace]
  refine ⟨91123076431836029641558967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60748717621224019761039311 91123076431836029641558967)
  ·
    refine ⟨136684614647754044462338451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91123076431836029641558967 136684614647754044462338451)
    ·
      refine ⟨205026921971631066693507677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136684614647754044462338451 205026921971631066693507677)
      ·
        refine ⟨76885095739361650010065379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205026921971631066693507677 76885095739361650010065379)
        ·
          refine ⟨115327643609042475015098069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76885095739361650010065379 115327643609042475015098069)
          ·
            refine ⟨2702991647086933008166361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115327643609042475015098069 2702991647086933008166361)
            ·
              refine ⟨2027243735315199756124771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702991647086933008166361 2027243735315199756124771)
              ·
                refine ⟨3040865602972799634187157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027243735315199756124771 3040865602972799634187157)
                ·
                  refine ⟨142540575139349982852523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3040865602972799634187157 142540575139349982852523)
                  ·
                    rfl

theorem cell23_2498371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 6].length) (baseStart_2498371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498371 prefixEnd_2498371 := by exact prefixLift 2498371
  have htrace : WordTrace (prefixWord ++ tailWord_2498371) baseStart_2498371 baseEnd_2498371 := by
    simpa [prefixWord, tailWord_2498371, baseEnd_2498371] using wordTrace_append hprefix tailTrace_2498371
  have hstable : (prefixWord ++ tailWord_2498371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498371).length < 2 ^ (prefixWord ++ tailWord_2498371).sum := by decide
  have hdescent : baseEnd_2498371 < baseStart_2498371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498401 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2498401 : Nat := 118140960795 + 2498401 * 2 ^ 59
def prefixEnd_2498401 : Nat := 4983230072969 + 3 ^ 40 * 2498401 * 2
def baseEnd_2498401 : Nat := 427626860224594909432523

theorem tailTrace_2498401 : CollatzResearch.WordTrace tailWord_2498401 prefixEnd_2498401 427626860224594909432523 := by
  unfold tailWord_2498401
  simp only [CollatzResearch.WordTrace]
  refine ⟨91124170621727344765151057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60749447081151563176767371 91124170621727344765151057)
  ·
    refine ⟨68343127966295508573863293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91124170621727344765151057 68343127966295508573863293)
    ·
      refine ⟨25628672987360815715198735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68343127966295508573863293 25628672987360815715198735)
      ·
        refine ⟨38443009481041223572798103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25628672987360815715198735 38443009481041223572798103)
        ·
          refine ⟨57664514221561835359197155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38443009481041223572798103 57664514221561835359197155)
          ·
            refine ⟨86496771332342753038795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57664514221561835359197155 86496771332342753038795733)
            ·
              refine ⟨2027268078101783274346775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86496771332342753038795733 2027268078101783274346775)
              ·
                refine ⟨3040902117152674911520163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027268078101783274346775 3040902117152674911520163)
                ·
                  refine ⟨4561353175729012367280245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040902117152674911520163 4561353175729012367280245)
                  ·
                    refine ⟨427626860224594909432523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4561353175729012367280245 427626860224594909432523)
                    ·
                      rfl

theorem cell23_2498401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2498401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498401 prefixEnd_2498401 := by exact prefixLift 2498401
  have htrace : WordTrace (prefixWord ++ tailWord_2498401) baseStart_2498401 baseEnd_2498401 := by
    simpa [prefixWord, tailWord_2498401, baseEnd_2498401] using wordTrace_append hprefix tailTrace_2498401
  have hstable : (prefixWord ++ tailWord_2498401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498401).length < 2 ^ (prefixWord ++ tailWord_2498401).sum := by decide
  have hdescent : baseEnd_2498401 < baseStart_2498401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498441 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_2498441 : Nat := 118140960795 + 2498441 * 2 ^ 59
def prefixEnd_2498441 : Nat := 4983230072969 + 3 ^ 40 * 2498441 * 2
def baseEnd_2498441 : Nat := 1282901119899964571797385

theorem tailTrace_2498441 : CollatzResearch.WordTrace tailWord_2498441 prefixEnd_2498441 1282901119899964571797385 := by
  unfold tailWord_2498441
  simp only [CollatzResearch.WordTrace]
  refine ⟨91125629541582431596607177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60750419694388287731071451 91125629541582431596607177)
  ·
    refine ⟨68344222156186823697455383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91125629541582431596607177 68344222156186823697455383)
    ·
      refine ⟨102516333234280235546183075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68344222156186823697455383 102516333234280235546183075)
      ·
        refine ⟨153774499851420353319274613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102516333234280235546183075 153774499851420353319274613)
        ·
          refine ⟨14416359361070658123681995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153774499851420353319274613 14416359361070658123681995)
          ·
            refine ⟨21624539041605987185522993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14416359361070658123681995 21624539041605987185522993)
            ·
              refine ⟨16218404281204490389142245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21624539041605987185522993 16218404281204490389142245)
              ·
                refine ⟨3040950802725841947964171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16218404281204490389142245 3040950802725841947964171)
                ·
                  refine ⟨4561426204088762921946257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040950802725841947964171 4561426204088762921946257)
                  ·
                    refine ⟨3421069653066572191459693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4561426204088762921946257 3421069653066572191459693)
                    ·
                      refine ⟨1282901119899964571797385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3421069653066572191459693 1282901119899964571797385)
                      ·
                        rfl

theorem cell23_2498441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_2498441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498441 prefixEnd_2498441 := by exact prefixLift 2498441
  have htrace : WordTrace (prefixWord ++ tailWord_2498441) baseStart_2498441 baseEnd_2498441 := by
    simpa [prefixWord, tailWord_2498441, baseEnd_2498441] using wordTrace_append hprefix tailTrace_2498441
  have hstable : (prefixWord ++ tailWord_2498441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498441).length < 2 ^ (prefixWord ++ tailWord_2498441).sum := by decide
  have hdescent : baseEnd_2498441 < baseStart_2498441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498442 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2498442 : Nat := 118140960795 + 2498442 * 2 ^ 59
def prefixEnd_2498442 : Nat := 4983230072969 + 3 ^ 40 * 2498442 * 2
def baseEnd_2498442 : Nat := 1282901633380619067884881

theorem tailTrace_2498442 : CollatzResearch.WordTrace tailWord_2498442 prefixEnd_2498442 1282901633380619067884881 := by
  unfold tailWord_2498442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22781416503644702191848395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60750444009719205844929053 22781416503644702191848395)
  ·
    refine ⟨34172124755467053287772593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22781416503644702191848395 34172124755467053287772593)
    ·
      refine ⟨25629093566600289965829445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34172124755467053287772593 25629093566600289965829445)
      ·
        refine ⟨4805455043737554368593021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25629093566600289965829445 4805455043737554368593021)
        ·
          refine ⟨1802045641401582888222383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4805455043737554368593021 1802045641401582888222383)
          ·
            refine ⟨2703068462102374332333575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802045641401582888222383 2703068462102374332333575)
            ·
              refine ⟨4054602693153561498500363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703068462102374332333575 4054602693153561498500363)
              ·
                refine ⟨6081904039730342247750545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054602693153561498500363 6081904039730342247750545)
                ·
                  refine ⟨4561428029797756685812909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6081904039730342247750545 4561428029797756685812909)
                  ·
                    refine ⟨1710535511174158757179841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4561428029797756685812909 1710535511174158757179841)
                    ·
                      refine ⟨1282901633380619067884881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710535511174158757179841 1282901633380619067884881)
                      ·
                        rfl

theorem cell23_2498442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2498442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498442 prefixEnd_2498442 := by exact prefixLift 2498442
  have htrace : WordTrace (prefixWord ++ tailWord_2498442) baseStart_2498442 baseEnd_2498442 := by
    simpa [prefixWord, tailWord_2498442, baseEnd_2498442] using wordTrace_append hprefix tailTrace_2498442
  have hstable : (prefixWord ++ tailWord_2498442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498442).length < 2 ^ (prefixWord ++ tailWord_2498442).sum := by decide
  have hdescent : baseEnd_2498442 < baseStart_2498442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498447 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_2498447 : Nat := 118140960795 + 2498447 * 2 ^ 59
def prefixEnd_2498447 : Nat := 4983230072969 + 3 ^ 40 * 2498447 * 2
def baseEnd_2498447 : Nat := 1282904200783891548322357

theorem tailTrace_2498447 : CollatzResearch.WordTrace tailWord_2498447 prefixEnd_2498447 1282904200783891548322357 := by
  unfold tailWord_2498447
  simp only [CollatzResearch.WordTrace]
  refine ⟨91125848379560694621325595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60750565586373796414217063 91125848379560694621325595)
  ·
    refine ⟨136688772569341041931988393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91125848379560694621325595 136688772569341041931988393)
    ·
      refine ⟨102516579427005781448991295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136688772569341041931988393 102516579427005781448991295)
      ·
        refine ⟨153774869140508672173486943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102516579427005781448991295 153774869140508672173486943)
        ·
          refine ⟨230662303710763008260230415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153774869140508672173486943 230662303710763008260230415)
          ·
            refine ⟨345993455566144512390345623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230662303710763008260230415 345993455566144512390345623)
            ·
              refine ⟨518990183349216768585518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345993455566144512390345623 518990183349216768585518435)
              ·
                refine ⟨778485275023825152878277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518990183349216768585518435 778485275023825152878277653)
                ·
                  refine ⟨36491497266741804041169265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 778485275023825152878277653 36491497266741804041169265)
                  ·
                    refine ⟨27368622950056353030876949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36491497266741804041169265 27368622950056353030876949)
                    ·
                      refine ⟨1282904200783891548322357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27368622950056353030876949 1282904200783891548322357)
                      ·
                        rfl

theorem cell23_2498447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_2498447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498447 prefixEnd_2498447 := by exact prefixLift 2498447
  have htrace : WordTrace (prefixWord ++ tailWord_2498447) baseStart_2498447 baseEnd_2498447 := by
    simpa [prefixWord, tailWord_2498447, baseEnd_2498447] using wordTrace_append hprefix tailTrace_2498447
  have hstable : (prefixWord ++ tailWord_2498447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498447).length < 2 ^ (prefixWord ++ tailWord_2498447).sum := by decide
  have hdescent : baseEnd_2498447 < baseStart_2498447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498455 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 1, 2, 2]
def baseStart_2498455 : Nat := 118140960795 + 2498455 * 2 ^ 59
def prefixEnd_2498455 : Nat := 4983230072969 + 3 ^ 40 * 2498455 * 2
def baseEnd_2498455 : Nat := 1282908308629127517022321

theorem tailTrace_2498455 : CollatzResearch.WordTrace tailWord_2498455 prefixEnd_2498455 1282908308629127517022321 := by
  unfold tailWord_2498455
  simp only [CollatzResearch.WordTrace]
  refine ⟨91126140163531711987616819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60750760109021141325077879 91126140163531711987616819)
  ·
    refine ⟨136689210245297567981425229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91126140163531711987616819 136689210245297567981425229)
    ·
      refine ⟨51258453841986587993034461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136689210245297567981425229 51258453841986587993034461)
      ·
        refine ⟨19221920190744970497387923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51258453841986587993034461 19221920190744970497387923)
        ·
          refine ⟨28832880286117455746081885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19221920190744970497387923 28832880286117455746081885)
          ·
            refine ⟨10812330107294045904780707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28832880286117455746081885 10812330107294045904780707)
            ·
              refine ⟨16218495160941068857171061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812330107294045904780707 16218495160941068857171061)
              ·
                refine ⟨1520483921338225205359787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16218495160941068857171061 1520483921338225205359787)
                ·
                  refine ⟨2280725882007337808039681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520483921338225205359787 2280725882007337808039681)
                  ·
                    refine ⟨1710544411505503356029761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280725882007337808039681 1710544411505503356029761)
                    ·
                      refine ⟨1282908308629127517022321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710544411505503356029761 1282908308629127517022321)
                      ·
                        rfl

theorem cell23_2498455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_2498455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498455 prefixEnd_2498455 := by exact prefixLift 2498455
  have htrace : WordTrace (prefixWord ++ tailWord_2498455) baseStart_2498455 baseEnd_2498455 := by
    simpa [prefixWord, tailWord_2498455, baseEnd_2498455] using wordTrace_append hprefix tailTrace_2498455
  have hstable : (prefixWord ++ tailWord_2498455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498455).length < 2 ^ (prefixWord ++ tailWord_2498455).sum := by decide
  have hdescent : baseEnd_2498455 < baseStart_2498455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498458 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2498458 : Nat := 118140960795 + 2498458 * 2 ^ 59
def prefixEnd_2498458 : Nat := 4983230072969 + 3 ^ 40 * 2498458 * 2
def baseEnd_2498458 : Nat := 1282909849071091005284807

theorem tailTrace_2498458 : CollatzResearch.WordTrace tailWord_2498458 prefixEnd_2498458 1282909849071091005284807 := by
  unfold tailWord_2498458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22781562395630210874994007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60750833055013895666650685 22781562395630210874994007)
  ·
    refine ⟨34172343593445316312491011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22781562395630210874994007 34172343593445316312491011)
    ·
      refine ⟨51258515390167974468736517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34172343593445316312491011 51258515390167974468736517)
      ·
        refine ⟨9610971635656495212888097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51258515390167974468736517 9610971635656495212888097)
        ·
          refine ⟨7208228726742371409666073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9610971635656495212888097 7208228726742371409666073)
          ·
            refine ⟨5406171545056778557249555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7208228726742371409666073 5406171545056778557249555)
            ·
              refine ⟨8109257317585167835874333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406171545056778557249555 8109257317585167835874333)
              ·
                refine ⟨3040971494094437938452875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8109257317585167835874333 3040971494094437938452875)
                ·
                  refine ⟨4561457241141656907679313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040971494094437938452875 4561457241141656907679313)
                  ·
                    refine ⟨3421092930856242680759485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4561457241141656907679313 3421092930856242680759485)
                    ·
                      refine ⟨1282909849071091005284807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3421092930856242680759485 1282909849071091005284807)
                      ·
                        rfl

theorem cell23_2498458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2498458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498458 prefixEnd_2498458 := by exact prefixLift 2498458
  have htrace : WordTrace (prefixWord ++ tailWord_2498458) baseStart_2498458 baseEnd_2498458 := by
    simpa [prefixWord, tailWord_2498458, baseEnd_2498458] using wordTrace_append hprefix tailTrace_2498458
  have hstable : (prefixWord ++ tailWord_2498458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498458).length < 2 ^ (prefixWord ++ tailWord_2498458).sum := by decide
  have hdescent : baseEnd_2498458 < baseStart_2498458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498465 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2498465 : Nat := 118140960795 + 2498465 * 2 ^ 59
def prefixEnd_2498465 : Nat := 4983230072969 + 3 ^ 40 * 2498465 * 2
def baseEnd_2498465 : Nat := 427637814478557492632425

theorem tailTrace_2498465 : CollatzResearch.WordTrace tailWord_2498465 prefixEnd_2498465 427637814478557492632425 := by
  unfold tailWord_2498465
  simp only [CollatzResearch.WordTrace]
  refine ⟨91126504893495483695480849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60751003262330322463653899 91126504893495483695480849)
  ·
    refine ⟨68344878670121612771610637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91126504893495483695480849 68344878670121612771610637)
    ·
      refine ⟨25629329501295604789353989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68344878670121612771610637 25629329501295604789353989)
      ·
        refine ⟨4805499281492925898003873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25629329501295604789353989 4805499281492925898003873)
        ·
          refine ⟨3604124461119694423502905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805499281492925898003873 3604124461119694423502905)
          ·
            refine ⟨2703093345839770817627179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3604124461119694423502905 2703093345839770817627179)
            ·
              refine ⟨4054640018759656226440769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703093345839770817627179 4054640018759656226440769)
              ·
                refine ⟨3040980014069742169830577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054640018759656226440769 3040980014069742169830577)
                ·
                  refine ⟨2280735010552306627372933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040980014069742169830577 2280735010552306627372933)
                  ·
                    refine ⟨427637814478557492632425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280735010552306627372933 427637814478557492632425)
                    ·
                      rfl

theorem cell23_2498465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2498465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498465 prefixEnd_2498465 := by exact prefixLift 2498465
  have htrace : WordTrace (prefixWord ++ tailWord_2498465) baseStart_2498465 baseEnd_2498465 := by
    simpa [prefixWord, tailWord_2498465, baseEnd_2498465] using wordTrace_append hprefix tailTrace_2498465
  have hstable : (prefixWord ++ tailWord_2498465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498465).length < 2 ^ (prefixWord ++ tailWord_2498465).sum := by decide
  have hdescent : baseEnd_2498465 < baseStart_2498465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498511 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 4, 2]
def baseStart_2498511 : Nat := 118140960795 + 2498511 * 2 ^ 59
def prefixEnd_2498511 : Nat := 4983230072969 + 3 ^ 40 * 2498511 * 2
def baseEnd_2498511 : Nat := 1282937063545779297922063

theorem tailTrace_2498511 : CollatzResearch.WordTrace tailWord_2498511 prefixEnd_2498511 1282937063545779297922063 := by
  unfold tailWord_2498511
  simp only [CollatzResearch.WordTrace]
  refine ⟨91128182651328833551655387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60752121767552555701103591 91128182651328833551655387)
  ·
    refine ⟨136692273976993250327483081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91128182651328833551655387 136692273976993250327483081)
    ·
      refine ⟨102519205482744937745612311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136692273976993250327483081 102519205482744937745612311)
      ·
        refine ⟨153778808224117406618418467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102519205482744937745612311 153778808224117406618418467)
        ·
          refine ⟨230668212336176109927627701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153778808224117406618418467 230668212336176109927627701)
          ·
            refine ⟨21625144906516510305715097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230668212336176109927627701 21625144906516510305715097)
            ·
              refine ⟨16218858679887382729286323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21625144906516510305715097 16218858679887382729286323)
              ·
                refine ⟨24328288019831074093929485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16218858679887382729286323 24328288019831074093929485)
                ·
                  refine ⟨9123108007436652785223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24328288019831074093929485 9123108007436652785223557)
                  ·
                    refine ⟨1710582751394372397229417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9123108007436652785223557 1710582751394372397229417)
                    ·
                      refine ⟨1282937063545779297922063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710582751394372397229417 1282937063545779297922063)
                      ·
                        rfl

theorem cell23_2498511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4, 2].length) (baseStart_2498511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498511 prefixEnd_2498511 := by exact prefixLift 2498511
  have htrace : WordTrace (prefixWord ++ tailWord_2498511) baseStart_2498511 baseEnd_2498511 := by
    simpa [prefixWord, tailWord_2498511, baseEnd_2498511] using wordTrace_append hprefix tailTrace_2498511
  have hstable : (prefixWord ++ tailWord_2498511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498511).length < 2 ^ (prefixWord ++ tailWord_2498511).sum := by decide
  have hdescent : baseEnd_2498511 < baseStart_2498511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498588 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2498588 : Nat := 118140960795 + 2498588 * 2 ^ 59
def prefixEnd_2498588 : Nat := 4983230072969 + 3 ^ 40 * 2498588 * 2
def baseEnd_2498588 : Nat := 1282976601556175496659209

theorem tailTrace_2498588 : CollatzResearch.WordTrace tailWord_2498588 prefixEnd_2498588 1282976601556175496659209 := by
  unfold tailWord_2498588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45565495536024937851104209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60753994048033250468138945 45565495536024937851104209)
  ·
    refine ⟨34174121652018703388328157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45565495536024937851104209 34174121652018703388328157)
    ·
      refine ⟨12815295619507013770623059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34174121652018703388328157 12815295619507013770623059)
      ·
        refine ⟨19222943429260520655934589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12815295619507013770623059 19222943429260520655934589)
        ·
          refine ⟨7208603785972695245975471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19222943429260520655934589 7208603785972695245975471)
          ·
            refine ⟨10812905678959042868963207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208603785972695245975471 10812905678959042868963207)
            ·
              refine ⟨16219358518438564303444811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812905678959042868963207 16219358518438564303444811)
              ·
                refine ⟨24329037777657846455167217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219358518438564303444811 24329037777657846455167217)
                ·
                  refine ⟨18246778333243384841375413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24329037777657846455167217 18246778333243384841375413)
                  ·
                    refine ⟨1710635468741567328878945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18246778333243384841375413 1710635468741567328878945)
                    ·
                      refine ⟨1282976601556175496659209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710635468741567328878945 1282976601556175496659209)
                      ·
                        rfl

theorem cell23_2498588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2498588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498588 prefixEnd_2498588 := by exact prefixLift 2498588
  have htrace : WordTrace (prefixWord ++ tailWord_2498588) baseStart_2498588 baseEnd_2498588 := by
    simpa [prefixWord, tailWord_2498588, baseEnd_2498588] using wordTrace_append hprefix tailTrace_2498588
  have hstable : (prefixWord ++ tailWord_2498588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498588).length < 2 ^ (prefixWord ++ tailWord_2498588).sum := by decide
  have hdescent : baseEnd_2498588 < baseStart_2498588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498611 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 5, 4]
def baseStart_2498611 : Nat := 118140960795 + 2498611 * 2 ^ 59
def prefixEnd_2498611 : Nat := 4983230072969 + 3 ^ 40 * 2498611 * 2
def baseEnd_2498611 : Nat := 427662803870409635557201

theorem tailTrace_2498611 : CollatzResearch.WordTrace tailWord_2498611 prefixEnd_2498611 427662803870409635557201 := by
  unfold tailWord_2498611
  simp only [CollatzResearch.WordTrace]
  refine ⟨91131829950966550630295687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60754553300644367086863791 91131829950966550630295687)
  ·
    refine ⟨136697744926449825945443531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91131829950966550630295687 136697744926449825945443531)
    ·
      refine ⟨205046617389674738918165297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136697744926449825945443531 205046617389674738918165297)
      ·
        refine ⟨153784963042256054188623973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205046617389674738918165297 153784963042256054188623973)
        ·
          refine ⟨28834680570423010160366995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153784963042256054188623973 28834680570423010160366995)
          ·
            refine ⟨43252020855634515240550493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28834680570423010160366995 43252020855634515240550493)
            ·
              refine ⟨16219507820862943215206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43252020855634515240550493 16219507820862943215206435)
              ·
                refine ⟨24329261731294414822809653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219507820862943215206435 24329261731294414822809653)
                ·
                  refine ⟨2280868287308851389638405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24329261731294414822809653 2280868287308851389638405)
                  ·
                    refine ⟨427662803870409635557201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280868287308851389638405 427662803870409635557201)
                    ·
                      rfl

theorem cell23_2498611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 4].length) (baseStart_2498611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498611 prefixEnd_2498611 := by exact prefixLift 2498611
  have htrace : WordTrace (prefixWord ++ tailWord_2498611) baseStart_2498611 baseEnd_2498611 := by
    simpa [prefixWord, tailWord_2498611, baseEnd_2498611] using wordTrace_append hprefix tailTrace_2498611
  have hstable : (prefixWord ++ tailWord_2498611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498611).length < 2 ^ (prefixWord ++ tailWord_2498611).sum := by decide
  have hdescent : baseEnd_2498611 < baseStart_2498611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498645 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_2498645 : Nat := 118140960795 + 2498645 * 2 ^ 59
def prefixEnd_2498645 : Nat := 4983230072969 + 3 ^ 40 * 2498645 * 2
def baseEnd_2498645 : Nat := 427668623317827257882149

theorem tailTrace_2498645 : CollatzResearch.WordTrace tailWord_2498645 prefixEnd_2498645 427668623317827257882149 := by
  unfold tailWord_2498645
  simp only [CollatzResearch.WordTrace]
  refine ⟨91133070032843374437033389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60755380021895582958022259 91133070032843374437033389)
  ·
    refine ⟨34174901262316265413887521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91133070032843374437033389 34174901262316265413887521)
    ·
      refine ⟨25631175946737199060415641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34174901262316265413887521 25631175946737199060415641)
      ·
        refine ⟨19223381960052899295311731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25631175946737199060415641 19223381960052899295311731)
        ·
          refine ⟨28835072940079348942967597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19223381960052899295311731 28835072940079348942967597)
          ·
            refine ⟨10813152352529755853612849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28835072940079348942967597 10813152352529755853612849)
            ·
              refine ⟨8109864264397316890209637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10813152352529755853612849 8109864264397316890209637)
              ·
                refine ⟨1520599549574496916914307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8109864264397316890209637 1520599549574496916914307)
                ·
                  refine ⟨2280899324361745375371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520599549574496916914307 2280899324361745375371461)
                  ·
                    refine ⟨427668623317827257882149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280899324361745375371461 427668623317827257882149)
                    ·
                      rfl

theorem cell23_2498645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_2498645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498645 prefixEnd_2498645 := by exact prefixLift 2498645
  have htrace : WordTrace (prefixWord ++ tailWord_2498645) baseStart_2498645 baseEnd_2498645 := by
    simpa [prefixWord, tailWord_2498645, baseEnd_2498645] using wordTrace_append hprefix tailTrace_2498645
  have hstable : (prefixWord ++ tailWord_2498645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498645).length < 2 ^ (prefixWord ++ tailWord_2498645).sum := by decide
  have hdescent : baseEnd_2498645 < baseStart_2498645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498722 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2498722 : Nat := 118140960795 + 2498722 * 2 ^ 59
def prefixEnd_2498722 : Nat := 4983230072969 + 3 ^ 40 * 2498722 * 2
def baseEnd_2498722 : Nat := 427681802654625990794531

theorem tailTrace_2498722 : CollatzResearch.WordTrace tailWord_2498722 prefixEnd_2498722 427681802654625990794531 := by
  unfold tailWord_2498722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22783969613391104146896605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60757252302376277725057613 22783969613391104146896605)
  ·
    refine ⟨8543988605021664055086227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22783969613391104146896605 8543988605021664055086227)
    ·
      refine ⟨12815982907532496082629341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8543988605021664055086227 12815982907532496082629341)
      ·
        refine ⟨4805993590324686030986003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12815982907532496082629341 4805993590324686030986003)
        ·
          refine ⟨7208990385487029046479005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4805993590324686030986003 7208990385487029046479005)
          ·
            refine ⟨2703371394557635892429627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7208990385487029046479005 2703371394557635892429627)
            ·
              refine ⟨4055057091836453838644441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703371394557635892429627 4055057091836453838644441)
              ·
                refine ⟨3041292818877340378983331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055057091836453838644441 3041292818877340378983331)
                ·
                  refine ⟨4561939228316010568474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041292818877340378983331 4561939228316010568474997)
                  ·
                    refine ⟨427681802654625990794531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4561939228316010568474997 427681802654625990794531)
                    ·
                      rfl

theorem cell23_2498722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2498722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498722 prefixEnd_2498722 := by exact prefixLift 2498722
  have htrace : WordTrace (prefixWord ++ tailWord_2498722) baseStart_2498722 baseEnd_2498722 := by
    simpa [prefixWord, tailWord_2498722, baseEnd_2498722] using wordTrace_append hprefix tailTrace_2498722
  have hstable : (prefixWord ++ tailWord_2498722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498722).length < 2 ^ (prefixWord ++ tailWord_2498722).sum := by decide
  have hdescent : baseEnd_2498722 < baseStart_2498722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498725 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 5, 2, 2]
def baseStart_2498725 : Nat := 118140960795 + 2498725 * 2 ^ 59
def prefixEnd_2498725 : Nat := 4983230072969 + 3 ^ 40 * 2498725 * 2
def baseEnd_2498725 : Nat := 1283046948405841460646079

theorem tailTrace_2498725 : CollatzResearch.WordTrace tailWord_2498725 prefixEnd_2498725 1283046948405841460646079 := by
  unfold tailWord_2498725
  simp only [CollatzResearch.WordTrace]
  refine ⟨91135987872553548099945629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60757325248369032066630419 91135987872553548099945629)
  ·
    refine ⟨34175995452207580537479611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91135987872553548099945629 34175995452207580537479611)
    ·
      refine ⟨51263993178311370806219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34175995452207580537479611 51263993178311370806219417)
      ·
        refine ⟨38447994883733528104664563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51263993178311370806219417 38447994883733528104664563)
        ·
          refine ⟨57671992325600292156996845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38447994883733528104664563 57671992325600292156996845)
          ·
            refine ⟨21626997122100109558873817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57671992325600292156996845 21626997122100109558873817)
            ·
              refine ⟨16220247841575082169155363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21626997122100109558873817 16220247841575082169155363)
              ·
                refine ⟨24330371762362623253733045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16220247841575082169155363 24330371762362623253733045)
                ·
                  refine ⟨2280972352721495930037473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24330371762362623253733045 2280972352721495930037473)
                  ·
                    refine ⟨1710729264541121947528105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2280972352721495930037473 1710729264541121947528105)
                    ·
                      refine ⟨1283046948405841460646079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710729264541121947528105 1283046948405841460646079)
                      ·
                        rfl

theorem cell23_2498725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_2498725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498725 prefixEnd_2498725 := by exact prefixLift 2498725
  have htrace : WordTrace (prefixWord ++ tailWord_2498725) baseStart_2498725 baseEnd_2498725 := by
    simpa [prefixWord, tailWord_2498725, baseEnd_2498725] using wordTrace_append hprefix tailTrace_2498725
  have hstable : (prefixWord ++ tailWord_2498725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498725).length < 2 ^ (prefixWord ++ tailWord_2498725).sum := by decide
  have hdescent : baseEnd_2498725 < baseStart_2498725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498738 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2498738 : Nat := 118140960795 + 2498738 * 2 ^ 59
def prefixEnd_2498738 : Nat := 4983230072969 + 3 ^ 40 * 2498738 * 2
def baseEnd_2498738 : Nat := 1283053623654349909783519

theorem tailTrace_2498738 : CollatzResearch.WordTrace tailWord_2498738 prefixEnd_2498738 1283053623654349909783519 := by
  unfold tailWord_2498738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784115505376612830042217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60757641347670967546779245 22784115505376612830042217)
  ·
    refine ⟨17088086629032459622531663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22784115505376612830042217 17088086629032459622531663)
    ·
      refine ⟨25632129943548689433797495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17088086629032459622531663 25632129943548689433797495)
      ·
        refine ⟨38448194915323034150696243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25632129943548689433797495 38448194915323034150696243)
        ·
          refine ⟨57672292372984551226044365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38448194915323034150696243 57672292372984551226044365)
          ·
            refine ⟨21627109639869206709766637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57672292372984551226044365 21627109639869206709766637)
            ·
              refine ⟨8110166114950952516162489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21627109639869206709766637 8110166114950952516162489)
              ·
                refine ⟨6082624586213214387121867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8110166114950952516162489 6082624586213214387121867)
                ·
                  refine ⟨9123936879319821580682801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082624586213214387121867 9123936879319821580682801)
                  ·
                    refine ⟨6842952659489866185512101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9123936879319821580682801 6842952659489866185512101)
                    ·
                      refine ⟨1283053623654349909783519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6842952659489866185512101 1283053623654349909783519)
                      ·
                        rfl

theorem cell23_2498738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2498738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498738 prefixEnd_2498738 := by exact prefixLift 2498738
  have htrace : WordTrace (prefixWord ++ tailWord_2498738) baseStart_2498738 baseEnd_2498738 := by
    simpa [prefixWord, tailWord_2498738, baseEnd_2498738] using wordTrace_append hprefix tailTrace_2498738
  have hstable : (prefixWord ++ tailWord_2498738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498738).length < 2 ^ (prefixWord ++ tailWord_2498738).sum := by decide
  have hdescent : baseEnd_2498738 < baseStart_2498738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498748 : List Nat := [2, 2, 2, 3, 4, 10]
def baseStart_2498748 : Nat := 118140960795 + 2498748 * 2 ^ 59
def prefixEnd_2498748 : Nat := 4983230072969 + 3 ^ 40 * 2498748 * 2
def baseEnd_2498748 : Nat := 5280077195312324570611

theorem tailTrace_2498748 : CollatzResearch.WordTrace tailWord_2498748 prefixEnd_2498748 5280077195312324570611 := by
  unfold tailWord_2498748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45568413375735111514016449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60757884500980148685355265 45568413375735111514016449)
  ·
    refine ⟨34176310031801333635512337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45568413375735111514016449 34176310031801333635512337)
    ·
      refine ⟨25632232523851000226634253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34176310031801333635512337 25632232523851000226634253)
      ·
        refine ⟨9612087196444125084987845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25632232523851000226634253 9612087196444125084987845)
        ·
          refine ⟨1802266349333273453435221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9612087196444125084987845 1802266349333273453435221)
          ·
            refine ⟨5280077195312324570611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1802266349333273453435221 5280077195312324570611)
            ·
              rfl

theorem cell23_2498748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 10].length) (baseStart_2498748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498748 prefixEnd_2498748 := by exact prefixLift 2498748
  have htrace : WordTrace (prefixWord ++ tailWord_2498748) baseStart_2498748 baseEnd_2498748 := by
    simpa [prefixWord, tailWord_2498748, baseEnd_2498748] using wordTrace_append hprefix tailTrace_2498748
  have hstable : (prefixWord ++ tailWord_2498748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498748).length < 2 ^ (prefixWord ++ tailWord_2498748).sum := by decide
  have hdescent : baseEnd_2498748 < baseStart_2498748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498753 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2498753 : Nat := 118140960795 + 2498753 * 2 ^ 59
def prefixEnd_2498753 : Nat := 4983230072969 + 3 ^ 40 * 2498753 * 2
def baseEnd_2498753 : Nat := 1283061325864167351095951

theorem tailTrace_2498753 : CollatzResearch.WordTrace tailWord_2498753 prefixEnd_2498753 1283061325864167351095951 := by
  unfold tailWord_2498753
  simp only [CollatzResearch.WordTrace]
  refine ⟨91137009116452108881964913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60758006077634739254643275 91137009116452108881964913)
  ·
    refine ⟨68352756837339081661473685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91137009116452108881964913 68352756837339081661473685)
    ·
      refine ⟨3204035476750269452881579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68352756837339081661473685 3204035476750269452881579)
      ·
        refine ⟨4806053215125404179322369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204035476750269452881579 4806053215125404179322369)
        ·
          refine ⟨3604539911344053134491777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806053215125404179322369 3604539911344053134491777)
          ·
            refine ⟨2703404933508039850868833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3604539911344053134491777 2703404933508039850868833)
            ·
              refine ⟨2027553700131029888151625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703404933508039850868833 2027553700131029888151625)
              ·
                refine ⟨1520665275098272416113719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027553700131029888151625 1520665275098272416113719)
                ·
                  refine ⟨2280997912647408624170579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520665275098272416113719 2280997912647408624170579)
                  ·
                    refine ⟨3421496868971112936255869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2280997912647408624170579 3421496868971112936255869)
                    ·
                      refine ⟨1283061325864167351095951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3421496868971112936255869 1283061325864167351095951)
                      ·
                        rfl

theorem cell23_2498753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2498753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498753 prefixEnd_2498753 := by exact prefixLift 2498753
  have htrace : WordTrace (prefixWord ++ tailWord_2498753) baseStart_2498753 baseEnd_2498753 := by
    simpa [prefixWord, tailWord_2498753, baseEnd_2498753] using wordTrace_append hprefix tailTrace_2498753
  have hstable : (prefixWord ++ tailWord_2498753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498753).length < 2 ^ (prefixWord ++ tailWord_2498753).sum := by decide
  have hdescent : baseEnd_2498753 < baseStart_2498753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498785 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_2498785 : Nat := 118140960795 + 2498785 * 2 ^ 59
def prefixEnd_2498785 : Nat := 4983230072969 + 3 ^ 40 * 2498785 * 2
def baseEnd_2498785 : Nat := 1283077757245111225895803

theorem tailTrace_2498785 : CollatzResearch.WordTrace tailWord_2498785 prefixEnd_2498785 1283077757245111225895803 := by
  unfold tailWord_2498785
  simp only [CollatzResearch.WordTrace]
  refine ⟨91138176252336178347129809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60758784168224118898086539 91138176252336178347129809)
  ·
    refine ⟨68353632189252133760347357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91138176252336178347129809 68353632189252133760347357)
    ·
      refine ⟨25632612070969550160130259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68353632189252133760347357 25632612070969550160130259)
      ·
        refine ⟨38448918106454325240195389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25632612070969550160130259 38448918106454325240195389)
        ·
          refine ⟨14418344289920371965073271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38448918106454325240195389 14418344289920371965073271)
          ·
            refine ⟨21627516434880557947609907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418344289920371965073271 21627516434880557947609907)
            ·
              refine ⟨32441274652320836921414861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21627516434880557947609907 32441274652320836921414861)
              ·
                refine ⟨12165477994620313845530573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32441274652320836921414861 12165477994620313845530573)
                ·
                  refine ⟨4562054247982617692073965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12165477994620313845530573 4562054247982617692073965)
                  ·
                    refine ⟨1710770342993481634527737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4562054247982617692073965 1710770342993481634527737)
                    ·
                      refine ⟨1283077757245111225895803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710770342993481634527737 1283077757245111225895803)
                      ·
                        rfl

theorem cell23_2498785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_2498785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498785 prefixEnd_2498785 := by exact prefixLift 2498785
  have htrace : WordTrace (prefixWord ++ tailWord_2498785) baseStart_2498785 baseEnd_2498785 := by
    simpa [prefixWord, tailWord_2498785, baseEnd_2498785] using wordTrace_append hprefix tailTrace_2498785
  have hstable : (prefixWord ++ tailWord_2498785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498785).length < 2 ^ (prefixWord ++ tailWord_2498785).sum := by decide
  have hdescent : baseEnd_2498785 < baseStart_2498785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498828 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2498828 : Nat := 118140960795 + 2498828 * 2 ^ 59
def prefixEnd_2498828 : Nat := 4983230072969 + 3 ^ 40 * 2498828 * 2
def baseEnd_2498828 : Nat := 1283099836913254557658105

theorem tailTrace_2498828 : CollatzResearch.WordTrace tailWord_2498828 prefixEnd_2498828 1283099836913254557658105 := by
  unfold tailWord_2498828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45569872295590198345472569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60759829727453597793963425 45569872295590198345472569)
  ·
    refine ⟨34177404221692648759104427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45569872295590198345472569 34177404221692648759104427)
    ·
      refine ⟨51266106332538973138656641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34177404221692648759104427 51266106332538973138656641)
      ·
        refine ⟨38449579749404229853992481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51266106332538973138656641 38449579749404229853992481)
        ·
          refine ⟨28837184812053172390494361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38449579749404229853992481 28837184812053172390494361)
          ·
            refine ⟨21627888609039879292870771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28837184812053172390494361 21627888609039879292870771)
            ·
              refine ⟨32441832913559818939306157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21627888609039879292870771 32441832913559818939306157)
              ·
                refine ⟨12165687342584932102239809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32441832913559818939306157 12165687342584932102239809)
                ·
                  refine ⟨9124265506938699076679857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12165687342584932102239809 9124265506938699076679857)
                  ·
                    refine ⟨6843199130204024307509893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9124265506938699076679857 6843199130204024307509893)
                    ·
                      refine ⟨1283099836913254557658105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6843199130204024307509893 1283099836913254557658105)
                      ·
                        rfl

theorem cell23_2498828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2498828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498828 prefixEnd_2498828 := by exact prefixLift 2498828
  have htrace : WordTrace (prefixWord ++ tailWord_2498828) baseStart_2498828 baseEnd_2498828 := by
    simpa [prefixWord, tailWord_2498828, baseEnd_2498828] using wordTrace_append hprefix tailTrace_2498828
  have hstable : (prefixWord ++ tailWord_2498828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498828).length < 2 ^ (prefixWord ++ tailWord_2498828).sum := by decide
  have hdescent : baseEnd_2498828 < baseStart_2498828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498831 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_2498831 : Nat := 118140960795 + 2498831 * 2 ^ 59
def prefixEnd_2498831 : Nat := 4983230072969 + 3 ^ 40 * 2498831 * 2
def baseEnd_2498831 : Nat := 1283101377355218045920591

theorem tailTrace_2498831 : CollatzResearch.WordTrace tailWord_2498831 prefixEnd_2498831 1283101377355218045920591 := by
  unfold tailWord_2498831
  simp only [CollatzResearch.WordTrace]
  refine ⟨91139854010169528203304347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60759902673446352135536231 91139854010169528203304347)
  ·
    refine ⟨136709781015254292304956521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91139854010169528203304347 136709781015254292304956521)
    ·
      refine ⟨102532335761440719228717391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136709781015254292304956521 102532335761440719228717391)
      ·
        refine ⟨153798503642161078843076087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102532335761440719228717391 153798503642161078843076087)
        ·
          refine ⟨230697755463241618264614131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153798503642161078843076087 230697755463241618264614131)
          ·
            refine ⟨346046633194862427396921197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230697755463241618264614131 346046633194862427396921197)
            ·
              refine ⟨129767487448073410273845449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346046633194862427396921197 129767487448073410273845449)
              ·
                refine ⟨97325615586055057705384087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129767487448073410273845449 97325615586055057705384087)
                ·
                  refine ⟨145988423379082586558076131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97325615586055057705384087 145988423379082586558076131)
                  ·
                    refine ⟨218982635068623879837114197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145988423379082586558076131 218982635068623879837114197)
                    ·
                      refine ⟨1283101377355218045920591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 218982635068623879837114197 1283101377355218045920591)
                      ·
                        rfl

theorem cell23_2498831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_2498831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498831 prefixEnd_2498831 := by exact prefixLift 2498831
  have htrace : WordTrace (prefixWord ++ tailWord_2498831) baseStart_2498831 baseEnd_2498831 := by
    simpa [prefixWord, tailWord_2498831, baseEnd_2498831] using wordTrace_append hprefix tailTrace_2498831
  have hstable : (prefixWord ++ tailWord_2498831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498831).length < 2 ^ (prefixWord ++ tailWord_2498831).sum := by decide
  have hdescent : baseEnd_2498831 < baseStart_2498831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498888 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2498888 : Nat := 118140960795 + 2498888 * 2 ^ 59
def prefixEnd_2498888 : Nat := 4983230072969 + 3 ^ 40 * 2498888 * 2
def baseEnd_2498888 : Nat := 1283130645752524322907829

theorem tailTrace_2498888 : CollatzResearch.WordTrace tailWord_2498888 prefixEnd_2498888 1283130645752524322907829 := by
  unfold tailWord_2498888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45570966485481513469064659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60761288647308684625419545 45570966485481513469064659)
  ·
    refine ⟨68356449728222270203596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45570966485481513469064659 68356449728222270203596989)
    ·
      refine ⟨25633668648083351326348871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68356449728222270203596989 25633668648083351326348871)
      ·
        refine ⟨38450502972125026989523307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633668648083351326348871 38450502972125026989523307)
        ·
          refine ⟨57675754458187540484284961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38450502972125026989523307 57675754458187540484284961)
          ·
            refine ⟨43256815843640655363213721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57675754458187540484284961 43256815843640655363213721)
            ·
              refine ⟨32442611882730491522410291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43256815843640655363213721 32442611882730491522410291)
              ·
                refine ⟨48663917824095737283615437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32442611882730491522410291 48663917824095737283615437)
                ·
                  refine ⟨18248969184035901481355789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48663917824095737283615437 18248969184035901481355789)
                  ·
                    refine ⟨6843363444013463055508421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18248969184035901481355789 6843363444013463055508421)
                    ·
                      refine ⟨1283130645752524322907829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6843363444013463055508421 1283130645752524322907829)
                      ·
                        rfl

theorem cell23_2498888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2498888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498888 prefixEnd_2498888 := by exact prefixLift 2498888
  have htrace : WordTrace (prefixWord ++ tailWord_2498888) baseStart_2498888 baseEnd_2498888 := by
    simpa [prefixWord, tailWord_2498888, baseEnd_2498888] using wordTrace_append hprefix tailTrace_2498888
  have hstable : (prefixWord ++ tailWord_2498888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498888).length < 2 ^ (prefixWord ++ tailWord_2498888).sum := by decide
  have hdescent : baseEnd_2498888 < baseStart_2498888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498898 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2498898 : Nat := 118140960795 + 2498898 * 2 ^ 59
def prefixEnd_2498898 : Nat := 4983230072969 + 3 ^ 40 * 2498898 * 2
def baseEnd_2498898 : Nat := 427711926853023094594261

theorem tailTrace_2498898 : CollatzResearch.WordTrace tailWord_2498898 prefixEnd_2498898 427711926853023094594261 := by
  unfold tailWord_2498898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785574425231699661498337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60761531800617865763995565 22785574425231699661498337)
  ·
    refine ⟨17089180818923774746123753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22785574425231699661498337 17089180818923774746123753)
    ·
      refine ⟨12816885614192831059592815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17089180818923774746123753 12816885614192831059592815)
      ·
        refine ⟨19225328421289246589389223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12816885614192831059592815 19225328421289246589389223)
        ·
          refine ⟨28837992631933869884083835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19225328421289246589389223 28837992631933869884083835)
          ·
            refine ⟨43256988947900804826125753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28837992631933869884083835 43256988947900804826125753)
            ·
              refine ⟨32442741710925603619594315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43256988947900804826125753 32442741710925603619594315)
              ·
                refine ⟨48664112566388405429391473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32442741710925603619594315 48664112566388405429391473)
                ·
                  refine ⟨36498084424791304072043605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48664112566388405429391473 36498084424791304072043605)
                  ·
                    refine ⟨427711926853023094594261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36498084424791304072043605 427711926853023094594261)
                    ·
                      rfl

theorem cell23_2498898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2498898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498898 prefixEnd_2498898 := by exact prefixLift 2498898
  have htrace : WordTrace (prefixWord ++ tailWord_2498898) baseStart_2498898 baseEnd_2498898 := by
    simpa [prefixWord, tailWord_2498898, baseEnd_2498898] using wordTrace_append hprefix tailTrace_2498898
  have hstable : (prefixWord ++ tailWord_2498898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498898).length < 2 ^ (prefixWord ++ tailWord_2498898).sum := by decide
  have hdescent : baseEnd_2498898 < baseStart_2498898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498905 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 4, 2]
def baseStart_2498905 : Nat := 118140960795 + 2498905 * 2 ^ 59
def prefixEnd_2498905 : Nat := 4983230072969 + 3 ^ 40 * 2498905 * 2
def baseEnd_2498905 : Nat := 1283139374923650756395251

theorem tailTrace_2498905 : CollatzResearch.WordTrace tailWord_2498905 prefixEnd_2498905 1283139374923650756395251 := by
  unfold tailWord_2498905
  simp only [CollatzResearch.WordTrace]
  refine ⟨91142553011901438841498169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60761702007934292560998779 91142553011901438841498169)
  ·
    refine ⟨68356914758926079131123627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91142553011901438841498169 68356914758926079131123627)
    ·
      refine ⟨102535372138389118696685441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68356914758926079131123627 102535372138389118696685441)
      ·
        refine ⟨76901529103791839022514081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102535372138389118696685441 76901529103791839022514081)
        ·
          refine ⟨57676146827843879266885561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76901529103791839022514081 57676146827843879266885561)
          ·
            refine ⟨43257110120882909450164171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57676146827843879266885561 43257110120882909450164171)
            ·
              refine ⟨64885665181324364175246257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43257110120882909450164171 64885665181324364175246257)
              ·
                refine ⟨48664248885993273131434693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64885665181324364175246257 48664248885993273131434693)
                ·
                  refine ⟨9124546666123738712144005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48664248885993273131434693 9124546666123738712144005)
                  ·
                    refine ⟨1710852499898201008527001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9124546666123738712144005 1710852499898201008527001)
                    ·
                      refine ⟨1283139374923650756395251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1710852499898201008527001 1283139374923650756395251)
                      ·
                        rfl

theorem cell23_2498905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_2498905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498905 prefixEnd_2498905 := by exact prefixLift 2498905
  have htrace : WordTrace (prefixWord ++ tailWord_2498905) baseStart_2498905 baseEnd_2498905 := by
    simpa [prefixWord, tailWord_2498905, baseEnd_2498905] using wordTrace_append hprefix tailTrace_2498905
  have hstable : (prefixWord ++ tailWord_2498905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498905).length < 2 ^ (prefixWord ++ tailWord_2498905).sum := by decide
  have hdescent : baseEnd_2498905 < baseStart_2498905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498922 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2498922 : Nat := 118140960795 + 2498922 * 2 ^ 59
def prefixEnd_2498922 : Nat := 4983230072969 + 3 ^ 40 * 2498922 * 2
def baseEnd_2498922 : Nat := 1283148104094777189882673

theorem tailTrace_2498922 : CollatzResearch.WordTrace tailWord_2498922 prefixEnd_2498922 1283148104094777189882673 := by
  unfold tailWord_2498922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785793263209962686216755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60762115368559900496578013 22785793263209962686216755)
  ·
    refine ⟨34178689894814944029325133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22785793263209962686216755 34178689894814944029325133)
    ·
      refine ⟨12817008710555604010996925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34178689894814944029325133 12817008710555604010996925)
      ·
        refine ⟨4806378266458351504123847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12817008710555604010996925 4806378266458351504123847)
        ·
          refine ⟨7209567399687527256185771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806378266458351504123847 7209567399687527256185771)
          ·
            refine ⟨10814351099531290884278657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7209567399687527256185771 10814351099531290884278657)
            ·
              refine ⟨8110763324648468163208993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10814351099531290884278657 8110763324648468163208993)
              ·
                refine ⟨6083072493486351122406745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8110763324648468163208993 6083072493486351122406745)
                ·
                  refine ⟨4562304370114763341805059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6083072493486351122406745 4562304370114763341805059)
                  ·
                    refine ⟨6843456555172145012707589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4562304370114763341805059 6843456555172145012707589)
                    ·
                      refine ⟨1283148104094777189882673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6843456555172145012707589 1283148104094777189882673)
                      ·
                        rfl

theorem cell23_2498922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2498922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2498922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2498922 prefixEnd_2498922 := by exact prefixLift 2498922
  have htrace : WordTrace (prefixWord ++ tailWord_2498922) baseStart_2498922 baseEnd_2498922 := by
    simpa [prefixWord, tailWord_2498922, baseEnd_2498922] using wordTrace_append hprefix tailTrace_2498922
  have hstable : (prefixWord ++ tailWord_2498922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498922).length < 2 ^ (prefixWord ++ tailWord_2498922).sum := by decide
  have hdescent : baseEnd_2498922 < baseStart_2498922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499025 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_2499025 : Nat := 118140960795 + 2499025 * 2 ^ 59
def prefixEnd_2499025 : Nat := 4983230072969 + 3 ^ 40 * 2499025 * 2
def baseEnd_2499025 : Nat := 1283200992602190286894699

theorem tailTrace_2499025 : CollatzResearch.WordTrace tailWord_2499025 prefixEnd_2499025 1283200992602190286894699 := by
  unfold tailWord_2499025
  simp only [CollatzResearch.WordTrace]
  refine ⟨91146929771466699335866529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60764619847644466223911019 91146929771466699335866529)
  ·
    refine ⟨68360197328600024501899897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91146929771466699335866529 68360197328600024501899897)
    ·
      refine ⟨51270147996450018376424923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68360197328600024501899897 51270147996450018376424923)
      ·
        refine ⟨76905221994675027564637385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51270147996450018376424923 76905221994675027564637385)
        ·
          refine ⟨57678916496006270673478039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76905221994675027564637385 57678916496006270673478039)
          ·
            refine ⟨86518374744009406010217059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57678916496006270673478039 86518374744009406010217059)
            ·
              refine ⟨129777562116014109015325589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86518374744009406010217059 129777562116014109015325589)
              ·
                refine ⟨6083323224188161360093387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129777562116014109015325589 6083323224188161360093387)
                ·
                  refine ⟨9124984836282242040140081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083323224188161360093387 9124984836282242040140081)
                  ·
                    refine ⟨6843738627211681530105061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9124984836282242040140081 6843738627211681530105061)
                    ·
                      refine ⟨1283200992602190286894699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6843738627211681530105061 1283200992602190286894699)
                      ·
                        rfl

theorem cell23_2499025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_2499025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499025 prefixEnd_2499025 := by exact prefixLift 2499025
  have htrace : WordTrace (prefixWord ++ tailWord_2499025) baseStart_2499025 baseEnd_2499025 := by
    simpa [prefixWord, tailWord_2499025, baseEnd_2499025] using wordTrace_append hprefix tailTrace_2499025
  have hstable : (prefixWord ++ tailWord_2499025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499025).length < 2 ^ (prefixWord ++ tailWord_2499025).sum := by decide
  have hdescent : baseEnd_2499025 < baseStart_2499025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499079 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2499079 : Nat := 118140960795 + 2499079 * 2 ^ 59
def prefixEnd_2499079 : Nat := 4983230072969 + 3 ^ 40 * 2499079 * 2
def baseEnd_2499079 : Nat := 1283228720557533075619451

theorem tailTrace_2499079 : CollatzResearch.WordTrace tailWord_2499079 prefixEnd_2499079 1283228720557533075619451 := by
  unfold tailWord_2499079
  simp only [CollatzResearch.WordTrace]
  refine ⟨91148899313271066558332291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60765932875514044372221527 91148899313271066558332291)
  ·
    refine ⟨136723348969906599837498437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91148899313271066558332291 136723348969906599837498437)
    ·
      refine ⟨25635627931857487469530957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136723348969906599837498437 25635627931857487469530957)
      ·
        refine ⟨9613360474446557801074109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25635627931857487469530957 9613360474446557801074109)
        ·
          refine ⟨3605010177917459175402791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9613360474446557801074109 3605010177917459175402791)
          ·
            refine ⟨5407515266876188763104187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605010177917459175402791 5407515266876188763104187)
            ·
              refine ⟨8111272900314283144656281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407515266876188763104187 8111272900314283144656281)
              ·
                refine ⟨6083454675235712358492211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111272900314283144656281 6083454675235712358492211)
                ·
                  refine ⟨9125182012853568537738317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083454675235712358492211 9125182012853568537738317)
                  ·
                    refine ⟨3421943254820088201651869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9125182012853568537738317 3421943254820088201651869)
                    ·
                      refine ⟨1283228720557533075619451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3421943254820088201651869 1283228720557533075619451)
                      ·
                        rfl

theorem cell23_2499079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2499079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499079 prefixEnd_2499079 := by exact prefixLift 2499079
  have htrace : WordTrace (prefixWord ++ tailWord_2499079) baseStart_2499079 baseEnd_2499079 := by
    simpa [prefixWord, tailWord_2499079, baseEnd_2499079] using wordTrace_append hprefix tailTrace_2499079
  have hstable : (prefixWord ++ tailWord_2499079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499079).length < 2 ^ (prefixWord ++ tailWord_2499079).sum := by decide
  have hdescent : baseEnd_2499079 < baseStart_2499079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499096 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2499096 : Nat := 118140960795 + 2499096 * 2 ^ 59
def prefixEnd_2499096 : Nat := 4983230072969 + 3 ^ 40 * 2499096 * 2
def baseEnd_2499096 : Nat := 1283237449728659509106873

theorem tailTrace_2499096 : CollatzResearch.WordTrace tailWord_2499096 prefixEnd_2499096 1283237449728659509106873 := by
  unfold tailWord_2499096
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574759677104739230850571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60766346236139652307800761 45574759677104739230850571)
  ·
    refine ⟨68362139515657108846275857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45574759677104739230850571 68362139515657108846275857)
    ·
      refine ⟨51271604636742831634706893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68362139515657108846275857 51271604636742831634706893)
      ·
        refine ⟨19226851738778561863015085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51271604636742831634706893 19226851738778561863015085)
        ·
          refine ⟨7210069402041960698630657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19226851738778561863015085 7210069402041960698630657)
          ·
            refine ⟨5407552051531470523972993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7210069402041960698630657 5407552051531470523972993)
            ·
              refine ⟨4055664038648602892979745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5407552051531470523972993 4055664038648602892979745)
              ·
                refine ⟨3041748028986452169734809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055664038648602892979745 3041748028986452169734809)
                ·
                  refine ⟨2281311021739839127301107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041748028986452169734809 2281311021739839127301107)
                  ·
                    refine ⟨3421966532609758690951661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2281311021739839127301107 3421966532609758690951661)
                    ·
                      refine ⟨1283237449728659509106873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3421966532609758690951661 1283237449728659509106873)
                      ·
                        rfl

theorem cell23_2499096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2499096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499096 prefixEnd_2499096 := by exact prefixLift 2499096
  have htrace : WordTrace (prefixWord ++ tailWord_2499096) baseStart_2499096 baseEnd_2499096 := by
    simpa [prefixWord, tailWord_2499096, baseEnd_2499096] using wordTrace_append hprefix tailTrace_2499096
  have hstable : (prefixWord ++ tailWord_2499096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499096).length < 2 ^ (prefixWord ++ tailWord_2499096).sum := by decide
  have hdescent : baseEnd_2499096 < baseStart_2499096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499112 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2499112 : Nat := 118140960795 + 2499112 * 2 ^ 59
def prefixEnd_2499112 : Nat := 4983230072969 + 3 ^ 40 * 2499112 * 2
def baseEnd_2499112 : Nat := 427748555139710482168933

theorem tailTrace_2499112 : CollatzResearch.WordTrace tailWord_2499112 prefixEnd_2499112 427748555139710482168933 := by
  unfold tailWord_2499112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575051461075756597141795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60766735281434342129522393 45575051461075756597141795)
  ·
    refine ⟨68362577191613634895712693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45575051461075756597141795 68362577191613634895712693)
    ·
      refine ⟨6408991611713778271473065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68362577191613634895712693 6408991611713778271473065)
      ·
        refine ⟨4806743708785333703604799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6408991611713778271473065 4806743708785333703604799)
        ·
          refine ⟨7210115563178000555407199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806743708785333703604799 7210115563178000555407199)
          ·
            refine ⟨10815173344767000833110799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210115563178000555407199 10815173344767000833110799)
            ·
              refine ⟨16222760017150501249666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10815173344767000833110799 16222760017150501249666199)
              ·
                refine ⟨24334140025725751874499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16222760017150501249666199 24334140025725751874499299)
                ·
                  refine ⟨36501210038588627811748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24334140025725751874499299 36501210038588627811748949)
                  ·
                    refine ⟨427748555139710482168933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36501210038588627811748949 427748555139710482168933)
                    ·
                      rfl

theorem cell23_2499112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2499112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499112 prefixEnd_2499112 := by exact prefixLift 2499112
  have htrace : WordTrace (prefixWord ++ tailWord_2499112) baseStart_2499112 baseEnd_2499112 := by
    simpa [prefixWord, tailWord_2499112, baseEnd_2499112] using wordTrace_append hprefix tailTrace_2499112
  have hstable : (prefixWord ++ tailWord_2499112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499112).length < 2 ^ (prefixWord ++ tailWord_2499112).sum := by decide
  have hdescent : baseEnd_2499112 < baseStart_2499112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499149 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2499149 : Nat := 118140960795 + 2499149 * 2 ^ 59
def prefixEnd_2499149 : Nat := 4983230072969 + 3 ^ 40 * 2499149 * 2
def baseEnd_2499149 : Nat := 1283264664203347801744129

theorem tailTrace_2499149 : CollatzResearch.WordTrace tailWord_2499149 prefixEnd_2499149 1283264664203347801744129 := by
  unfold tailWord_2499149
  simp only [CollatzResearch.WordTrace]
  refine ⟨91151452423017468513380501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60767634948678312342253667 91151452423017468513380501)
  ·
    refine ⟨4272724332328943836564711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91151452423017468513380501 4272724332328943836564711)
    ·
      refine ⟨6409086498493415754847067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272724332328943836564711 6409086498493415754847067)
      ·
        refine ⟨9613629747740123632270601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409086498493415754847067 9613629747740123632270601)
        ·
          refine ⟨7210222310805092724202951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9613629747740123632270601 7210222310805092724202951)
          ·
            refine ⟨10815333466207639086304427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210222310805092724202951 10815333466207639086304427)
            ·
              refine ⟨16223000199311458629456641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10815333466207639086304427 16223000199311458629456641)
              ·
                refine ⟨12167250149483593972092481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16223000199311458629456641 12167250149483593972092481)
                ·
                  refine ⟨9125437612112695479069361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12167250149483593972092481 9125437612112695479069361)
                  ·
                    refine ⟨6844078209084521609302021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9125437612112695479069361 6844078209084521609302021)
                    ·
                      refine ⟨1283264664203347801744129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6844078209084521609302021 1283264664203347801744129)
                      ·
                        rfl

theorem cell23_2499149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2499149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499149 prefixEnd_2499149 := by exact prefixLift 2499149
  have htrace : WordTrace (prefixWord ++ tailWord_2499149) baseStart_2499149 baseEnd_2499149 := by
    simpa [prefixWord, tailWord_2499149, baseEnd_2499149] using wordTrace_append hprefix tailTrace_2499149
  have hstable : (prefixWord ++ tailWord_2499149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499149).length < 2 ^ (prefixWord ++ tailWord_2499149).sum := by decide
  have hdescent : baseEnd_2499149 < baseStart_2499149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499153 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_2499153 : Nat := 118140960795 + 2499153 * 2 ^ 59
def prefixEnd_2499153 : Nat := 4983230072969 + 3 ^ 40 * 2499153 * 2
def baseEnd_2499153 : Nat := 1283266718125965786094111

theorem tailTrace_2499153 : CollatzResearch.WordTrace tailWord_2499153 prefixEnd_2499153 1283266718125965786094111 := by
  unfold tailWord_2499153
  simp only [CollatzResearch.WordTrace]
  refine ⟨91151598315002977196526113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60767732210001984797684075 91151598315002977196526113)
  ·
    refine ⟨68363698736252232897394585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91151598315002977196526113 68363698736252232897394585)
    ·
      refine ⟨51272774052189174673045939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68363698736252232897394585 51272774052189174673045939)
      ·
        refine ⟨76909161078283762009568909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51272774052189174673045939 76909161078283762009568909)
        ·
          refine ⟨28840935404356410753588341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76909161078283762009568909 28840935404356410753588341)
          ·
            refine ⟨2703837694158413508148907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28840935404356410753588341 2703837694158413508148907)
            ·
              refine ⟨4055756541237620262223361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703837694158413508148907 4055756541237620262223361)
              ·
                refine ⟨3041817405928215196667521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055756541237620262223361 3041817405928215196667521)
                ·
                  refine ⟨2281363054446161397500641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041817405928215196667521 2281363054446161397500641)
                  ·
                    refine ⟨1711022290834621048125481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2281363054446161397500641 1711022290834621048125481)
                    ·
                      refine ⟨1283266718125965786094111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711022290834621048125481 1283266718125965786094111)
                      ·
                        rfl

theorem cell23_2499153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_2499153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499153 prefixEnd_2499153 := by exact prefixLift 2499153
  have htrace : WordTrace (prefixWord ++ tailWord_2499153) baseStart_2499153 baseEnd_2499153 := by
    simpa [prefixWord, tailWord_2499153, baseEnd_2499153] using wordTrace_append hprefix tailTrace_2499153
  have hstable : (prefixWord ++ tailWord_2499153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499153).length < 2 ^ (prefixWord ++ tailWord_2499153).sum := by decide
  have hdescent : baseEnd_2499153 < baseStart_2499153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499170 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2499170 : Nat := 118140960795 + 2499170 * 2 ^ 59
def prefixEnd_2499170 : Nat := 4983230072969 + 3 ^ 40 * 2499170 * 2
def baseEnd_2499170 : Nat := 1283275447297092219581533

theorem tailTrace_2499170 : CollatzResearch.WordTrace tailWord_2499170 prefixEnd_2499170 1283275447297092219581533 := by
  unfold tailWord_2499170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22788054588985347274973741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60768145570627592733263309 22788054588985347274973741)
  ·
    refine ⟨8545520470869505228115153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22788054588985347274973741 8545520470869505228115153)
    ·
      refine ⟨6409140353152128921086365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8545520470869505228115153 6409140353152128921086365)
      ·
        refine ⟨2403427632432048345407387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6409140353152128921086365 2403427632432048345407387)
        ·
          refine ⟨3605141448648072518111081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403427632432048345407387 3605141448648072518111081)
          ·
            refine ⟨2703856086486054388583311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3605141448648072518111081 2703856086486054388583311)
            ·
              refine ⟨4055784129729081582874967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703856086486054388583311 4055784129729081582874967)
              ·
                refine ⟨6083676194593622374312451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055784129729081582874967 6083676194593622374312451)
                ·
                  refine ⟨9125514291890433561468677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083676194593622374312451 9125514291890433561468677)
                  ·
                    refine ⟨1711033929729456292775377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9125514291890433561468677 1711033929729456292775377)
                    ·
                      refine ⟨1283275447297092219581533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711033929729456292775377 1283275447297092219581533)
                      ·
                        rfl

theorem cell23_2499170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2499170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499170 prefixEnd_2499170 := by exact prefixLift 2499170
  have htrace : WordTrace (prefixWord ++ tailWord_2499170) baseStart_2499170 baseEnd_2499170 := by
    simpa [prefixWord, tailWord_2499170, baseEnd_2499170] using wordTrace_append hprefix tailTrace_2499170
  have hstable : (prefixWord ++ tailWord_2499170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499170).length < 2 ^ (prefixWord ++ tailWord_2499170).sum := by decide
  have hdescent : baseEnd_2499170 < baseStart_2499170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499212 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2499212 : Nat := 118140960795 + 2499212 * 2 ^ 59
def prefixEnd_2499212 : Nat := 4983230072969 + 3 ^ 40 * 2499212 * 2
def baseEnd_2499212 : Nat := 1283297013484581055256339

theorem tailTrace_2499212 : CollatzResearch.WordTrace tailWord_2499212 prefixEnd_2499212 1283297013484581055256339 := by
  unfold tailWord_2499212
  simp only [CollatzResearch.WordTrace]
  refine ⟨45576875110894615136461945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60769166814526153515282593 45576875110894615136461945)
  ·
    refine ⟨34182656333170961352346459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45576875110894615136461945 34182656333170961352346459)
    ·
      refine ⟨51273984499756442028519689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34182656333170961352346459 51273984499756442028519689)
      ·
        refine ⟨38455488374817331521389767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51273984499756442028519689 38455488374817331521389767)
        ·
          refine ⟨57683232562225997282084651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38455488374817331521389767 57683232562225997282084651)
          ·
            refine ⟨86524848843338995923126977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57683232562225997282084651 86524848843338995923126977)
            ·
              refine ⟨64893636632504246942345233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86524848843338995923126977 64893636632504246942345233)
              ·
                refine ⟨48670227474378185206758925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64893636632504246942345233 48670227474378185206758925)
                ·
                  refine ⟨18251335302891819452534597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48670227474378185206758925 18251335302891819452534597)
                  ·
                    refine ⟨3422125369292216147350237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18251335302891819452534597 3422125369292216147350237)
                    ·
                      refine ⟨1283297013484581055256339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3422125369292216147350237 1283297013484581055256339)
                      ·
                        rfl

theorem cell23_2499212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2499212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499212 prefixEnd_2499212 := by exact prefixLift 2499212
  have htrace : WordTrace (prefixWord ++ tailWord_2499212) baseStart_2499212 baseEnd_2499212 := by
    simpa [prefixWord, tailWord_2499212, baseEnd_2499212] using wordTrace_append hprefix tailTrace_2499212
  have hstable : (prefixWord ++ tailWord_2499212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499212).length < 2 ^ (prefixWord ++ tailWord_2499212).sum := by decide
  have hdescent : baseEnd_2499212 < baseStart_2499212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499309 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_2499309 : Nat := 118140960795 + 2499309 * 2 ^ 59
def prefixEnd_2499309 : Nat := 4983230072969 + 3 ^ 40 * 2499309 * 2
def baseEnd_2499309 : Nat := 427782273702689058581131

theorem tailTrace_2499309 : CollatzResearch.WordTrace tailWord_2499309 prefixEnd_2499309 427782273702689058581131 := by
  unfold tailWord_2499309
  simp only [CollatzResearch.WordTrace]
  refine ⟨91157288102437815839204981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60771525401625210559469987 91157288102437815839204981)
  ·
    refine ⟨8545995759603545234925467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91157288102437815839204981 8545995759603545234925467)
    ·
      refine ⟨12818993639405317852388201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545995759603545234925467 12818993639405317852388201)
      ·
        refine ⟨9614245229553988389291151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12818993639405317852388201 9614245229553988389291151)
        ·
          refine ⟨14421367844330982583936727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9614245229553988389291151 14421367844330982583936727)
          ·
            refine ⟨21632051766496473875905091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14421367844330982583936727 21632051766496473875905091)
            ·
              refine ⟨32448077649744710813857637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21632051766496473875905091 32448077649744710813857637)
              ·
                refine ⟨6084014559327133277598307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32448077649744710813857637 6084014559327133277598307)
                ·
                  refine ⟨9126021838990699916397461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6084014559327133277598307 9126021838990699916397461)
                  ·
                    refine ⟨427782273702689058581131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9126021838990699916397461 427782273702689058581131)
                    ·
                      rfl

theorem cell23_2499309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_2499309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499309 prefixEnd_2499309 := by exact prefixLift 2499309
  have htrace : WordTrace (prefixWord ++ tailWord_2499309) baseStart_2499309 baseEnd_2499309 := by
    simpa [prefixWord, tailWord_2499309, baseEnd_2499309] using wordTrace_append hprefix tailTrace_2499309
  have hstable : (prefixWord ++ tailWord_2499309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499309).length < 2 ^ (prefixWord ++ tailWord_2499309).sum := by decide
  have hdescent : baseEnd_2499309 < baseStart_2499309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499310 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_2499310 : Nat := 118140960795 + 2499310 * 2 ^ 59
def prefixEnd_2499310 : Nat := 4983230072969 + 3 ^ 40 * 2499310 * 2
def baseEnd_2499310 : Nat := 1283347334588721671830889

theorem tailTrace_2499310 : CollatzResearch.WordTrace tailWord_2499310 prefixEnd_2499310 1283347334588721671830889 := by
  unfold tailWord_2499310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394665571929274126248923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60771549716956128673327589 11394665571929274126248923)
  ·
    refine ⟨17091998357893911189373385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11394665571929274126248923 17091998357893911189373385)
    ·
      refine ⟨12818998768420433392030039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17091998357893911189373385 12818998768420433392030039)
      ·
        refine ⟨19228498152630650088045059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12818998768420433392030039 19228498152630650088045059)
        ·
          refine ⟨28842747228945975132067589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19228498152630650088045059 28842747228945975132067589)
          ·
            refine ⟨5408015105427370337262673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28842747228945975132067589 5408015105427370337262673)
            ·
              refine ⟨4056011329070527752947005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5408015105427370337262673 4056011329070527752947005)
              ·
                refine ⟨1521004248401447907355127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4056011329070527752947005 1521004248401447907355127)
                ·
                  refine ⟨2281506372602171861032691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521004248401447907355127 2281506372602171861032691)
                  ·
                    refine ⟨3422259558903257791549037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2281506372602171861032691 3422259558903257791549037)
                    ·
                      refine ⟨1283347334588721671830889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3422259558903257791549037 1283347334588721671830889)
                      ·
                        rfl

theorem cell23_2499310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_2499310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499310 prefixEnd_2499310 := by exact prefixLift 2499310
  have htrace : WordTrace (prefixWord ++ tailWord_2499310) baseStart_2499310 baseEnd_2499310 := by
    simpa [prefixWord, tailWord_2499310, baseEnd_2499310] using wordTrace_append hprefix tailTrace_2499310
  have hstable : (prefixWord ++ tailWord_2499310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499310).length < 2 ^ (prefixWord ++ tailWord_2499310).sum := by decide
  have hdescent : baseEnd_2499310 < baseStart_2499310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499317 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 6]
def baseStart_2499317 : Nat := 118140960795 + 2499317 * 2 ^ 59
def prefixEnd_2499317 : Nat := 4983230072969 + 3 ^ 40 * 2499317 * 2
def baseEnd_2499317 : Nat := 142594547661478127160373

theorem tailTrace_2499317 : CollatzResearch.WordTrace tailWord_2499317 prefixEnd_2499317 142594547661478127160373 := by
  unfold tailWord_2499317
  simp only [CollatzResearch.WordTrace]
  refine ⟨91157579886408833205496205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60771719924272555470330803 91157579886408833205496205)
  ·
    refine ⟨34184092457403312452061077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91157579886408833205496205 34184092457403312452061077)
    ·
      refine ⟨1602379333940780271190363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34184092457403312452061077 1602379333940780271190363)
      ·
        refine ⟨2403569000911170406785545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602379333940780271190363 2403569000911170406785545)
        ·
          refine ⟨1802676750683377805089159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403569000911170406785545 1802676750683377805089159)
          ·
            refine ⟨2704015126025066707633739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802676750683377805089159 2704015126025066707633739)
            ·
              refine ⟨4056022689037600061450609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704015126025066707633739 4056022689037600061450609)
              ·
                refine ⟨3042017016778200046087957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4056022689037600061450609 3042017016778200046087957)
                ·
                  refine ⟨142594547661478127160373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3042017016778200046087957 142594547661478127160373)
                  ·
                    rfl

theorem cell23_2499317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_2499317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499317 prefixEnd_2499317 := by exact prefixLift 2499317
  have htrace : WordTrace (prefixWord ++ tailWord_2499317) baseStart_2499317 baseEnd_2499317 := by
    simpa [prefixWord, tailWord_2499317, baseEnd_2499317] using wordTrace_append hprefix tailTrace_2499317
  have hstable : (prefixWord ++ tailWord_2499317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499317).length < 2 ^ (prefixWord ++ tailWord_2499317).sum := by decide
  have hdescent : baseEnd_2499317 < baseStart_2499317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499356 : List Nat := [2, 2, 3, 1, 1, 5, 2, 7]
def baseStart_2499356 : Nat := 118140960795 + 2499356 * 2 ^ 59
def prefixEnd_2499356 : Nat := 4983230072969 + 3 ^ 40 * 2499356 * 2
def baseEnd_2499356 : Nat := 47532257581438092290951

theorem tailTrace_2499356 : CollatzResearch.WordTrace tailWord_2499356 prefixEnd_2499356 47532257581438092290951 := by
  unfold tailWord_2499356
  simp only [CollatzResearch.WordTrace]
  refine ⟨45579501166633771433082961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60772668222178361910777281 45579501166633771433082961)
  ·
    refine ⟨34184625874975328574812221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45579501166633771433082961 34184625874975328574812221)
    ·
      refine ⟨12819234703115748215554583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34184625874975328574812221 12819234703115748215554583)
      ·
        refine ⟨19228852054673622323331875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12819234703115748215554583 19228852054673622323331875)
        ·
          refine ⟨28843278082010433484997813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19228852054673622323331875 28843278082010433484997813)
          ·
            refine ⟨2704057320188478139218545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28843278082010433484997813 2704057320188478139218545)
            ·
              refine ⟨2028042990141358604413909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704057320188478139218545 2028042990141358604413909)
              ·
                refine ⟨47532257581438092290951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2028042990141358604413909 47532257581438092290951)
                ·
                  rfl

theorem cell23_2499356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 7].length) (baseStart_2499356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499356 prefixEnd_2499356 := by exact prefixLift 2499356
  have htrace : WordTrace (prefixWord ++ tailWord_2499356) baseStart_2499356 baseEnd_2499356 := by
    simpa [prefixWord, tailWord_2499356, baseEnd_2499356] using wordTrace_append hprefix tailTrace_2499356
  have hstable : (prefixWord ++ tailWord_2499356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499356).length < 2 ^ (prefixWord ++ tailWord_2499356).sum := by decide
  have hdescent : baseEnd_2499356 < baseStart_2499356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499373 : List Nat := [1, 5, 3, 2, 1, 2, 9]
def baseStart_2499373 : Nat := 118140960795 + 2499373 * 2 ^ 59
def prefixEnd_2499373 : Nat := 4983230072969 + 3 ^ 40 * 2499373 * 2
def baseEnd_2499373 : Nat := 15844193628024134880779

theorem tailTrace_2499373 : CollatzResearch.WordTrace tailWord_2499373 prefixEnd_2499373 15844193628024134880779 := by
  unfold tailWord_2499373
  simp only [CollatzResearch.WordTrace]
  refine ⟨91159622374205954769534773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60773081582803969846356515 91159622374205954769534773)
  ·
    refine ⟨8546214597581808259643885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91159622374205954769534773 8546214597581808259643885)
    ·
      refine ⟨3204830474093178097366457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8546214597581808259643885 3204830474093178097366457)
      ·
        refine ⟨2403622855569883573024843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204830474093178097366457 2403622855569883573024843)
        ·
          refine ⟨3605434283354825359537265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403622855569883573024843 3605434283354825359537265)
          ·
            refine ⟨2704075712516119019652949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3605434283354825359537265 2704075712516119019652949)
            ·
              refine ⟨15844193628024134880779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2704075712516119019652949 15844193628024134880779)
              ·
                rfl

theorem cell23_2499373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 9].length) (baseStart_2499373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499373 prefixEnd_2499373 := by exact prefixLift 2499373
  have htrace : WordTrace (prefixWord ++ tailWord_2499373) baseStart_2499373 baseEnd_2499373 := by
    simpa [prefixWord, tailWord_2499373, baseEnd_2499373] using wordTrace_append hprefix tailTrace_2499373
  have hstable : (prefixWord ++ tailWord_2499373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499373).length < 2 ^ (prefixWord ++ tailWord_2499373).sum := by decide
  have hdescent : baseEnd_2499373 < baseStart_2499373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499406 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_2499406 : Nat := 118140960795 + 2499406 * 2 ^ 59
def prefixEnd_2499406 : Nat := 4983230072969 + 3 ^ 40 * 2499406 * 2
def baseEnd_2499406 : Nat := 1283396628731553296230447

theorem tailTrace_2499406 : CollatzResearch.WordTrace tailWord_2499406 prefixEnd_2499406 1283396628731553296230447 := by
  unfold tailWord_2499406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11395103247885800175685759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60773883988724267603657381 11395103247885800175685759)
  ·
    refine ⟨17092654871828700263528639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11395103247885800175685759 17092654871828700263528639)
    ·
      refine ⟨25638982307743050395292959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17092654871828700263528639 25638982307743050395292959)
      ·
        refine ⟨38458473461614575592939439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25638982307743050395292959 38458473461614575592939439)
        ·
          refine ⟨57687710192421863389409159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38458473461614575592939439 57687710192421863389409159)
          ·
            refine ⟨86531565288632795084113739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57687710192421863389409159 86531565288632795084113739)
            ·
              refine ⟨129797347932949192626170609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86531565288632795084113739 129797347932949192626170609)
              ·
                refine ⟨97348010949711894469627957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129797347932949192626170609 97348010949711894469627957)
                ·
                  refine ⟨9126376026535490106527621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97348010949711894469627957 9126376026535490106527621)
                  ·
                    refine ⟨1711195504975404394973929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9126376026535490106527621 1711195504975404394973929)
                    ·
                      refine ⟨1283396628731553296230447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711195504975404394973929 1283396628731553296230447)
                      ·
                        rfl

theorem cell23_2499406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_2499406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499406 prefixEnd_2499406 := by exact prefixLift 2499406
  have htrace : WordTrace (prefixWord ++ tailWord_2499406) baseStart_2499406 baseEnd_2499406 := by
    simpa [prefixWord, tailWord_2499406, baseEnd_2499406] using wordTrace_append hprefix tailTrace_2499406
  have hstable : (prefixWord ++ tailWord_2499406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499406).length < 2 ^ (prefixWord ++ tailWord_2499406).sum := by decide
  have hdescent : baseEnd_2499406 < baseStart_2499406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499439 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_2499439 : Nat := 118140960795 + 2499439 * 2 ^ 59
def prefixEnd_2499439 : Nat := 4983230072969 + 3 ^ 40 * 2499439 * 2
def baseEnd_2499439 : Nat := 1283413573593151667117795

theorem tailTrace_2499439 : CollatzResearch.WordTrace tailWord_2499439 prefixEnd_2499439 1283413573593151667117795 := by
  unfold tailWord_2499439
  simp only [CollatzResearch.WordTrace]
  refine ⟨91162029591966848041437371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60774686394644565360958247 91162029591966848041437371)
  ·
    refine ⟨136743044387950272062156057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91162029591966848041437371 136743044387950272062156057)
    ·
      refine ⟨102557283290962704046617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136743044387950272062156057 102557283290962704046617043)
      ·
        refine ⟨153835924936444056069925565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102557283290962704046617043 153835924936444056069925565)
        ·
          refine ⟨57688471851166521026222087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153835924936444056069925565 57688471851166521026222087)
          ·
            refine ⟨86532707776749781539333131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57688471851166521026222087 86532707776749781539333131)
            ·
              refine ⟨129799061665124672308999697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86532707776749781539333131 129799061665124672308999697)
              ·
                refine ⟨97349296248843504231749773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129799061665124672308999697 97349296248843504231749773)
                ·
                  refine ⟨36505986093316314086906165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97349296248843504231749773 36505986093316314086906165)
                  ·
                    refine ⟨3422436196248404445647453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36505986093316314086906165 3422436196248404445647453)
                    ·
                      refine ⟨1283413573593151667117795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3422436196248404445647453 1283413573593151667117795)
                      ·
                        rfl

theorem cell23_2499439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_2499439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499439 prefixEnd_2499439 := by exact prefixLift 2499439
  have htrace : WordTrace (prefixWord ++ tailWord_2499439) baseStart_2499439 baseEnd_2499439 := by
    simpa [prefixWord, tailWord_2499439, baseEnd_2499439] using wordTrace_append hprefix tailTrace_2499439
  have hstable : (prefixWord ++ tailWord_2499439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499439).length < 2 ^ (prefixWord ++ tailWord_2499439).sum := by decide
  have hdescent : baseEnd_2499439 < baseStart_2499439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499459 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 7]
def baseStart_2499459 : Nat := 118140960795 + 2499459 * 2 ^ 59
def prefixEnd_2499459 : Nat := 4983230072969 + 3 ^ 40 * 2499459 * 2
def baseEnd_2499459 : Nat := 427807947735413862955901

theorem tailTrace_2499459 : CollatzResearch.WordTrace tailWord_2499459 prefixEnd_2499459 427807947735413862955901 := by
  unfold tailWord_2499459
  simp only [CollatzResearch.WordTrace]
  refine ⟨91162759051894391457165431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60775172701262927638110287 91162759051894391457165431)
  ·
    refine ⟨136744138577841587185748147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91162759051894391457165431 136744138577841587185748147)
    ·
      refine ⟨205116207866762380778622221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136744138577841587185748147 205116207866762380778622221)
      ·
        refine ⟨76918577950035892791983333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205116207866762380778622221 76918577950035892791983333)
        ·
          refine ⟨14422233365631729898496875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76918577950035892791983333 14422233365631729898496875)
          ·
            refine ⟨21633350048447594847745313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14422233365631729898496875 21633350048447594847745313)
            ·
              refine ⟨16225012536335696135808985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21633350048447594847745313 16225012536335696135808985)
              ·
                refine ⟨12168759402251772101856739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16225012536335696135808985 12168759402251772101856739)
                ·
                  refine ⟨18253139103377658152785109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12168759402251772101856739 18253139103377658152785109)
                  ·
                    refine ⟨427807947735413862955901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18253139103377658152785109 427807947735413862955901)
                    ·
                      rfl

theorem cell23_2499459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_2499459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499459 prefixEnd_2499459 := by exact prefixLift 2499459
  have htrace : WordTrace (prefixWord ++ tailWord_2499459) baseStart_2499459 baseEnd_2499459 := by
    simpa [prefixWord, tailWord_2499459, baseEnd_2499459] using wordTrace_append hprefix tailTrace_2499459
  have hstable : (prefixWord ++ tailWord_2499459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499459).length < 2 ^ (prefixWord ++ tailWord_2499459).sum := by decide
  have hdescent : baseEnd_2499459 < baseStart_2499459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499476 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2499476 : Nat := 118140960795 + 2499476 * 2 ^ 59
def prefixEnd_2499476 : Nat := 4983230072969 + 3 ^ 40 * 2499476 * 2
def baseEnd_2499476 : Nat := 427810857459122674118375

theorem tailTrace_2499476 : CollatzResearch.WordTrace tailWord_2499476 prefixEnd_2499476 427810857459122674118375 := by
  unfold tailWord_2499476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45581689546416401680267141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60775586061888535573689521 45581689546416401680267141)
  ·
    refine ⟨8546566789953075315050089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45581689546416401680267141 8546566789953075315050089)
    ·
      refine ⟨6409925092464806486287567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8546566789953075315050089 6409925092464806486287567)
      ·
        refine ⟨9614887638697209729431351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409925092464806486287567 9614887638697209729431351)
        ·
          refine ⟨14422331458045814594147027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9614887638697209729431351 14422331458045814594147027)
          ·
            refine ⟨21633497187068721891220541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14422331458045814594147027 21633497187068721891220541)
            ·
              refine ⟨8112561445150770709207703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21633497187068721891220541 8112561445150770709207703)
              ·
                refine ⟨12168842167726156063811555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112561445150770709207703 12168842167726156063811555)
                ·
                  refine ⟨18253263251589234095717333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12168842167726156063811555 18253263251589234095717333)
                  ·
                    refine ⟨427810857459122674118375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18253263251589234095717333 427810857459122674118375)
                    ·
                      rfl

theorem cell23_2499476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2499476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499476 prefixEnd_2499476 := by exact prefixLift 2499476
  have htrace : WordTrace (prefixWord ++ tailWord_2499476) baseStart_2499476 baseEnd_2499476 := by
    simpa [prefixWord, tailWord_2499476, baseEnd_2499476] using wordTrace_append hprefix tailTrace_2499476
  have hstable : (prefixWord ++ tailWord_2499476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499476).length < 2 ^ (prefixWord ++ tailWord_2499476).sum := by decide
  have hdescent : baseEnd_2499476 < baseStart_2499476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499513 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2499513 : Nat := 118140960795 + 2499513 * 2 ^ 59
def prefixEnd_2499513 : Nat := 4983230072969 + 3 ^ 40 * 2499513 * 2
def baseEnd_2499513 : Nat := 1283451571161584377592455

theorem tailTrace_2499513 : CollatzResearch.WordTrace tailWord_2499513 prefixEnd_2499513 1283451571161584377592455 := by
  unfold tailWord_2499513
  simp only [CollatzResearch.WordTrace]
  refine ⟨91164728593698758679631193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60776485729132505786420795 91164728593698758679631193)
  ·
    refine ⟨68373546445274069009723395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91164728593698758679631193 68373546445274069009723395)
    ·
      refine ⟨102560319667911103514585093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68373546445274069009723395 102560319667911103514585093)
      ·
        refine ⟨19230059937733331908984705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102560319667911103514585093 19230059937733331908984705)
        ·
          refine ⟨14422544953299998931738529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19230059937733331908984705 14422544953299998931738529)
          ·
            refine ⟨10816908714974999198803897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14422544953299998931738529 10816908714974999198803897)
            ·
              refine ⟨8112681536231249399102923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10816908714974999198803897 8112681536231249399102923)
              ·
                refine ⟨12169022304346874098654385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112681536231249399102923 12169022304346874098654385)
                ·
                  refine ⟨9126766728260155573990789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12169022304346874098654385 9126766728260155573990789)
                  ·
                    refine ⟨1711268761548779170123273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9126766728260155573990789 1711268761548779170123273)
                    ·
                      refine ⟨1283451571161584377592455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711268761548779170123273 1283451571161584377592455)
                      ·
                        rfl

theorem cell23_2499513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2499513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499513 prefixEnd_2499513 := by exact prefixLift 2499513
  have htrace : WordTrace (prefixWord ++ tailWord_2499513) baseStart_2499513 baseEnd_2499513 := by
    simpa [prefixWord, tailWord_2499513, baseEnd_2499513] using wordTrace_append hprefix tailTrace_2499513
  have hstable : (prefixWord ++ tailWord_2499513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499513).length < 2 ^ (prefixWord ++ tailWord_2499513).sum := by decide
  have hdescent : baseEnd_2499513 < baseStart_2499513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499557 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_2499557 : Nat := 118140960795 + 2499557 * 2 ^ 59
def prefixEnd_2499557 : Nat := 4983230072969 + 3 ^ 40 * 2499557 * 2
def baseEnd_2499557 : Nat := 427824721436794068480751

theorem tailTrace_2499557 : CollatzResearch.WordTrace tailWord_2499557 prefixEnd_2499557 427824721436794068480751 := by
  unfold tailWord_2499557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91166333405539354194232925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60777555603692902796155283 91166333405539354194232925)
  ·
    refine ⟨34187375027077257822837347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91166333405539354194232925 34187375027077257822837347)
    ·
      refine ⟨51281062540615886734256021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34187375027077257822837347 51281062540615886734256021)
      ·
        refine ⟨2403799806591369690668251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51281062540615886734256021 2403799806591369690668251)
        ·
          refine ⟨3605699709887054536002377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403799806591369690668251 3605699709887054536002377)
          ·
            refine ⟨2704274782415290902001783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3605699709887054536002377 2704274782415290902001783)
            ·
              refine ⟨4056412173622936353002675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704274782415290902001783 4056412173622936353002675)
              ·
                refine ⟨6084618260434404529504013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056412173622936353002675 6084618260434404529504013)
                ·
                  refine ⟨2281731847662901698564005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6084618260434404529504013 2281731847662901698564005)
                  ·
                    refine ⟨427824721436794068480751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281731847662901698564005 427824721436794068480751)
                    ·
                      rfl

theorem cell23_2499557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_2499557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499557 prefixEnd_2499557 := by exact prefixLift 2499557
  have htrace : WordTrace (prefixWord ++ tailWord_2499557) baseStart_2499557 baseEnd_2499557 := by
    simpa [prefixWord, tailWord_2499557, baseEnd_2499557] using wordTrace_append hprefix tailTrace_2499557
  have hstable : (prefixWord ++ tailWord_2499557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499557).length < 2 ^ (prefixWord ++ tailWord_2499557).sum := by decide
  have hdescent : baseEnd_2499557 < baseStart_2499557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499570 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_2499570 : Nat := 118140960795 + 2499570 * 2 ^ 59
def prefixEnd_2499570 : Nat := 4983230072969 + 3 ^ 40 * 2499570 * 2
def baseEnd_2499570 : Nat := 142608982173210072731077

theorem tailTrace_2499570 : CollatzResearch.WordTrace tailWord_2499570 prefixEnd_2499570 142608982173210072731077 := by
  unfold tailWord_2499570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22791701888623064353614041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60777871702994838276304109 22791701888623064353614041)
  ·
    refine ⟨17093776416467298265210531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22791701888623064353614041 17093776416467298265210531)
    ·
      refine ⟨25640664624700947397815797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17093776416467298265210531 25640664624700947397815797)
      ·
        refine ⟨2403812308565713818545231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25640664624700947397815797 2403812308565713818545231)
        ·
          refine ⟨3605718462848570727817847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403812308565713818545231 3605718462848570727817847)
          ·
            refine ⟨5408577694272856091726771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605718462848570727817847 5408577694272856091726771)
            ·
              refine ⟨8112866541409284137590157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408577694272856091726771 8112866541409284137590157)
              ·
                refine ⟨3042324953028481551596309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8112866541409284137590157 3042324953028481551596309)
                ·
                  refine ⟨142608982173210072731077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3042324953028481551596309 142608982173210072731077)
                  ·
                    rfl

theorem cell23_2499570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_2499570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499570 prefixEnd_2499570 := by exact prefixLift 2499570
  have htrace : WordTrace (prefixWord ++ tailWord_2499570) baseStart_2499570 baseEnd_2499570 := by
    simpa [prefixWord, tailWord_2499570, baseEnd_2499570] using wordTrace_append hprefix tailTrace_2499570
  have hstable : (prefixWord ++ tailWord_2499570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499570).length < 2 ^ (prefixWord ++ tailWord_2499570).sum := by decide
  have hdescent : baseEnd_2499570 < baseStart_2499570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499596 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_2499596 : Nat := 118140960795 + 2499596 * 2 ^ 59
def prefixEnd_2499596 : Nat := 4983230072969 + 3 ^ 40 * 2499596 * 2
def baseEnd_2499596 : Nat := 427831396685302517618191

theorem tailTrace_2499596 : CollatzResearch.WordTrace tailWord_2499596 prefixEnd_2499596 427831396685302517618191 := by
  unfold tailWord_2499596
  simp only [CollatzResearch.WordTrace]
  refine ⟨45583877926199031927451321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60778503901598709236601761 45583877926199031927451321)
  ·
    refine ⟨34187908444649273945588491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45583877926199031927451321 34187908444649273945588491)
    ·
      refine ⟨51281862666973910918382737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34187908444649273945588491 51281862666973910918382737)
      ·
        refine ⟨38461397000230433188787053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51281862666973910918382737 38461397000230433188787053)
        ·
          refine ⟨14423023875086412445795145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38461397000230433188787053 14423023875086412445795145)
          ·
            refine ⟨10817267906314809334346359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14423023875086412445795145 10817267906314809334346359)
            ·
              refine ⟨16225901859472214001519539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817267906314809334346359 16225901859472214001519539)
              ·
                refine ⟨24338852789208321002279309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16225901859472214001519539 24338852789208321002279309)
                ·
                  refine ⟨9127069795953120375854741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24338852789208321002279309 9127069795953120375854741)
                  ·
                    refine ⟨427831396685302517618191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9127069795953120375854741 427831396685302517618191)
                    ·
                      rfl

theorem cell23_2499596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_2499596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499596 prefixEnd_2499596 := by exact prefixLift 2499596
  have htrace : WordTrace (prefixWord ++ tailWord_2499596) baseStart_2499596 baseEnd_2499596 := by
    simpa [prefixWord, tailWord_2499596, baseEnd_2499596] using wordTrace_append hprefix tailTrace_2499596
  have hstable : (prefixWord ++ tailWord_2499596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499596).length < 2 ^ (prefixWord ++ tailWord_2499596).sum := by decide
  have hdescent : baseEnd_2499596 < baseStart_2499596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499630 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2499630 : Nat := 118140960795 + 2499630 * 2 ^ 59
def prefixEnd_2499630 : Nat := 4983230072969 + 3 ^ 40 * 2499630 * 2
def baseEnd_2499630 : Nat := 427837216132720139943139

theorem tailTrace_2499630 : CollatzResearch.WordTrace tailWord_2499630 prefixEnd_2499630 427837216132720139943139 := by
  unfold tailWord_2499630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11396124491784360957705043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60779330622849925107760229 11396124491784360957705043)
  ·
    refine ⟨17094186737676541436557565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11396124491784360957705043 17094186737676541436557565)
    ·
      refine ⟨6410320026628703038709087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17094186737676541436557565 6410320026628703038709087)
      ·
        refine ⟨9615480039943054558063631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410320026628703038709087 9615480039943054558063631)
        ·
          refine ⟨14423220059914581837095447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9615480039943054558063631 14423220059914581837095447)
          ·
            refine ⟨21634830089871872755643171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14423220059914581837095447 21634830089871872755643171)
            ·
              refine ⟨32452245134807809133464757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21634830089871872755643171 32452245134807809133464757)
              ·
                refine ⟨3042397981388232106262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32452245134807809133464757 3042397981388232106262321)
                ·
                  refine ⟨2281798486041174079696741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042397981388232106262321 2281798486041174079696741)
                  ·
                    refine ⟨427837216132720139943139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281798486041174079696741 427837216132720139943139)
                    ·
                      rfl

theorem cell23_2499630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2499630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499630 prefixEnd_2499630 := by exact prefixLift 2499630
  have htrace : WordTrace (prefixWord ++ tailWord_2499630) baseStart_2499630 baseEnd_2499630 := by
    simpa [prefixWord, tailWord_2499630, baseEnd_2499630] using wordTrace_append hprefix tailTrace_2499630
  have hstable : (prefixWord ++ tailWord_2499630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499630).length < 2 ^ (prefixWord ++ tailWord_2499630).sum := by decide
  have hdescent : baseEnd_2499630 < baseStart_2499630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499633 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2499633 : Nat := 118140960795 + 2499633 * 2 ^ 59
def prefixEnd_2499633 : Nat := 4983230072969 + 3 ^ 40 * 2499633 * 2
def baseEnd_2499633 : Nat := 1283513188840123908091903

theorem tailTrace_2499633 : CollatzResearch.WordTrace tailWord_2499633 prefixEnd_2499633 1283513188840123908091903 := by
  unfold tailWord_2499633
  simp only [CollatzResearch.WordTrace]
  refine ⟨91169105353264019173999553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60779403568842679449333035 91169105353264019173999553)
  ·
    refine ⟨68376829014948014380499665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91169105353264019173999553 68376829014948014380499665)
    ·
      refine ⟨51282621761211010785374749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68376829014948014380499665 51282621761211010785374749)
      ·
        refine ⟨19230983160454129044515531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51282621761211010785374749 19230983160454129044515531)
        ·
          refine ⟨28846474740681193566773297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19230983160454129044515531 28846474740681193566773297)
          ·
            refine ⟨21634856055510895175079973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28846474740681193566773297 21634856055510895175079973)
            ·
              refine ⟨4056535510408292845327495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21634856055510895175079973 4056535510408292845327495)
              ·
                refine ⟨6084803265612439267991243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056535510408292845327495 6084803265612439267991243)
                ·
                  refine ⟨9127204898418658901986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6084803265612439267991243 9127204898418658901986865)
                  ·
                    refine ⟨6845403673813994176490149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9127204898418658901986865 6845403673813994176490149)
                    ·
                      refine ⟨1283513188840123908091903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6845403673813994176490149 1283513188840123908091903)
                      ·
                        rfl

theorem cell23_2499633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2499633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499633 prefixEnd_2499633 := by exact prefixLift 2499633
  have htrace : WordTrace (prefixWord ++ tailWord_2499633) baseStart_2499633 baseEnd_2499633 := by
    simpa [prefixWord, tailWord_2499633, baseEnd_2499633] using wordTrace_append hprefix tailTrace_2499633
  have hstable : (prefixWord ++ tailWord_2499633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499633).length < 2 ^ (prefixWord ++ tailWord_2499633).sum := by decide
  have hdescent : baseEnd_2499633 < baseStart_2499633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499653 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_2499653 : Nat := 118140960795 + 2499653 * 2 ^ 59
def prefixEnd_2499653 : Nat := 4983230072969 + 3 ^ 40 * 2499653 * 2
def baseEnd_2499653 : Nat := 1283523458453213829841811

theorem tailTrace_2499653 : CollatzResearch.WordTrace tailWord_2499653 prefixEnd_2499653 1283523458453213829841811 := by
  unfold tailWord_2499653
  simp only [CollatzResearch.WordTrace]
  refine ⟨91169834813191562589727613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60779889875461041726485075 91169834813191562589727613)
  ·
    refine ⟨34188688054946835971147855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91169834813191562589727613 34188688054946835971147855)
    ·
      refine ⟨51283032082420253956721783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34188688054946835971147855 51283032082420253956721783)
      ·
        refine ⟨76924548123630380935082675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51283032082420253956721783 76924548123630380935082675)
        ·
          refine ⟨115386822185445571402624013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76924548123630380935082675 115386822185445571402624013)
          ·
            refine ⟨43270058319542089275984005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115386822185445571402624013 43270058319542089275984005)
            ·
              refine ⟨8113135934914141739247001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43270058319542089275984005 8113135934914141739247001)
              ·
                refine ⟨6084851951185606304435251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8113135934914141739247001 6084851951185606304435251)
                ·
                  refine ⟨9127277926778409456652877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6084851951185606304435251 9127277926778409456652877)
                  ·
                    refine ⟨3422729222541903546244829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9127277926778409456652877 3422729222541903546244829)
                    ·
                      refine ⟨1283523458453213829841811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3422729222541903546244829 1283523458453213829841811)
                      ·
                        rfl

theorem cell23_2499653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_2499653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499653 prefixEnd_2499653 := by exact prefixLift 2499653
  have htrace : WordTrace (prefixWord ++ tailWord_2499653) baseStart_2499653 baseEnd_2499653 := by
    simpa [prefixWord, tailWord_2499653, baseEnd_2499653] using wordTrace_append hprefix tailTrace_2499653
  have hstable : (prefixWord ++ tailWord_2499653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499653).length < 2 ^ (prefixWord ++ tailWord_2499653).sum := by decide
  have hdescent : baseEnd_2499653 < baseStart_2499653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499654 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2499654 : Nat := 118140960795 + 2499654 * 2 ^ 59
def prefixEnd_2499654 : Nat := 4983230072969 + 3 ^ 40 * 2499654 * 2
def baseEnd_2499654 : Nat := 1283523971933868325929307

theorem tailTrace_2499654 : CollatzResearch.WordTrace tailWord_2499654 prefixEnd_2499654 1283523971933868325929307 := by
  unfold tailWord_2499654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849058477693373117516063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60779914190791959840342677 2849058477693373117516063)
  ·
    refine ⟨4273587716540059676274095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849058477693373117516063 4273587716540059676274095)
    ·
      refine ⟨6410381574810089514411143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273587716540059676274095 6410381574810089514411143)
      ·
        refine ⟨9615572362215134271616715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410381574810089514411143 9615572362215134271616715)
        ·
          refine ⟨14423358543322701407425073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9615572362215134271616715 14423358543322701407425073)
          ·
            refine ⟨10817518907492026055568805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14423358543322701407425073 10817518907492026055568805)
            ·
              refine ⟨2028284795154754885419151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10817518907492026055568805 2028284795154754885419151)
              ·
                refine ⟨3042427192732132328128727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028284795154754885419151 3042427192732132328128727)
                ·
                  refine ⟨4563640789098198492193091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042427192732132328128727 4563640789098198492193091)
                  ·
                    refine ⟨6845461183647297738289637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4563640789098198492193091 6845461183647297738289637)
                    ·
                      refine ⟨1283523971933868325929307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6845461183647297738289637 1283523971933868325929307)
                      ·
                        rfl

theorem cell23_2499654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2499654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499654 prefixEnd_2499654 := by exact prefixLift 2499654
  have htrace : WordTrace (prefixWord ++ tailWord_2499654) baseStart_2499654 baseEnd_2499654 := by
    simpa [prefixWord, tailWord_2499654, baseEnd_2499654] using wordTrace_append hprefix tailTrace_2499654
  have hstable : (prefixWord ++ tailWord_2499654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499654).length < 2 ^ (prefixWord ++ tailWord_2499654).sum := by decide
  have hdescent : baseEnd_2499654 < baseStart_2499654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499713 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2499713 : Nat := 118140960795 + 2499713 * 2 ^ 59
def prefixEnd_2499713 : Nat := 4983230072969 + 3 ^ 40 * 2499713 * 2
def baseEnd_2499713 : Nat := 1283554267292483595091535

theorem tailTrace_2499713 : CollatzResearch.WordTrace tailWord_2499713 prefixEnd_2499713 1283554267292483595091535 := by
  unfold tailWord_2499713
  simp only [CollatzResearch.WordTrace]
  refine ⟨91172023192974192836911793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60781348795316128557941195 91172023192974192836911793)
  ·
    refine ⟨68379017394730644627683845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91172023192974192836911793 68379017394730644627683845)
    ·
      refine ⟨12821065761511995867690721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68379017394730644627683845 12821065761511995867690721)
      ·
        refine ⟨9615799321133996900768041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12821065761511995867690721 9615799321133996900768041)
        ·
          refine ⟨7211849490850497675576031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9615799321133996900768041 7211849490850497675576031)
          ·
            refine ⟨10817774236275746513364047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211849490850497675576031 10817774236275746513364047)
            ·
              refine ⟨16226661354413619770046071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817774236275746513364047 16226661354413619770046071)
              ·
                refine ⟨24339992031620429655069107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16226661354413619770046071 24339992031620429655069107)
                ·
                  refine ⟨36509988047430644482603661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24339992031620429655069107 36509988047430644482603661)
                  ·
                    refine ⟨13691245517786491680976373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36509988047430644482603661 13691245517786491680976373)
                    ·
                      refine ⟨1283554267292483595091535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13691245517786491680976373 1283554267292483595091535)
                      ·
                        rfl

theorem cell23_2499713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2499713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499713 prefixEnd_2499713 := by exact prefixLift 2499713
  have htrace : WordTrace (prefixWord ++ tailWord_2499713) baseStart_2499713 baseEnd_2499713 := by
    simpa [prefixWord, tailWord_2499713, baseEnd_2499713] using wordTrace_append hprefix tailTrace_2499713
  have hstable : (prefixWord ++ tailWord_2499713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499713).length < 2 ^ (prefixWord ++ tailWord_2499713).sum := by decide
  have hdescent : baseEnd_2499713 < baseStart_2499713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499763 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 2, 5]
def baseStart_2499763 : Nat := 118140960795 + 2499763 * 2 ^ 59
def prefixEnd_2499763 : Nat := 4983230072969 + 3 ^ 40 * 2499763 * 2
def baseEnd_2499763 : Nat := 427859980441736133155435

theorem tailTrace_2499763 : CollatzResearch.WordTrace tailWord_2499763 prefixEnd_2499763 427859980441736133155435 := by
  unfold tailWord_2499763
  simp only [CollatzResearch.WordTrace]
  refine ⟨91173846842793051376231943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60782564561862034250821295 91173846842793051376231943)
  ·
    refine ⟨136760770264189577064347915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91173846842793051376231943 136760770264189577064347915)
    ·
      refine ⟨205141155396284365596521873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136760770264189577064347915 205141155396284365596521873)
      ·
        refine ⟨153855866547213274197391405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205141155396284365596521873 153855866547213274197391405)
        ·
          refine ⟨57695949955204977824021777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153855866547213274197391405 57695949955204977824021777)
          ·
            refine ⟨43271962466403733368016333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57695949955204977824021777 43271962466403733368016333)
            ·
              refine ⟨16226985924901400013006125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43271962466403733368016333 16226985924901400013006125)
              ·
                refine ⟨6085119721838025004877297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16226985924901400013006125 6085119721838025004877297)
                ·
                  refine ⟨4563839791378518753657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6085119721838025004877297 4563839791378518753657973)
                  ·
                    refine ⟨427859980441736133155435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4563839791378518753657973 427859980441736133155435)
                    ·
                      rfl

theorem cell23_2499763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].length) (baseStart_2499763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499763 prefixEnd_2499763 := by exact prefixLift 2499763
  have htrace : WordTrace (prefixWord ++ tailWord_2499763) baseStart_2499763 baseEnd_2499763 := by
    simpa [prefixWord, tailWord_2499763, baseEnd_2499763] using wordTrace_append hprefix tailTrace_2499763
  have hstable : (prefixWord ++ tailWord_2499763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499763).length < 2 ^ (prefixWord ++ tailWord_2499763).sum := by decide
  have hdescent : baseEnd_2499763 < baseStart_2499763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499773 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2499773 : Nat := 118140960795 + 2499773 * 2 ^ 59
def prefixEnd_2499773 : Nat := 4983230072969 + 3 ^ 40 * 2499773 * 2
def baseEnd_2499773 : Nat := 1283585076131753360341259

theorem tailTrace_2499773 : CollatzResearch.WordTrace tailWord_2499773 prefixEnd_2499773 1283585076131753360341259 := by
  unfold tailWord_2499773
  simp only [CollatzResearch.WordTrace]
  refine ⟨91174211572756823084095973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60782807715171215389397315 91174211572756823084095973)
  ·
    refine ⟨17095164669891904328267995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91174211572756823084095973 17095164669891904328267995)
    ·
      refine ⟨25642747004837856492401993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17095164669891904328267995 25642747004837856492401993)
      ·
        refine ⟨19232060253628392369301495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25642747004837856492401993 19232060253628392369301495)
        ·
          refine ⟨28848090380442588553952243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19232060253628392369301495 28848090380442588553952243)
          ·
            refine ⟨43272135570663882830928365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28848090380442588553952243 43272135570663882830928365)
            ·
              refine ⟨16227050838998956061598137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43272135570663882830928365 16227050838998956061598137)
              ·
                refine ⟨12170288129249217046198603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16227050838998956061598137 12170288129249217046198603)
                ·
                  refine ⟨18255432193873825569297905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12170288129249217046198603 18255432193873825569297905)
                  ·
                    refine ⟨13691574145405369176973429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18255432193873825569297905 13691574145405369176973429)
                    ·
                      refine ⟨1283585076131753360341259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13691574145405369176973429 1283585076131753360341259)
                      ·
                        rfl

theorem cell23_2499773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2499773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499773 prefixEnd_2499773 := by exact prefixLift 2499773
  have htrace : WordTrace (prefixWord ++ tailWord_2499773) baseStart_2499773 baseEnd_2499773 := by
    simpa [prefixWord, tailWord_2499773, baseEnd_2499773] using wordTrace_append hprefix tailTrace_2499773
  have hstable : (prefixWord ++ tailWord_2499773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499773).length < 2 ^ (prefixWord ++ tailWord_2499773).sum := by decide
  have hdescent : baseEnd_2499773 < baseStart_2499773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499820 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2499820 : Nat := 118140960795 + 2499820 * 2 ^ 59
def prefixEnd_2499820 : Nat := 4983230072969 + 3 ^ 40 * 2499820 * 2
def baseEnd_2499820 : Nat := 1283609209722514676453543

theorem tailTrace_2499820 : CollatzResearch.WordTrace tailWord_2499820 prefixEnd_2499820 1283609209722514676453543 := by
  unfold tailWord_2499820
  simp only [CollatzResearch.WordTrace]
  refine ⟨45587962901793275055528457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60783950535724366740704609 45587962901793275055528457)
  ·
    refine ⟨34190972176344956291646343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45587962901793275055528457 34190972176344956291646343)
    ·
      refine ⟨51286458264517434437469515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34190972176344956291646343 51286458264517434437469515)
      ·
        refine ⟨76929687396776151656204273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51286458264517434437469515 76929687396776151656204273)
        ·
          refine ⟨57697265547582113742153205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76929687396776151656204273 57697265547582113742153205)
          ·
            refine ⟨5409118645085823163326863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57697265547582113742153205 5409118645085823163326863)
            ·
              refine ⟨8113677967628734744990295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409118645085823163326863 8113677967628734744990295)
              ·
                refine ⟨12170516951443102117485443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113677967628734744990295 12170516951443102117485443)
                ·
                  refine ⟨18255775427164653176228165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12170516951443102117485443 18255775427164653176228165)
                  ·
                    refine ⟨3422957892593372470542781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18255775427164653176228165 3422957892593372470542781)
                    ·
                      refine ⟨1283609209722514676453543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3422957892593372470542781 1283609209722514676453543)
                      ·
                        rfl

theorem cell23_2499820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2499820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499820 prefixEnd_2499820 := by exact prefixLift 2499820
  have htrace : WordTrace (prefixWord ++ tailWord_2499820) baseStart_2499820 baseEnd_2499820 := by
    simpa [prefixWord, tailWord_2499820, baseEnd_2499820] using wordTrace_append hprefix tailTrace_2499820
  have hstable : (prefixWord ++ tailWord_2499820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499820).length < 2 ^ (prefixWord ++ tailWord_2499820).sum := by decide
  have hdescent : baseEnd_2499820 < baseStart_2499820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499827 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 1, 4]
def baseStart_2499827 : Nat := 118140960795 + 2499827 * 2 ^ 59
def prefixEnd_2499827 : Nat := 4983230072969 + 3 ^ 40 * 2499827 * 2
def baseEnd_2499827 : Nat := 427870934695698716355337

theorem tailTrace_2499827 : CollatzResearch.WordTrace tailWord_2499827 prefixEnd_2499827 427870934695698716355337 := by
  unfold tailWord_2499827
  simp only [CollatzResearch.WordTrace]
  refine ⟨91176181114561190306561735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60784120743040793537707823 91176181114561190306561735)
  ·
    refine ⟨136764271671841785459842603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91176181114561190306561735 136764271671841785459842603)
    ·
      refine ⟨205146407507762678189763905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136764271671841785459842603 205146407507762678189763905)
      ·
        refine ⟨153859805630822008642322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205146407507762678189763905 153859805630822008642322929)
        ·
          refine ⟨115394854223116506481742197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153859805630822008642322929 115394854223116506481742197)
          ·
            refine ⟨10818267583417172482663331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115394854223116506481742197 10818267583417172482663331)
            ·
              refine ⟨16227401375125758723994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818267583417172482663331 16227401375125758723994997)
              ·
                refine ⟨1521318878918039880374531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16227401375125758723994997 1521318878918039880374531)
                ·
                  refine ⟨2281978318377059820561797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521318878918039880374531 2281978318377059820561797)
                  ·
                    refine ⟨427870934695698716355337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281978318377059820561797 427870934695698716355337)
                    ·
                      rfl

theorem cell23_2499827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 4].length) (baseStart_2499827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499827 prefixEnd_2499827 := by exact prefixLift 2499827
  have htrace : WordTrace (prefixWord ++ tailWord_2499827) baseStart_2499827 baseEnd_2499827 := by
    simpa [prefixWord, tailWord_2499827, baseEnd_2499827] using wordTrace_append hprefix tailTrace_2499827
  have hstable : (prefixWord ++ tailWord_2499827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499827).length < 2 ^ (prefixWord ++ tailWord_2499827).sum := by decide
  have hdescent : baseEnd_2499827 < baseStart_2499827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499843 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_2499843 : Nat := 118140960795 + 2499843 * 2 ^ 59
def prefixEnd_2499843 : Nat := 4983230072969 + 3 ^ 40 * 2499843 * 2
def baseEnd_2499843 : Nat := 1283621019777568086465937

theorem tailTrace_2499843 : CollatzResearch.WordTrace tailWord_2499843 prefixEnd_2499843 1283621019777568086465937 := by
  unfold tailWord_2499843
  simp only [CollatzResearch.WordTrace]
  refine ⟨91176764682503225039144183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60784509788335483359429455 91176764682503225039144183)
  ·
    refine ⟨136765147023754837558716275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91176764682503225039144183 136765147023754837558716275)
    ·
      refine ⟨205147720535632256338074413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136765147023754837558716275 205147720535632256338074413)
      ·
        refine ⟨76930395200862096126777905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205147720535632256338074413 76930395200862096126777905)
        ·
          refine ⟨57697796400646572095083429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76930395200862096126777905 57697796400646572095083429)
          ·
            refine ⟨10818336825121232267828143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57697796400646572095083429 10818336825121232267828143)
            ·
              refine ⟨16227505237681848401742215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818336825121232267828143 16227505237681848401742215)
              ·
                refine ⟨24341257856522772602613323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16227505237681848401742215 24341257856522772602613323)
                ·
                  refine ⟨36511886784784158903919985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24341257856522772602613323 36511886784784158903919985)
                  ·
                    refine ⟨27383915088588119177939989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36511886784784158903919985 27383915088588119177939989)
                    ·
                      refine ⟨1283621019777568086465937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27383915088588119177939989 1283621019777568086465937)
                      ·
                        rfl

theorem cell23_2499843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_2499843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499843 prefixEnd_2499843 := by exact prefixLift 2499843
  have htrace : WordTrace (prefixWord ++ tailWord_2499843) baseStart_2499843 baseEnd_2499843 := by
    simpa [prefixWord, tailWord_2499843, baseEnd_2499843] using wordTrace_append hprefix tailTrace_2499843
  have hstable : (prefixWord ++ tailWord_2499843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499843).length < 2 ^ (prefixWord ++ tailWord_2499843).sum := by decide
  have hdescent : baseEnd_2499843 < baseStart_2499843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499844 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2499844 : Nat := 118140960795 + 2499844 * 2 ^ 59
def prefixEnd_2499844 : Nat := 4983230072969 + 3 ^ 40 * 2499844 * 2
def baseEnd_2499844 : Nat := 427873844419407527517811

theorem tailTrace_2499844 : CollatzResearch.WordTrace tailWord_2499844 prefixEnd_2499844 427873844419407527517811 := by
  unfold tailWord_2499844
  simp only [CollatzResearch.WordTrace]
  refine ⟨45588400577749801104965293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60784534103666401473287057 45588400577749801104965293)
  ·
    refine ⟨17095650216656175414361985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45588400577749801104965293 17095650216656175414361985)
    ·
      refine ⟨12821737662492131560771489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17095650216656175414361985 12821737662492131560771489)
      ·
        refine ⟨9616303246869098670578617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12821737662492131560771489 9616303246869098670578617)
        ·
          refine ⟨7212227435151824002933963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9616303246869098670578617 7212227435151824002933963)
          ·
            refine ⟨10818341152727736004400945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212227435151824002933963 10818341152727736004400945)
            ·
              refine ⟨8113755864545802003300709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10818341152727736004400945 8113755864545802003300709)
              ·
                refine ⟨1521329224602337875618883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8113755864545802003300709 1521329224602337875618883)
                ·
                  refine ⟨2281993836903506813428325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521329224602337875618883 2281993836903506813428325)
                  ·
                    refine ⟨427873844419407527517811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281993836903506813428325 427873844419407527517811)
                    ·
                      rfl

theorem cell23_2499844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2499844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499844 prefixEnd_2499844 := by exact prefixLift 2499844
  have htrace : WordTrace (prefixWord ++ tailWord_2499844) baseStart_2499844 baseEnd_2499844 := by
    simpa [prefixWord, tailWord_2499844, baseEnd_2499844] using wordTrace_append hprefix tailTrace_2499844
  have hstable : (prefixWord ++ tailWord_2499844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499844).length < 2 ^ (prefixWord ++ tailWord_2499844).sum := by decide
  have hdescent : baseEnd_2499844 < baseStart_2499844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499877 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_2499877 : Nat := 118140960795 + 2499877 * 2 ^ 59
def prefixEnd_2499877 : Nat := 4983230072969 + 3 ^ 40 * 2499877 * 2
def baseEnd_2499877 : Nat := 1283638478119820953440781

theorem tailTrace_2499877 : CollatzResearch.WordTrace tailWord_2499877 prefixEnd_2499877 1283638478119820953440781 := by
  unfold tailWord_2499877
  simp only [CollatzResearch.WordTrace]
  refine ⟨91178004764380048845881885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60785336509586699230587923 91178004764380048845881885)
  ·
    refine ⟨34191751786642518317205707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91178004764380048845881885 34191751786642518317205707)
    ·
      refine ⟨51287627679963777475808561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34191751786642518317205707 51287627679963777475808561)
      ·
        refine ⟨38465720759972833106856421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51287627679963777475808561 38465720759972833106856421)
        ·
          refine ⟨7212322642494906207535579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38465720759972833106856421 7212322642494906207535579)
          ·
            refine ⟨10818483963742359311303369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212322642494906207535579 10818483963742359311303369)
            ·
              refine ⟨8113862972806769483477527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10818483963742359311303369 8113862972806769483477527)
              ·
                refine ⟨12170794459210154225216291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113862972806769483477527 12170794459210154225216291)
                ·
                  refine ⟨18256191688815231337824437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12170794459210154225216291 18256191688815231337824437)
                  ·
                    refine ⟨1711517970826427937921041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18256191688815231337824437 1711517970826427937921041)
                    ·
                      refine ⟨1283638478119820953440781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711517970826427937921041 1283638478119820953440781)
                      ·
                        rfl

theorem cell23_2499877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_2499877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499877 prefixEnd_2499877 := by exact prefixLift 2499877
  have htrace : WordTrace (prefixWord ++ tailWord_2499877) baseStart_2499877 baseEnd_2499877 := by
    simpa [prefixWord, tailWord_2499877, baseEnd_2499877] using wordTrace_append hprefix tailTrace_2499877
  have hstable : (prefixWord ++ tailWord_2499877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499877).length < 2 ^ (prefixWord ++ tailWord_2499877).sum := by decide
  have hdescent : baseEnd_2499877 < baseStart_2499877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499913 : List Nat := [1, 2, 1, 1, 2, 3, 3, 10]
def baseStart_2499913 : Nat := 118140960795 + 2499913 * 2 ^ 59
def prefixEnd_2499913 : Nat := 4983230072969 + 3 ^ 40 * 2499913 * 2
def baseEnd_2499913 : Nat := 47542850497162326392245

theorem tailTrace_2499913 : CollatzResearch.WordTrace tailWord_2499913 prefixEnd_2499913 47542850497162326392245 := by
  unfold tailWord_2499913
  simp only [CollatzResearch.WordTrace]
  refine ⟨91179317792249626994192393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60786211861499751329461595 91179317792249626994192393)
  ·
    refine ⟨68384488344187220245644295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91179317792249626994192393 68384488344187220245644295)
    ·
      refine ⟨102576732516280830368466443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68384488344187220245644295 102576732516280830368466443)
      ·
        refine ⟨153865098774421245552699665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102576732516280830368466443 153865098774421245552699665)
        ·
          refine ⟨115398824080815934164524749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153865098774421245552699665 115398824080815934164524749)
          ·
            refine ⟨43274559030305975311696781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115398824080815934164524749 43274559030305975311696781)
            ·
              refine ⟨16227959636364740741886293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43274559030305975311696781 16227959636364740741886293)
              ·
                refine ⟨47542850497162326392245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16227959636364740741886293 47542850497162326392245)
                ·
                  rfl

theorem cell23_2499913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 10].length) (baseStart_2499913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499913 prefixEnd_2499913 := by exact prefixLift 2499913
  have htrace : WordTrace (prefixWord ++ tailWord_2499913) baseStart_2499913 baseEnd_2499913 := by
    simpa [prefixWord, tailWord_2499913, baseEnd_2499913] using wordTrace_append hprefix tailTrace_2499913
  have hstable : (prefixWord ++ tailWord_2499913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499913).length < 2 ^ (prefixWord ++ tailWord_2499913).sum := by decide
  have hdescent : baseEnd_2499913 < baseStart_2499913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499920 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_2499920 : Nat := 118140960795 + 2499920 * 2 ^ 59
def prefixEnd_2499920 : Nat := 4983230072969 + 3 ^ 40 * 2499920 * 2
def baseEnd_2499920 : Nat := 1283660557787964285203083

theorem tailTrace_2499920 : CollatzResearch.WordTrace tailWord_2499920 prefixEnd_2499920 1283660557787964285203083 := by
  unfold tailWord_2499920
  simp only [CollatzResearch.WordTrace]
  refine ⟨45589786551612133594848607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60786382068816178126464809 45589786551612133594848607)
  ·
    refine ⟨68384679827418200392272911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45589786551612133594848607 68384679827418200392272911)
    ·
      refine ⟨102577019741127300588409367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68384679827418200392272911 102577019741127300588409367)
      ·
        refine ⟨153865529611690950882614051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102577019741127300588409367 153865529611690950882614051)
        ·
          refine ⟨230798294417536426323921077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153865529611690950882614051 230798294417536426323921077)
          ·
            refine ⟨21637340101644039967867601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230798294417536426323921077 21637340101644039967867601)
            ·
              refine ⟨16228005076233029975900701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21637340101644039967867601 16228005076233029975900701)
              ·
                refine ⟨6085501903587386240962763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16228005076233029975900701 6085501903587386240962763)
                ·
                  refine ⟨9128252855381079361444145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085501903587386240962763 9128252855381079361444145)
                  ·
                    refine ⟨6846189641535809521083109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9128252855381079361444145 6846189641535809521083109)
                    ·
                      refine ⟨1283660557787964285203083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6846189641535809521083109 1283660557787964285203083)
                      ·
                        rfl

theorem cell23_2499920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_2499920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499920 prefixEnd_2499920 := by exact prefixLift 2499920
  have htrace : WordTrace (prefixWord ++ tailWord_2499920) baseStart_2499920 baseEnd_2499920 := by
    simpa [prefixWord, tailWord_2499920, baseEnd_2499920] using wordTrace_append hprefix tailTrace_2499920
  have hstable : (prefixWord ++ tailWord_2499920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499920).length < 2 ^ (prefixWord ++ tailWord_2499920).sum := by decide
  have hdescent : baseEnd_2499920 < baseStart_2499920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499924 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_2499924 : Nat := 118140960795 + 2499924 * 2 ^ 59
def prefixEnd_2499924 : Nat := 4983230072969 + 3 ^ 40 * 2499924 * 2
def baseEnd_2499924 : Nat := 1283662611710582269553065

theorem tailTrace_2499924 : CollatzResearch.WordTrace tailWord_2499924 prefixEnd_2499924 1283662611710582269553065 := by
  unfold tailWord_2499924
  simp only [CollatzResearch.WordTrace]
  refine ⟨45589859497604887936421413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60786479330139850581895217 45589859497604887936421413)
  ·
    refine ⟨8548098655800916488079015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45589859497604887936421413 8548098655800916488079015)
    ·
      refine ⟨12822147983701374732118523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548098655800916488079015 12822147983701374732118523)
      ·
        refine ⟨19233221975552062098177785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12822147983701374732118523 19233221975552062098177785)
        ·
          refine ⟨14424916481664046573633339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19233221975552062098177785 14424916481664046573633339)
          ·
            refine ⟨21637374722496069860450009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14424916481664046573633339 21637374722496069860450009)
            ·
              refine ⟨16228031041872052395337507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21637374722496069860450009 16228031041872052395337507)
              ·
                refine ⟨24342046562808078593006261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16228031041872052395337507 24342046562808078593006261)
                ·
                  refine ⟨2282066865263257368094337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24342046562808078593006261 2282066865263257368094337)
                  ·
                    refine ⟨1711550148947443026070753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2282066865263257368094337 1711550148947443026070753)
                    ·
                      refine ⟨1283662611710582269553065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711550148947443026070753 1283662611710582269553065)
                      ·
                        rfl

theorem cell23_2499924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_2499924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499924 prefixEnd_2499924 := by exact prefixLift 2499924
  have htrace : WordTrace (prefixWord ++ tailWord_2499924) baseStart_2499924 baseEnd_2499924 := by
    simpa [prefixWord, tailWord_2499924, baseEnd_2499924] using wordTrace_append hprefix tailTrace_2499924
  have hstable : (prefixWord ++ tailWord_2499924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499924).length < 2 ^ (prefixWord ++ tailWord_2499924).sum := by decide
  have hdescent : baseEnd_2499924 < baseStart_2499924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499927 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_2499927 : Nat := 118140960795 + 2499927 * 2 ^ 59
def prefixEnd_2499927 : Nat := 4983230072969 + 3 ^ 40 * 2499927 * 2
def baseEnd_2499927 : Nat := 1283664152152545757815551

theorem tailTrace_2499927 : CollatzResearch.WordTrace tailWord_2499927 prefixEnd_2499927 1283664152152545757815551 := by
  unfold tailWord_2499927
  simp only [CollatzResearch.WordTrace]
  refine ⟨91179828414198907385202035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60786552276132604923468023 91179828414198907385202035)
  ·
    refine ⟨136769742621298361077803053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91179828414198907385202035 136769742621298361077803053)
    ·
      refine ⟨51288653482986885404176145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136769742621298361077803053 51288653482986885404176145)
      ·
        refine ⟨38466490112240164053132109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51288653482986885404176145 38466490112240164053132109)
        ·
          refine ⟨14424933792090061519924541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38466490112240164053132109 14424933792090061519924541)
          ·
            refine ⟨5409350172033773069971703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14424933792090061519924541 5409350172033773069971703)
            ·
              refine ⟨8114025258050659604957555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409350172033773069971703 8114025258050659604957555)
              ·
                refine ⟨12171037887075989407436333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114025258050659604957555 12171037887075989407436333)
                ·
                  refine ⟨4564139207653496027788625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12171037887075989407436333 4564139207653496027788625)
                  ·
                    refine ⟨3423104405740122020841469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564139207653496027788625 3423104405740122020841469)
                    ·
                      refine ⟨1283664152152545757815551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423104405740122020841469 1283664152152545757815551)
                      ·
                        rfl

theorem cell23_2499927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_2499927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499927 prefixEnd_2499927 := by exact prefixLift 2499927
  have htrace : WordTrace (prefixWord ++ tailWord_2499927) baseStart_2499927 baseEnd_2499927 := by
    simpa [prefixWord, tailWord_2499927, baseEnd_2499927] using wordTrace_append hprefix tailTrace_2499927
  have hstable : (prefixWord ++ tailWord_2499927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499927).length < 2 ^ (prefixWord ++ tailWord_2499927).sum := by decide
  have hdescent : baseEnd_2499927 < baseStart_2499927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499941 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_2499941 : Nat := 118140960795 + 2499941 * 2 ^ 59
def prefixEnd_2499941 : Nat := 4983230072969 + 3 ^ 40 * 2499941 * 2
def baseEnd_2499941 : Nat := 1283671340881708703040487

theorem tailTrace_2499941 : CollatzResearch.WordTrace tailWord_2499941 prefixEnd_2499941 1283671340881708703040487 := by
  unfold tailWord_2499941
  simp only [CollatzResearch.WordTrace]
  refine ⟨91180339036148187776211677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60786892690765458517474451 91180339036148187776211677)
  ·
    refine ⟨34192627138555570416079379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91180339036148187776211677 34192627138555570416079379)
    ·
      refine ⟨51288940707833355624119069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34192627138555570416079379 51288940707833355624119069)
      ·
        refine ⟨19233352765437508359044651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51288940707833355624119069 19233352765437508359044651)
        ·
          refine ⟨28850029148156262538566977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19233352765437508359044651 28850029148156262538566977)
          ·
            refine ⟨21637521861117196903925233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28850029148156262538566977 21637521861117196903925233)
            ·
              refine ⟨16228141395837897677943925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21637521861117196903925233 16228141395837897677943925)
              ·
                refine ⟨1521388255859802907307243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16228141395837897677943925 1521388255859802907307243)
                ·
                  refine ⟨2282082383789704360960865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521388255859802907307243 2282082383789704360960865)
                  ·
                    refine ⟨1711561787842278270720649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2282082383789704360960865 1711561787842278270720649)
                    ·
                      refine ⟨1283671340881708703040487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711561787842278270720649 1283671340881708703040487)
                      ·
                        rfl

theorem cell23_2499941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_2499941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499941 prefixEnd_2499941 := by exact prefixLift 2499941
  have htrace : WordTrace (prefixWord ++ tailWord_2499941) baseStart_2499941 baseEnd_2499941 := by
    simpa [prefixWord, tailWord_2499941, baseEnd_2499941] using wordTrace_append hprefix tailTrace_2499941
  have hstable : (prefixWord ++ tailWord_2499941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499941).length < 2 ^ (prefixWord ++ tailWord_2499941).sum := by decide
  have hdescent : baseEnd_2499941 < baseStart_2499941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499944 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2499944 : Nat := 118140960795 + 2499944 * 2 ^ 59
def prefixEnd_2499944 : Nat := 4983230072969 + 3 ^ 40 * 2499944 * 2
def baseEnd_2499944 : Nat := 1283672881323672191302973

theorem tailTrace_2499944 : CollatzResearch.WordTrace tailWord_2499944 prefixEnd_2499944 1283672881323672191302973 := by
  unfold tailWord_2499944
  simp only [CollatzResearch.WordTrace]
  refine ⟨45590224227568659644285443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60786965636758212859047257 45590224227568659644285443)
  ·
    refine ⟨68385336341352989466428165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45590224227568659644285443 68385336341352989466428165)
    ·
      refine ⟨12822250564003685524955281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68385336341352989466428165 12822250564003685524955281)
      ·
        refine ⟨9616687923002764143716461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12822250564003685524955281 9616687923002764143716461)
        ·
          refine ⟨3606257971126036553893673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9616687923002764143716461 3606257971126036553893673)
          ·
            refine ⟨2704693478344527415420255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606257971126036553893673 2704693478344527415420255)
            ·
              refine ⟨4057040217516791123130383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704693478344527415420255 4057040217516791123130383)
              ·
                refine ⟨6085560326275186684695575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057040217516791123130383 6085560326275186684695575)
                ·
                  refine ⟨9128340489412780027043363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085560326275186684695575 9128340489412780027043363)
                  ·
                    refine ⟨13692510734119170040565045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9128340489412780027043363 13692510734119170040565045)
                    ·
                      refine ⟨1283672881323672191302973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13692510734119170040565045 1283672881323672191302973)
                      ·
                        rfl

theorem cell23_2499944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2499944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499944 prefixEnd_2499944 := by exact prefixLift 2499944
  have htrace : WordTrace (prefixWord ++ tailWord_2499944) baseStart_2499944 baseEnd_2499944 := by
    simpa [prefixWord, tailWord_2499944, baseEnd_2499944] using wordTrace_append hprefix tailTrace_2499944
  have hstable : (prefixWord ++ tailWord_2499944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499944).length < 2 ^ (prefixWord ++ tailWord_2499944).sum := by decide
  have hdescent : baseEnd_2499944 < baseStart_2499944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499980 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2499980 : Nat := 118140960795 + 2499980 * 2 ^ 59
def prefixEnd_2499980 : Nat := 4983230072969 + 3 ^ 40 * 2499980 * 2
def baseEnd_2499980 : Nat := 1283691366627234050452807

theorem tailTrace_2499980 : CollatzResearch.WordTrace tailWord_2499980 prefixEnd_2499980 1283691366627234050452807 := by
  unfold tailWord_2499980
  simp only [CollatzResearch.WordTrace]
  refine ⟨45590880741503448718440697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60787840988671264957920929 45590880741503448718440697)
  ·
    refine ⟨34193160556127586538830523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45590880741503448718440697 34193160556127586538830523)
    ·
      refine ⟨51289740834191379808245785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34193160556127586538830523 51289740834191379808245785)
      ·
        refine ⟨38467305625643534856184339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51289740834191379808245785 38467305625643534856184339)
        ·
          refine ⟨57700958438465302284276509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38467305625643534856184339 57700958438465302284276509)
          ·
            refine ⟨21637859414424488356603691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57700958438465302284276509 21637859414424488356603691)
            ·
              refine ⟨32456789121636732534905537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21637859414424488356603691 32456789121636732534905537)
              ·
                refine ⟨24342591841227549401179153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32456789121636732534905537 24342591841227549401179153)
                ·
                  refine ⟨18256943880920662050884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24342591841227549401179153 18256943880920662050884365)
                  ·
                    refine ⟨6846353955345248269081637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18256943880920662050884365 6846353955345248269081637)
                    ·
                      refine ⟨1283691366627234050452807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6846353955345248269081637 1283691366627234050452807)
                      ·
                        rfl

theorem cell23_2499980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2499980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2499980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2499980 prefixEnd_2499980 := by exact prefixLift 2499980
  have htrace : WordTrace (prefixWord ++ tailWord_2499980) baseStart_2499980 baseEnd_2499980 := by
    simpa [prefixWord, tailWord_2499980, baseEnd_2499980] using wordTrace_append hprefix tailTrace_2499980
  have hstable : (prefixWord ++ tailWord_2499980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499980).length < 2 ^ (prefixWord ++ tailWord_2499980).sum := by decide
  have hdescent : baseEnd_2499980 < baseStart_2499980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500000 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2500000 : Nat := 118140960795 + 2500000 * 2 ^ 59
def prefixEnd_2500000 : Nat := 4983230072969 + 3 ^ 40 * 2500000 * 2
def baseEnd_2500000 : Nat := 1283701636240323972202715

theorem tailTrace_2500000 : CollatzResearch.WordTrace tailWord_2500000 prefixEnd_2500000 1283701636240323972202715 := by
  unfold tailWord_2500000
  simp only [CollatzResearch.WordTrace]
  refine ⟨45591245471467220426304727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60788327295289627235072969 45591245471467220426304727)
  ·
    refine ⟨68386868207200830639457091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45591245471467220426304727 68386868207200830639457091)
    ·
      refine ⟨102580302310801245959185637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68386868207200830639457091 102580302310801245959185637)
      ·
        refine ⟨19233806683275233617347307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102580302310801245959185637 19233806683275233617347307)
        ·
          refine ⟨28850710024912850426020961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19233806683275233617347307 28850710024912850426020961)
          ·
            refine ⟨21638032518684637819515721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28850710024912850426020961 21638032518684637819515721)
            ·
              refine ⟨16228524389013478364636791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21638032518684637819515721 16228524389013478364636791)
              ·
                refine ⟨24342786583520217546955187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16228524389013478364636791 24342786583520217546955187)
                ·
                  refine ⟨36514179875280326320432781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24342786583520217546955187 36514179875280326320432781)
                  ·
                    refine ⟨13692817453230122370162293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36514179875280326320432781 13692817453230122370162293)
                    ·
                      refine ⟨1283701636240323972202715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13692817453230122370162293 1283701636240323972202715)
                      ·
                        rfl

theorem cell23_2500000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2500000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500000 prefixEnd_2500000 := by exact prefixLift 2500000
  have htrace : WordTrace (prefixWord ++ tailWord_2500000) baseStart_2500000 baseEnd_2500000 := by
    simpa [prefixWord, tailWord_2500000, baseEnd_2500000] using wordTrace_append hprefix tailTrace_2500000
  have hstable : (prefixWord ++ tailWord_2500000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500000).length < 2 ^ (prefixWord ++ tailWord_2500000).sum := by decide
  have hdescent : baseEnd_2500000 < baseStart_2500000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500067 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 4, 5]
def baseStart_2500067 : Nat := 118140960795 + 2500067 * 2 ^ 59
def prefixEnd_2500067 : Nat := 4983230072969 + 3 ^ 40 * 2500067 * 2
def baseEnd_2500067 : Nat := 427912013148058403354969

theorem tailTrace_2500067 : CollatzResearch.WordTrace tailWord_2500067 prefixEnd_2500067 427912013148058403354969 := by
  unfold tailWord_2500067
  simp only [CollatzResearch.WordTrace]
  refine ⟨91184934633691711295298455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60789956422461140863532303 91184934633691711295298455)
  ·
    refine ⟨136777401950537566942947683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91184934633691711295298455 136777401950537566942947683)
    ·
      refine ⟨205166102925806350414421525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136777401950537566942947683 205166102925806350414421525)
      ·
        refine ⟨9617161074647172675676009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 205166102925806350414421525 9617161074647172675676009)
        ·
          refine ⟨7212870805985379506757007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9617161074647172675676009 7212870805985379506757007)
          ·
            refine ⟨10819306208978069260135511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212870805985379506757007 10819306208978069260135511)
            ·
              refine ⟨16228959313467103890203267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819306208978069260135511 16228959313467103890203267)
              ·
                refine ⟨24343438970200655835304901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16228959313467103890203267 24343438970200655835304901)
                ·
                  refine ⟨4564394806912622969119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24343438970200655835304901 4564394806912622969119669)
                  ·
                    refine ⟨427912013148058403354969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4564394806912622969119669 427912013148058403354969)
                    ·
                      rfl

theorem cell23_2500067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].length) (baseStart_2500067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500067 prefixEnd_2500067 := by exact prefixLift 2500067
  have htrace : WordTrace (prefixWord ++ tailWord_2500067) baseStart_2500067 baseEnd_2500067 := by
    simpa [prefixWord, tailWord_2500067, baseEnd_2500067] using wordTrace_append hprefix tailTrace_2500067
  have hstable : (prefixWord ++ tailWord_2500067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500067).length < 2 ^ (prefixWord ++ tailWord_2500067).sum := by decide
  have hdescent : baseEnd_2500067 < baseStart_2500067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500071 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 5]
def baseStart_2500071 : Nat := 118140960795 + 2500071 * 2 ^ 59
def prefixEnd_2500071 : Nat := 4983230072969 + 3 ^ 40 * 2500071 * 2
def baseEnd_2500071 : Nat := 142637565929643688268321

theorem tailTrace_2500071 : CollatzResearch.WordTrace tailWord_2500071 prefixEnd_2500071 142637565929643688268321 := by
  unfold tailWord_2500071
  simp only [CollatzResearch.WordTrace]
  refine ⟨91185080525677219978444067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60790053683784813318962711 91185080525677219978444067)
  ·
    refine ⟨136777620788515829967666101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91185080525677219978444067 136777620788515829967666101)
    ·
      refine ⟨12822901948923359059468697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136777620788515829967666101 12822901948923359059468697)
      ·
        refine ⟨9617176461692519294601523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12822901948923359059468697 9617176461692519294601523)
        ·
          refine ⟨14425764692538778941902285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9617176461692519294601523 14425764692538778941902285)
          ·
            refine ⟨5409661759702042103213357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14425764692538778941902285 5409661759702042103213357)
            ·
              refine ⟨2028623159888265788705009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5409661759702042103213357 2028623159888265788705009)
              ·
                refine ⟨1521467369916199341528757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028623159888265788705009 1521467369916199341528757)
                ·
                  refine ⟨142637565929643688268321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1521467369916199341528757 142637565929643688268321)
                  ·
                    rfl

theorem cell23_2500071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 5].length) (baseStart_2500071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500071 prefixEnd_2500071 := by exact prefixLift 2500071
  have htrace : WordTrace (prefixWord ++ tailWord_2500071) baseStart_2500071 baseEnd_2500071 := by
    simpa [prefixWord, tailWord_2500071, baseEnd_2500071] using wordTrace_append hprefix tailTrace_2500071
  have hstable : (prefixWord ++ tailWord_2500071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500071).length < 2 ^ (prefixWord ++ tailWord_2500071).sum := by decide
  have hdescent : baseEnd_2500071 < baseStart_2500071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500124 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2500124 : Nat := 118140960795 + 2500124 * 2 ^ 59
def prefixEnd_2500124 : Nat := 4983230072969 + 3 ^ 40 * 2500124 * 2
def baseEnd_2500124 : Nat := 1283765307841481487052145

theorem tailTrace_2500124 : CollatzResearch.WordTrace tailWord_2500124 prefixEnd_2500124 1283765307841481487052145 := by
  unfold tailWord_2500124
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593506797242605015061713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60791342396323473353415617 45593506797242605015061713)
  ·
    refine ⟨34195130097931953761296285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45593506797242605015061713 34195130097931953761296285)
    ·
      refine ⟨12823173786724482660486107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34195130097931953761296285 12823173786724482660486107)
      ·
        refine ⟨19234760680086723990729161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12823173786724482660486107 19234760680086723990729161)
        ·
          refine ⟨14426070510065042993046871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19234760680086723990729161 14426070510065042993046871)
          ·
            refine ⟨21639105765097564489570307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14426070510065042993046871 21639105765097564489570307)
            ·
              refine ⟨32458658647646346734355461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21639105765097564489570307 32458658647646346734355461)
              ·
                refine ⟨6085998496433690012691649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32458658647646346734355461 6085998496433690012691649)
                ·
                  refine ⟨4564498872325267509518737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6085998496433690012691649 4564498872325267509518737)
                  ·
                    refine ⟨3423374154243950632139053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564498872325267509518737 3423374154243950632139053)
                    ·
                      refine ⟨1283765307841481487052145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423374154243950632139053 1283765307841481487052145)
                      ·
                        rfl

theorem cell23_2500124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2500124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500124 prefixEnd_2500124 := by exact prefixLift 2500124
  have htrace : WordTrace (prefixWord ++ tailWord_2500124) baseStart_2500124 baseEnd_2500124 := by
    simpa [prefixWord, tailWord_2500124, baseEnd_2500124] using wordTrace_append hprefix tailTrace_2500124
  have hstable : (prefixWord ++ tailWord_2500124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500124).length < 2 ^ (prefixWord ++ tailWord_2500124).sum := by decide
  have hdescent : baseEnd_2500124 < baseStart_2500124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500127 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 6]
def baseStart_2500127 : Nat := 118140960795 + 2500127 * 2 ^ 59
def prefixEnd_2500127 : Nat := 4983230072969 + 3 ^ 40 * 2500127 * 2
def baseEnd_2500127 : Nat := 142640760920382775034959

theorem tailTrace_2500127 : CollatzResearch.WordTrace tailWord_2500127 prefixEnd_2500127 142640760920382775034959 := by
  unfold tailWord_2500127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91187123013474341542482635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60791415342316227694988423 91187123013474341542482635)
  ·
    refine ⟨136780684520211512313723953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91187123013474341542482635 136780684520211512313723953)
    ·
      refine ⟨102585513390158634235292965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136780684520211512313723953 102585513390158634235292965)
      ·
        refine ⟨19234783760654743919117431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102585513390158634235292965 19234783760654743919117431)
        ·
          refine ⟨28852175640982115878676147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19234783760654743919117431 28852175640982115878676147)
          ·
            refine ⟨43278263461473173818014221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28852175640982115878676147 43278263461473173818014221)
            ·
              refine ⟨16229348798052440181755333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43278263461473173818014221 16229348798052440181755333)
              ·
                refine ⟨3043002899634832534079125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16229348798052440181755333 3043002899634832534079125)
                ·
                  refine ⟨142640760920382775034959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3043002899634832534079125 142640760920382775034959)
                  ·
                    rfl

theorem cell23_2500127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 6].length) (baseStart_2500127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500127 prefixEnd_2500127 := by exact prefixLift 2500127
  have htrace : WordTrace (prefixWord ++ tailWord_2500127) baseStart_2500127 baseEnd_2500127 := by
    simpa [prefixWord, tailWord_2500127, baseEnd_2500127] using wordTrace_append hprefix tailTrace_2500127
  have hstable : (prefixWord ++ tailWord_2500127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500127).length < 2 ^ (prefixWord ++ tailWord_2500127).sum := by decide
  have hdescent : baseEnd_2500127 < baseStart_2500127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500188 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2500188 : Nat := 118140960795 + 2500188 * 2 ^ 59
def prefixEnd_2500188 : Nat := 4983230072969 + 3 ^ 40 * 2500188 * 2
def baseEnd_2500188 : Nat := 1283798170603369236651851

theorem tailTrace_2500188 : CollatzResearch.WordTrace tailWord_2500188 prefixEnd_2500188 1283798170603369236651851 := by
  unfold tailWord_2500188
  simp only [CollatzResearch.WordTrace]
  refine ⟨45594673933126674480226609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60792898577502232640302145 45594673933126674480226609)
  ·
    refine ⟨34196005449845005860169957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45594673933126674480226609 34196005449845005860169957)
    ·
      refine ⟨6411751021845938598781867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34196005449845005860169957 6411751021845938598781867)
      ·
        refine ⟨9617626532768907898172801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411751021845938598781867 9617626532768907898172801)
        ·
          refine ⟨7213219899576680923629601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9617626532768907898172801 7213219899576680923629601)
          ·
            refine ⟨5409914924682510692722201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7213219899576680923629601 5409914924682510692722201)
            ·
              refine ⟨4057436193511883019541651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5409914924682510692722201 4057436193511883019541651)
              ·
                refine ⟨6086154290267824529312477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057436193511883019541651 6086154290267824529312477)
                ·
                  refine ⟨2282307858850434198492179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6086154290267824529312477 2282307858850434198492179)
                  ·
                    refine ⟨3423461788275651297738269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282307858850434198492179 3423461788275651297738269)
                    ·
                      refine ⟨1283798170603369236651851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423461788275651297738269 1283798170603369236651851)
                      ·
                        rfl

theorem cell23_2500188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2500188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500188 prefixEnd_2500188 := by exact prefixLift 2500188
  have htrace : WordTrace (prefixWord ++ tailWord_2500188) baseStart_2500188 baseEnd_2500188 := by
    simpa [prefixWord, tailWord_2500188, baseEnd_2500188] using wordTrace_append hprefix tailTrace_2500188
  have hstable : (prefixWord ++ tailWord_2500188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500188).length < 2 ^ (prefixWord ++ tailWord_2500188).sum := by decide
  have hdescent : baseEnd_2500188 < baseStart_2500188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500217 : List Nat := [1, 2, 1, 3, 3, 1, 3, 9]
def baseStart_2500217 : Nat := 118140960795 + 2500217 * 2 ^ 59
def prefixEnd_2500217 : Nat := 4983230072969 + 3 ^ 40 * 2500217 * 2
def baseEnd_2500217 : Nat := 47548631908975911969971

theorem tailTrace_2500217 : CollatzResearch.WordTrace tailWord_2500217 prefixEnd_2500217 47548631908975911969971 := by
  unfold tailWord_2500217
  simp only [CollatzResearch.WordTrace]
  refine ⟨91190405583148286913258905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60793603722098857942172603 91190405583148286913258905)
  ·
    refine ⟨68392804187361215184944179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91190405583148286913258905 68392804187361215184944179)
    ·
      refine ⟨102589206281041822777416269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68392804187361215184944179 102589206281041822777416269)
      ·
        refine ⟨38470952355390683541531101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102589206281041822777416269 38470952355390683541531101)
        ·
          refine ⟨14426607133271506328074163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38470952355390683541531101 14426607133271506328074163)
          ·
            refine ⟨21639910699907259492111245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14426607133271506328074163 21639910699907259492111245)
            ·
              refine ⟨8114966512465222309541717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21639910699907259492111245 8114966512465222309541717)
              ·
                refine ⟨47548631908975911969971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8114966512465222309541717 47548631908975911969971)
                ·
                  rfl

theorem cell23_2500217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 9].length) (baseStart_2500217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500217 prefixEnd_2500217 := by exact prefixLift 2500217
  have htrace : WordTrace (prefixWord ++ tailWord_2500217) baseStart_2500217 baseEnd_2500217 := by
    simpa [prefixWord, tailWord_2500217, baseEnd_2500217] using wordTrace_append hprefix tailTrace_2500217
  have hstable : (prefixWord ++ tailWord_2500217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500217).length < 2 ^ (prefixWord ++ tailWord_2500217).sum := by decide
  have hdescent : baseEnd_2500217 < baseStart_2500217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500231 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2500231 : Nat := 118140960795 + 2500231 * 2 ^ 59
def prefixEnd_2500231 : Nat := 4983230072969 + 3 ^ 40 * 2500231 * 2
def baseEnd_2500231 : Nat := 1283820250271512568414153

theorem tailTrace_2500231 : CollatzResearch.WordTrace tailWord_2500231 prefixEnd_2500231 1283820250271512568414153 := by
  unfold tailWord_2500231
  simp only [CollatzResearch.WordTrace]
  refine ⟨91190916205097567304268547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60793944136731711536179031 91190916205097567304268547)
  ·
    refine ⟨136786374307646350956402821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91190916205097567304268547 136786374307646350956402821)
    ·
      refine ⟨25647445182683690804325529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136786374307646350956402821 25647445182683690804325529)
      ·
        refine ⟨19235583887012768103244147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25647445182683690804325529 19235583887012768103244147)
        ·
          refine ⟨28853375830519152154866221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19235583887012768103244147 28853375830519152154866221)
          ·
            refine ⟨10820015936444682058074833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28853375830519152154866221 10820015936444682058074833)
            ·
              refine ⟨8115011952333511543556125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10820015936444682058074833 8115011952333511543556125)
              ·
                refine ⟨3043129482125066828833547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8115011952333511543556125 3043129482125066828833547)
                ·
                  refine ⟨4564694223187600243250321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043129482125066828833547 4564694223187600243250321)
                  ·
                    refine ⟨3423520667390700182437741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564694223187600243250321 3423520667390700182437741)
                    ·
                      refine ⟨1283820250271512568414153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423520667390700182437741 1283820250271512568414153)
                      ·
                        rfl

theorem cell23_2500231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2500231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500231 prefixEnd_2500231 := by exact prefixLift 2500231
  have htrace : WordTrace (prefixWord ++ tailWord_2500231) baseStart_2500231 baseEnd_2500231 := by
    simpa [prefixWord, tailWord_2500231, baseEnd_2500231] using wordTrace_append hprefix tailTrace_2500231
  have hstable : (prefixWord ++ tailWord_2500231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500231).length < 2 ^ (prefixWord ++ tailWord_2500231).sum := by decide
  have hdescent : baseEnd_2500231 < baseStart_2500231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500234 : List Nat := [3, 1, 2, 3, 2, 3, 9]
def baseStart_2500234 : Nat := 118140960795 + 2500234 * 2 ^ 59
def prefixEnd_2500234 : Nat := 4983230072969 + 3 ^ 40 * 2500234 * 2
def baseEnd_2500234 : Nat := 15849651737203408107119

theorem tailTrace_2500234 : CollatzResearch.WordTrace tailWord_2500234 prefixEnd_2500234 15849651737203408107119 := by
  unfold tailWord_2500234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797756406021674704156939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60794017082724465877751837 22797756406021674704156939)
  ·
    refine ⟨34196634609032512056235409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22797756406021674704156939 34196634609032512056235409)
    ·
      refine ⟨25647475956774384042176557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34196634609032512056235409 25647475956774384042176557)
      ·
        refine ⟨9617803483790394015816209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25647475956774384042176557 9617803483790394015816209)
        ·
          refine ⟨7213352612842795511862157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9617803483790394015816209 7213352612842795511862157)
          ·
            refine ⟨2705007229816048316948309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7213352612842795511862157 2705007229816048316948309)
            ·
              refine ⟨15849651737203408107119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2705007229816048316948309 15849651737203408107119)
              ·
                rfl

theorem cell23_2500234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 9].length) (baseStart_2500234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500234 prefixEnd_2500234 := by exact prefixLift 2500234
  have htrace : WordTrace (prefixWord ++ tailWord_2500234) baseStart_2500234 baseEnd_2500234 := by
    simpa [prefixWord, tailWord_2500234, baseEnd_2500234] using wordTrace_append hprefix tailTrace_2500234
  have hstable : (prefixWord ++ tailWord_2500234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500234).length < 2 ^ (prefixWord ++ tailWord_2500234).sum := by decide
  have hdescent : baseEnd_2500234 < baseStart_2500234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500271 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 3, 3, 2]
def baseStart_2500271 : Nat := 118140960795 + 2500271 * 2 ^ 59
def prefixEnd_2500271 : Nat := 4983230072969 + 3 ^ 40 * 2500271 * 2
def baseEnd_2500271 : Nat := 1283840789497692411913969

theorem tailTrace_2500271 : CollatzResearch.WordTrace tailWord_2500271 prefixEnd_2500271 1283840789497692411913969 := by
  unfold tailWord_2500271
  simp only [CollatzResearch.WordTrace]
  refine ⟨91192375124952654135724667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60794916749968436090483111 91192375124952654135724667)
  ·
    refine ⟨136788562687428981203587001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91192375124952654135724667 136788562687428981203587001)
    ·
      refine ⟨102591422015571735902690251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136788562687428981203587001 102591422015571735902690251)
      ·
        refine ⟨153887133023357603854035377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102591422015571735902690251 153887133023357603854035377)
        ·
          refine ⟨115415349767518202890526533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153887133023357603854035377 115415349767518202890526533)
          ·
            refine ⟨21640378081409663041973725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115415349767518202890526533 21640378081409663041973725)
            ·
              refine ⟨8115141780528623640740147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21640378081409663041973725 8115141780528623640740147)
              ·
                refine ⟨12172712670792935461110221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8115141780528623640740147 12172712670792935461110221)
                ·
                  refine ⟨4564767251547350797916333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12172712670792935461110221 4564767251547350797916333)
                  ·
                    refine ⟨1711787719330256549218625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4564767251547350797916333 1711787719330256549218625)
                    ·
                      refine ⟨1283840789497692411913969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1711787719330256549218625 1283840789497692411913969)
                      ·
                        rfl

theorem cell23_2500271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3, 2].length) (baseStart_2500271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500271 prefixEnd_2500271 := by exact prefixLift 2500271
  have htrace : WordTrace (prefixWord ++ tailWord_2500271) baseStart_2500271 baseEnd_2500271 := by
    simpa [prefixWord, tailWord_2500271, baseEnd_2500271] using wordTrace_append hprefix tailTrace_2500271
  have hstable : (prefixWord ++ tailWord_2500271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500271).length < 2 ^ (prefixWord ++ tailWord_2500271).sum := by decide
  have hdescent : baseEnd_2500271 < baseStart_2500271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500278 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2500278 : Nat := 118140960795 + 2500278 * 2 ^ 59
def prefixEnd_2500278 : Nat := 4983230072969 + 3 ^ 40 * 2500278 * 2
def baseEnd_2500278 : Nat := 1283844383862273884526437

theorem tailTrace_2500278 : CollatzResearch.WordTrace tailWord_2500278 prefixEnd_2500278 1283844383862273884526437 := by
  unfold tailWord_2500278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699539402245455895701843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60795086957284862887486325 5699539402245455895701843)
  ·
    refine ⟨8549309103368183843552765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5699539402245455895701843 8549309103368183843552765)
    ·
      refine ⟨3205990913763068941332287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8549309103368183843552765 3205990913763068941332287)
      ·
        refine ⟨4808986370644603411998431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205990913763068941332287 4808986370644603411998431)
        ·
          refine ⟨7213479555966905117997647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808986370644603411998431 7213479555966905117997647)
          ·
            refine ⟨10820219333950357676996471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7213479555966905117997647 10820219333950357676996471)
            ·
              refine ⟨16230329000925536515494707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10820219333950357676996471 16230329000925536515494707)
              ·
                refine ⟨24345493501388304773242061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16230329000925536515494707 24345493501388304773242061)
                ·
                  refine ⟨9129560063020614289965773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24345493501388304773242061 9129560063020614289965773)
                  ·
                    refine ⟨3423585023632730358737165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9129560063020614289965773 3423585023632730358737165)
                    ·
                      refine ⟨1283844383862273884526437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423585023632730358737165 1283844383862273884526437)
                      ·
                        rfl

theorem cell23_2500278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2500278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500278 prefixEnd_2500278 := by exact prefixLift 2500278
  have htrace : WordTrace (prefixWord ++ tailWord_2500278) baseStart_2500278 baseEnd_2500278 := by
    simpa [prefixWord, tailWord_2500278, baseEnd_2500278] using wordTrace_append hprefix tailTrace_2500278
  have hstable : (prefixWord ++ tailWord_2500278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500278).length < 2 ^ (prefixWord ++ tailWord_2500278).sum := by decide
  have hdescent : baseEnd_2500278 < baseStart_2500278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500314 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2500314 : Nat := 118140960795 + 2500314 * 2 ^ 59
def prefixEnd_2500314 : Nat := 4983230072969 + 3 ^ 40 * 2500314 * 2
def baseEnd_2500314 : Nat := 1283862869165835743676271

theorem tailTrace_2500314 : CollatzResearch.WordTrace tailWord_2500314 prefixEnd_2500314 1283862869165835743676271 := by
  unfold tailWord_2500314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22798485865949218119884999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60795962309197914986359997 22798485865949218119884999)
  ·
    refine ⟨34197728798923827179827499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22798485865949218119884999 34197728798923827179827499)
    ·
      refine ⟨51296593198385740769741249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34197728798923827179827499 51296593198385740769741249)
      ·
        refine ⟨38472444898789305577305937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51296593198385740769741249 38472444898789305577305937)
        ·
          refine ⟨28854333674091979182979453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38472444898789305577305937 28854333674091979182979453)
          ·
            refine ⟨10820375127784492193617295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28854333674091979182979453 10820375127784492193617295)
            ·
              refine ⟨16230562691676738290425943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10820375127784492193617295 16230562691676738290425943)
              ·
                refine ⟨24345844037515107435638915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16230562691676738290425943 24345844037515107435638915)
                ·
                  refine ⟨36518766056272661153458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24345844037515107435638915 36518766056272661153458373)
                  ·
                    refine ⟨6847268635551123966273445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36518766056272661153458373 6847268635551123966273445)
                    ·
                      refine ⟨1283862869165835743676271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6847268635551123966273445 1283862869165835743676271)
                      ·
                        rfl

theorem cell23_2500314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2500314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500314 prefixEnd_2500314 := by exact prefixLift 2500314
  have htrace : WordTrace (prefixWord ++ tailWord_2500314) baseStart_2500314 baseEnd_2500314 := by
    simpa [prefixWord, tailWord_2500314, baseEnd_2500314] using wordTrace_append hprefix tailTrace_2500314
  have hstable : (prefixWord ++ tailWord_2500314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500314).length < 2 ^ (prefixWord ++ tailWord_2500314).sum := by decide
  have hdescent : baseEnd_2500314 < baseStart_2500314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500324 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 7]
def baseStart_2500324 : Nat := 118140960795 + 2500324 * 2 ^ 59
def prefixEnd_2500324 : Nat := 4983230072969 + 3 ^ 40 * 2500324 * 2
def baseEnd_2500324 : Nat := 142652000441375633839025

theorem tailTrace_2500324 : CollatzResearch.WordTrace tailWord_2500324 prefixEnd_2500324 142652000441375633839025 := by
  unfold tailWord_2500324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45597154096880322093702013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60796205462507096124936017 45597154096880322093702013)
  ·
    refine ⟨17098932786330120785138255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45597154096880322093702013 17098932786330120785138255)
    ·
      refine ⟨25648399179495181177707383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17098932786330120785138255 25648399179495181177707383)
      ·
        refine ⟨38472598769242771766561075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25648399179495181177707383 38472598769242771766561075)
        ·
          refine ⟨57708898153864157649841613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38472598769242771766561075 57708898153864157649841613)
          ·
            refine ⟨21640836807699059118690605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57708898153864157649841613 21640836807699059118690605)
            ·
              refine ⟨8115313802887147169508977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21640836807699059118690605 8115313802887147169508977)
              ·
                refine ⟨6086485352165360377131733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8115313802887147169508977 6086485352165360377131733)
                ·
                  refine ⟨142652000441375633839025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6086485352165360377131733 142652000441375633839025)
                  ·
                    rfl

theorem cell23_2500324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_2500324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500324 prefixEnd_2500324 := by exact prefixLift 2500324
  have htrace : WordTrace (prefixWord ++ tailWord_2500324) baseStart_2500324 baseEnd_2500324 := by
    simpa [prefixWord, tailWord_2500324, baseEnd_2500324] using wordTrace_append hprefix tailTrace_2500324
  have hstable : (prefixWord ++ tailWord_2500324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500324).length < 2 ^ (prefixWord ++ tailWord_2500324).sum := by decide
  have hdescent : baseEnd_2500324 < baseStart_2500324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500364 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2500364 : Nat := 118140960795 + 2500364 * 2 ^ 59
def prefixEnd_2500364 : Nat := 4983230072969 + 3 ^ 40 * 2500364 * 2
def baseEnd_2500364 : Nat := 1283888543198560548051041

theorem tailTrace_2500364 : CollatzResearch.WordTrace tailWord_2500364 prefixEnd_2500364 1283888543198560548051041 := by
  unfold tailWord_2500364
  simp only [CollatzResearch.WordTrace]
  refine ⟨45597883556807865509430073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60797178075743820679240097 45597883556807865509430073)
  ·
    refine ⟨34198412667605899132072555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45597883556807865509430073 34198412667605899132072555)
    ·
      refine ⟨51297619001408848698108833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34198412667605899132072555 51297619001408848698108833)
      ·
        refine ⟨38473214251056636523581625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51297619001408848698108833 38473214251056636523581625)
        ·
          refine ⟨28854910688292477392686219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38473214251056636523581625 28854910688292477392686219)
          ·
            refine ⟨43282366032438716089029329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28854910688292477392686219 43282366032438716089029329)
            ·
              refine ⟨32461774524329037066771997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43282366032438716089029329 32461774524329037066771997)
              ·
                refine ⟨12173165446623388900039499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32461774524329037066771997 12173165446623388900039499)
                ·
                  refine ⟨18259748169935083350059249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12173165446623388900039499 18259748169935083350059249)
                  ·
                    refine ⟨13694811127451312512544437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18259748169935083350059249 13694811127451312512544437)
                    ·
                      refine ⟨1283888543198560548051041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13694811127451312512544437 1283888543198560548051041)
                      ·
                        rfl

theorem cell23_2500364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2500364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500364 prefixEnd_2500364 := by exact prefixLift 2500364
  have htrace : WordTrace (prefixWord ++ tailWord_2500364) baseStart_2500364 baseEnd_2500364 := by
    simpa [prefixWord, tailWord_2500364, baseEnd_2500364] using wordTrace_append hprefix tailTrace_2500364
  have hstable : (prefixWord ++ tailWord_2500364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500364).length < 2 ^ (prefixWord ++ tailWord_2500364).sum := by decide
  have hdescent : baseEnd_2500364 < baseStart_2500364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500384 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 8]
def baseStart_2500384 : Nat := 118140960795 + 2500384 * 2 ^ 59
def prefixEnd_2500384 : Nat := 4983230072969 + 3 ^ 40 * 2500384 * 2
def baseEnd_2500384 : Nat := 427966270937216823266983

theorem tailTrace_2500384 : CollatzResearch.WordTrace tailWord_2500384 prefixEnd_2500384 427966270937216823266983 := by
  unfold tailWord_2500384
  simp only [CollatzResearch.WordTrace]
  refine ⟨45598248286771637217294103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60797664382362182956392137 45598248286771637217294103)
  ·
    refine ⟨68397372430157455825941155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45598248286771637217294103 68397372430157455825941155)
    ·
      refine ⟨102596058645236183738911733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68397372430157455825941155 102596058645236183738911733)
      ·
        refine ⟨9618380497990892225522975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102596058645236183738911733 9618380497990892225522975)
        ·
          refine ⟨14427570746986338338284463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9618380497990892225522975 14427570746986338338284463)
          ·
            refine ⟨21641356120479507507426695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14427570746986338338284463 21641356120479507507426695)
            ·
              refine ⟨32462034180719261261140043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21641356120479507507426695 32462034180719261261140043)
              ·
                refine ⟨48693051271078891891710065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32462034180719261261140043 48693051271078891891710065)
                ·
                  refine ⟨36519788453309168918782549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48693051271078891891710065 36519788453309168918782549)
                  ·
                    refine ⟨427966270937216823266983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36519788453309168918782549 427966270937216823266983)
                    ·
                      rfl

theorem cell23_2500384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_2500384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500384 prefixEnd_2500384 := by exact prefixLift 2500384
  have htrace : WordTrace (prefixWord ++ tailWord_2500384) baseStart_2500384 baseEnd_2500384 := by
    simpa [prefixWord, tailWord_2500384, baseEnd_2500384] using wordTrace_append hprefix tailTrace_2500384
  have hstable : (prefixWord ++ tailWord_2500384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500384).length < 2 ^ (prefixWord ++ tailWord_2500384).sum := by decide
  have hdescent : baseEnd_2500384 < baseStart_2500384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500491 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 6, 4]
def baseStart_2500491 : Nat := 118140960795 + 2500491 * 2 ^ 59
def prefixEnd_2500491 : Nat := 4983230072969 + 3 ^ 40 * 2500491 * 2
def baseEnd_2500491 : Nat := 427984585080560517054319

theorem tailTrace_2500491 : CollatzResearch.WordTrace tailWord_2500491 prefixEnd_2500491 427984585080560517054319 := by
  unfold tailWord_2500491
  simp only [CollatzResearch.WordTrace]
  refine ⟨91200399184155631708733327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60800266122770421139155551 91200399184155631708733327)
  ·
    refine ⟨136800598776233447563099991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91200399184155631708733327 136800598776233447563099991)
    ·
      refine ⟨205200898164350171344649987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136800598776233447563099991 205200898164350171344649987)
      ·
        refine ⟨307801347246525257016974981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205200898164350171344649987 307801347246525257016974981)
        ·
          refine ⟨57712752608723485690682809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307801347246525257016974981 57712752608723485690682809)
          ·
            refine ⟨43284564456542614268012107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57712752608723485690682809 43284564456542614268012107)
            ·
              refine ⟨64926846684813921402018161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43284564456542614268012107 64926846684813921402018161)
              ·
                refine ⟨48695135013610441051513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64926846684813921402018161 48695135013610441051513621)
                ·
                  refine ⟨2282584453762989424289701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48695135013610441051513621 2282584453762989424289701)
                  ·
                    refine ⟨427984585080560517054319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282584453762989424289701 427984585080560517054319)
                    ·
                      rfl

theorem cell23_2500491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 4].length) (baseStart_2500491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500491 prefixEnd_2500491 := by exact prefixLift 2500491
  have htrace : WordTrace (prefixWord ++ tailWord_2500491) baseStart_2500491 baseEnd_2500491 := by
    simpa [prefixWord, tailWord_2500491, baseEnd_2500491] using wordTrace_append hprefix tailTrace_2500491
  have hstable : (prefixWord ++ tailWord_2500491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500491).length < 2 ^ (prefixWord ++ tailWord_2500491).sum := by decide
  have hdescent : baseEnd_2500491 < baseStart_2500491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500508 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2500508 : Nat := 118140960795 + 2500508 * 2 ^ 59
def prefixEnd_2500508 : Nat := 4983230072969 + 3 ^ 40 * 2500508 * 2
def baseEnd_2500508 : Nat := 427987494804269328216793

theorem tailTrace_2500508 : CollatzResearch.WordTrace tailWord_2500508 prefixEnd_2500508 427987494804269328216793 := by
  unfold tailWord_2500508
  simp only [CollatzResearch.WordTrace]
  refine ⟨45600509612547021806051089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60800679483396029074734785 45600509612547021806051089)
  ·
    refine ⟨34200382209410266354538317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45600509612547021806051089 34200382209410266354538317)
    ·
      refine ⟨12825143328528849882951869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34200382209410266354538317 12825143328528849882951869)
      ·
        refine ⟨4809428748198318706106951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12825143328528849882951869 4809428748198318706106951)
        ·
          refine ⟨7214143122297478059160427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809428748198318706106951 7214143122297478059160427)
          ·
            refine ⟨10821214683446217088740641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214143122297478059160427 10821214683446217088740641)
            ·
              refine ⟨8115911012584662816555481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10821214683446217088740641 8115911012584662816555481)
              ·
                refine ⟨6086933259438497112416611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8115911012584662816555481 6086933259438497112416611)
                ·
                  refine ⟨9130399889157745668624917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6086933259438497112416611 9130399889157745668624917)
                  ·
                    refine ⟨427987494804269328216793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9130399889157745668624917 427987494804269328216793)
                    ·
                      rfl

theorem cell23_2500508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2500508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500508 prefixEnd_2500508 := by exact prefixLift 2500508
  have htrace : WordTrace (prefixWord ++ tailWord_2500508) baseStart_2500508 baseEnd_2500508 := by
    simpa [prefixWord, tailWord_2500508, baseEnd_2500508] using wordTrace_append hprefix tailTrace_2500508
  have hstable : (prefixWord ++ tailWord_2500508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500508).length < 2 ^ (prefixWord ++ tailWord_2500508).sum := by decide
  have hdescent : baseEnd_2500508 < baseStart_2500508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500526 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2500526 : Nat := 118140960795 + 2500526 * 2 ^ 59
def prefixEnd_2500526 : Nat := 4983230072969 + 3 ^ 40 * 2500526 * 2
def baseEnd_2500526 : Nat := 1283971727064588914225297

theorem tailTrace_2500526 : CollatzResearch.WordTrace tailWord_2500526 prefixEnd_2500526 1283971727064588914225297 := by
  unfold tailWord_2500526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400209467378604085782179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60801117159352555124171621 11400209467378604085782179)
  ·
    refine ⟨17100314201067906128673269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400209467378604085782179 17100314201067906128673269)
    ·
      refine ⟨1603154456350116199563119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17100314201067906128673269 1603154456350116199563119)
      ·
        refine ⟨2404731684525174299344679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603154456350116199563119 2404731684525174299344679)
        ·
          refine ⟨3607097526787761449017019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404731684525174299344679 3607097526787761449017019)
          ·
            refine ⟨5410646290181642173525529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607097526787761449017019 5410646290181642173525529)
            ·
              refine ⟨4057984717636231630144147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410646290181642173525529 4057984717636231630144147)
              ·
                refine ⟨6086977076454347445216221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057984717636231630144147 6086977076454347445216221)
                ·
                  refine ⟨2282616403670380291956083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6086977076454347445216221 2282616403670380291956083)
                  ·
                    refine ⟨3423924605505570437934125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282616403670380291956083 3423924605505570437934125)
                    ·
                      refine ⟨1283971727064588914225297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423924605505570437934125 1283971727064588914225297)
                      ·
                        rfl

theorem cell23_2500526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2500526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500526 prefixEnd_2500526 := by exact prefixLift 2500526
  have htrace : WordTrace (prefixWord ++ tailWord_2500526) baseStart_2500526 baseEnd_2500526 := by
    simpa [prefixWord, tailWord_2500526, baseEnd_2500526] using wordTrace_append hprefix tailTrace_2500526
  have hstable : (prefixWord ++ tailWord_2500526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500526).length < 2 ^ (prefixWord ++ tailWord_2500526).sum := by decide
  have hdescent : baseEnd_2500526 < baseStart_2500526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500542 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2500542 : Nat := 118140960795 + 2500542 * 2 ^ 59
def prefixEnd_2500542 : Nat := 4983230072969 + 3 ^ 40 * 2500542 * 2
def baseEnd_2500542 : Nat := 427993314251686950541741

theorem tailTrace_2500542 : CollatzResearch.WordTrace tailWord_2500542 prefixEnd_2500542 427993314251686950541741 := by
  unfold tailWord_2500542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400282413371358427354985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60801506204647244945893253 11400282413371358427354985)
  ·
    refine ⟨8550211810028518820516239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11400282413371358427354985 8550211810028518820516239)
    ·
      refine ⟨12825317715042778230774359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8550211810028518820516239 12825317715042778230774359)
      ·
        refine ⟨19237976572564167346161539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825317715042778230774359 19237976572564167346161539)
        ·
          refine ⟨28856964858846251019242309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19237976572564167346161539 28856964858846251019242309)
          ·
            refine ⟨5410680911033672066107933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28856964858846251019242309 5410680911033672066107933)
            ·
              refine ⟨2029005341637627024790475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5410680911033672066107933 2029005341637627024790475)
              ·
                refine ⟨3043508012456440537185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029005341637627024790475 3043508012456440537185713)
                ·
                  refine ⟨2282631009342330402889285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043508012456440537185713 2282631009342330402889285)
                  ·
                    refine ⟨427993314251686950541741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282631009342330402889285 427993314251686950541741)
                    ·
                      rfl

theorem cell23_2500542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2500542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500542 prefixEnd_2500542 := by exact prefixLift 2500542
  have htrace : WordTrace (prefixWord ++ tailWord_2500542) baseStart_2500542 baseEnd_2500542 := by
    simpa [prefixWord, tailWord_2500542, baseEnd_2500542] using wordTrace_append hprefix tailTrace_2500542
  have hstable : (prefixWord ++ tailWord_2500542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500542).length < 2 ^ (prefixWord ++ tailWord_2500542).sum := by decide
  have hdescent : baseEnd_2500542 < baseStart_2500542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500565 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2500565 : Nat := 118140960795 + 2500565 * 2 ^ 59
def prefixEnd_2500565 : Nat := 4983230072969 + 3 ^ 40 * 2500565 * 2
def baseEnd_2500565 : Nat := 1283991752810114261637617

theorem tailTrace_2500565 : CollatzResearch.WordTrace tailWord_2500565 prefixEnd_2500565 1283991752810114261637617 := by
  unfold tailWord_2500565
  simp only [CollatzResearch.WordTrace]
  refine ⟨91203098185887542346927149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60802065457258361564618099 91203098185887542346927149)
  ·
    refine ⟨34201161819707828380097681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91203098185887542346927149 34201161819707828380097681)
    ·
      refine ⟨25650871364780871285073261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34201161819707828380097681 25650871364780871285073261)
      ·
        refine ⟨9619076761792826731902473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25650871364780871285073261 9619076761792826731902473)
        ·
          refine ⟨7214307571344620048926855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9619076761792826731902473 7214307571344620048926855)
          ·
            refine ⟨10821461357016930073390283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214307571344620048926855 10821461357016930073390283)
            ·
              refine ⟨16232192035525395110085425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10821461357016930073390283 16232192035525395110085425)
              ·
                refine ⟨12174144026644046332564069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16232192035525395110085425 12174144026644046332564069)
                ·
                  refine ⟨2282652004995758687355763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12174144026644046332564069 2282652004995758687355763)
                  ·
                    refine ⟨3423978007493638031033645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282652004995758687355763 3423978007493638031033645)
                    ·
                      refine ⟨1283991752810114261637617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3423978007493638031033645 1283991752810114261637617)
                      ·
                        rfl

theorem cell23_2500565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2500565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500565 prefixEnd_2500565 := by exact prefixLift 2500565
  have htrace : WordTrace (prefixWord ++ tailWord_2500565) baseStart_2500565 baseEnd_2500565 := by
    simpa [prefixWord, tailWord_2500565, baseEnd_2500565] using wordTrace_append hprefix tailTrace_2500565
  have hstable : (prefixWord ++ tailWord_2500565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500565).length < 2 ^ (prefixWord ++ tailWord_2500565).sum := by decide
  have hdescent : baseEnd_2500565 < baseStart_2500565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500572 : List Nat := [2, 2, 6, 1, 1, 2, 9]
def baseStart_2500572 : Nat := 118140960795 + 2500572 * 2 ^ 59
def prefixEnd_2500572 : Nat := 4983230072969 + 3 ^ 40 * 2500572 * 2
def baseEnd_2500572 : Nat := 15851794409564144867285

theorem tailTrace_2500572 : CollatzResearch.WordTrace tailWord_2500572 prefixEnd_2500572 15851794409564144867285 := by
  unfold tailWord_2500572
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601676748431091271215985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60802235664574788361621313 45601676748431091271215985)
  ·
    refine ⟨34201257561323318453411989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45601676748431091271215985 34201257561323318453411989)
    ·
      refine ⟨1603183948187030552503687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34201257561323318453411989 1603183948187030552503687)
      ·
        refine ⟨2404775922280545828755531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603183948187030552503687 2404775922280545828755531)
        ·
          refine ⟨3607163883420818743133297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404775922280545828755531 3607163883420818743133297)
          ·
            refine ⟨2705372912565614057349973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607163883420818743133297 2705372912565614057349973)
            ·
              refine ⟨15851794409564144867285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2705372912565614057349973 15851794409564144867285)
              ·
                rfl

theorem cell23_2500572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 9].length) (baseStart_2500572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500572 prefixEnd_2500572 := by exact prefixLift 2500572
  have htrace : WordTrace (prefixWord ++ tailWord_2500572) baseStart_2500572 baseEnd_2500572 := by
    simpa [prefixWord, tailWord_2500572, baseEnd_2500572] using wordTrace_append hprefix tailTrace_2500572
  have hstable : (prefixWord ++ tailWord_2500572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500572).length < 2 ^ (prefixWord ++ tailWord_2500572).sum := by decide
  have hdescent : baseEnd_2500572 < baseStart_2500572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500591 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_2500591 : Nat := 118140960795 + 2500591 * 2 ^ 59
def prefixEnd_2500591 : Nat := 4983230072969 + 3 ^ 40 * 2500591 * 2
def baseEnd_2500591 : Nat := 1284005103307131159912497

theorem tailTrace_2500591 : CollatzResearch.WordTrace tailWord_2500591 prefixEnd_2500591 1284005103307131159912497 := by
  unfold tailWord_2500591
  simp only [CollatzResearch.WordTrace]
  refine ⟨91204046483793348787373627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60802697655862232524915751 91204046483793348787373627)
  ·
    refine ⟨136806069725690023181060441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91204046483793348787373627 136806069725690023181060441)
    ·
      refine ⟨102604552294267517385795331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136806069725690023181060441 102604552294267517385795331)
      ·
        refine ⟨153906828441401276078692997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102604552294267517385795331 153906828441401276078692997)
        ·
          refine ⟨28857530332762739264754937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153906828441401276078692997 28857530332762739264754937)
          ·
            refine ⟨21643147749572054448566203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28857530332762739264754937 21643147749572054448566203)
            ·
              refine ⟨32464721624358081672849305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21643147749572054448566203 32464721624358081672849305)
              ·
                refine ⟨24348541218268561254636979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32464721624358081672849305 24348541218268561254636979)
                ·
                  refine ⟨36522811827402841881955469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24348541218268561254636979 36522811827402841881955469)
                  ·
                    refine ⟨13696054435276065705733301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36522811827402841881955469 13696054435276065705733301)
                    ·
                      refine ⟨1284005103307131159912497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13696054435276065705733301 1284005103307131159912497)
                      ·
                        rfl

theorem cell23_2500591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_2500591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500591 prefixEnd_2500591 := by exact prefixLift 2500591
  have htrace : WordTrace (prefixWord ++ tailWord_2500591) baseStart_2500591 baseEnd_2500591 := by
    simpa [prefixWord, tailWord_2500591, baseEnd_2500591] using wordTrace_append hprefix tailTrace_2500591
  have hstable : (prefixWord ++ tailWord_2500591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500591).length < 2 ^ (prefixWord ++ tailWord_2500591).sum := by decide
  have hdescent : baseEnd_2500591 < baseStart_2500591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500611 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 7]
def baseStart_2500611 : Nat := 118140960795 + 2500611 * 2 ^ 59
def prefixEnd_2500611 : Nat := 4983230072969 + 3 ^ 40 * 2500611 * 2
def baseEnd_2500611 : Nat := 142668374768913453518045

theorem tailTrace_2500611 : CollatzResearch.WordTrace tailWord_2500611 prefixEnd_2500611 142668374768913453518045 := by
  unfold tailWord_2500611
  simp only [CollatzResearch.WordTrace]
  refine ⟨91204775943720892203101687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60803183962480594802067791 91204775943720892203101687)
  ·
    refine ⟨136807163915581338304652531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91204775943720892203101687 136807163915581338304652531)
    ·
      refine ⟨205210745873372007456978797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136807163915581338304652531 205210745873372007456978797)
      ·
        refine ⟨76954029702514502796367049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205210745873372007456978797 76954029702514502796367049)
        ·
          refine ⟨57715522276885877097275287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76954029702514502796367049 57715522276885877097275287)
          ·
            refine ⟨86573283415328815645912931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57715522276885877097275287 86573283415328815645912931)
            ·
              refine ⟨129859925122993223468869397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86573283415328815645912931 129859925122993223468869397)
              ·
                refine ⟨6087183990140307350103253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129859925122993223468869397 6087183990140307350103253)
                ·
                  refine ⟨142668374768913453518045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6087183990140307350103253 142668374768913453518045)
                  ·
                    rfl

theorem cell23_2500611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 7].length) (baseStart_2500611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500611 prefixEnd_2500611 := by exact prefixLift 2500611
  have htrace : WordTrace (prefixWord ++ tailWord_2500611) baseStart_2500611 baseEnd_2500611 := by
    simpa [prefixWord, tailWord_2500611, baseEnd_2500611] using wordTrace_append hprefix tailTrace_2500611
  have hstable : (prefixWord ++ tailWord_2500611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500611).length < 2 ^ (prefixWord ++ tailWord_2500611).sum := by decide
  have hdescent : baseEnd_2500611 < baseStart_2500611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500645 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 5]
def baseStart_2500645 : Nat := 118140960795 + 2500645 * 2 ^ 59
def prefixEnd_2500645 : Nat := 4983230072969 + 3 ^ 40 * 2500645 * 2
def baseEnd_2500645 : Nat := 142670314584719327626361

theorem tailTrace_2500645 : CollatzResearch.WordTrace tailWord_2500645 prefixEnd_2500645 142670314584719327626361 := by
  unfold tailWord_2500645
  simp only [CollatzResearch.WordTrace]
  refine ⟨91206016025597716009839389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60804010683731810673226259 91206016025597716009839389)
  ·
    refine ⟨34202256009599143503689771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91206016025597716009839389 34202256009599143503689771)
    ·
      refine ⟨51303384014398715255534657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34202256009599143503689771 51303384014398715255534657)
      ·
        refine ⟨38477538010799036441650993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51303384014398715255534657 38477538010799036441650993)
        ·
          refine ⟨28858153508099277331238245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38477538010799036441650993 28858153508099277331238245)
          ·
            refine ⟨5410903782768614499607171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28858153508099277331238245 5410903782768614499607171)
            ·
              refine ⟨8116355674152921749410757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5410903782768614499607171 8116355674152921749410757)
              ·
                refine ⟨1521816688903672828014517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8116355674152921749410757 1521816688903672828014517)
                ·
                  refine ⟨142670314584719327626361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1521816688903672828014517 142670314584719327626361)
                  ·
                    rfl

theorem cell23_2500645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_2500645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500645 prefixEnd_2500645 := by exact prefixLift 2500645
  have htrace : WordTrace (prefixWord ++ tailWord_2500645) baseStart_2500645 baseEnd_2500645 := by
    simpa [prefixWord, tailWord_2500645, baseEnd_2500645] using wordTrace_append hprefix tailTrace_2500645
  have hstable : (prefixWord ++ tailWord_2500645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500645).length < 2 ^ (prefixWord ++ tailWord_2500645).sum := by decide
  have hdescent : baseEnd_2500645 < baseStart_2500645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500651 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_2500651 : Nat := 118140960795 + 2500651 * 2 ^ 59
def prefixEnd_2500651 : Nat := 4983230072969 + 3 ^ 40 * 2500651 * 2
def baseEnd_2500651 : Nat := 1284035912146400925162221

theorem tailTrace_2500651 : CollatzResearch.WordTrace tailWord_2500651 prefixEnd_2500651 1284035912146400925162221 := by
  unfold tailWord_2500651
  simp only [CollatzResearch.WordTrace]
  refine ⟨91206234863575979034557807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60804156575717319356371871 91206234863575979034557807)
  ·
    refine ⟨136809352295363968551836711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91206234863575979034557807 136809352295363968551836711)
    ·
      refine ⟨205214028443045952827755067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136809352295363968551836711 205214028443045952827755067)
      ·
        refine ⟨307821042664568929241632601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205214028443045952827755067 307821042664568929241632601)
        ·
          refine ⟨230865781998426696931224451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307821042664568929241632601 230865781998426696931224451)
          ·
            refine ⟨346298672997640045396836677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230865781998426696931224451 346298672997640045396836677)
            ·
              refine ⟨64931001187057508511906877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346298672997640045396836677 64931001187057508511906877)
              ·
                refine ⟨24349125445146565691965079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64931001187057508511906877 24349125445146565691965079)
                ·
                  refine ⟨36523688167719848537947619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24349125445146565691965079 36523688167719848537947619)
                  ·
                    refine ⟨54785532251579772806921429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36523688167719848537947619 54785532251579772806921429)
                    ·
                      refine ⟨1284035912146400925162221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54785532251579772806921429 1284035912146400925162221)
                      ·
                        rfl

theorem cell23_2500651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_2500651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500651 prefixEnd_2500651 := by exact prefixLift 2500651
  have htrace : WordTrace (prefixWord ++ tailWord_2500651) baseStart_2500651 baseEnd_2500651 := by
    simpa [prefixWord, tailWord_2500651, baseEnd_2500651] using wordTrace_append hprefix tailTrace_2500651
  have hstable : (prefixWord ++ tailWord_2500651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500651).length < 2 ^ (prefixWord ++ tailWord_2500651).sum := by decide
  have hdescent : baseEnd_2500651 < baseStart_2500651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500695 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_2500695 : Nat := 118140960795 + 2500695 * 2 ^ 59
def prefixEnd_2500695 : Nat := 4983230072969 + 3 ^ 40 * 2500695 * 2
def baseEnd_2500695 : Nat := 1284058505295198753012019

theorem tailTrace_2500695 : CollatzResearch.WordTrace tailWord_2500695 prefixEnd_2500695 1284058505295198753012019 := by
  unfold tailWord_2500695
  simp only [CollatzResearch.WordTrace]
  refine ⟨91207839675416574549159539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60805226450277716366106359 91207839675416574549159539)
  ·
    refine ⟨136811759513124861823739309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91207839675416574549159539 136811759513124861823739309)
    ·
      refine ⟨51304409817421823183902241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136811759513124861823739309 51304409817421823183902241)
      ·
        refine ⟨38478307363066367387926681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51304409817421823183902241 38478307363066367387926681)
        ·
          refine ⟨28858730522299775540945011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38478307363066367387926681 28858730522299775540945011)
          ·
            refine ⟨43288095783449663311417517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28858730522299775540945011 43288095783449663311417517)
            ·
              refine ⟨16233035918793623741781569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43288095783449663311417517 16233035918793623741781569)
              ·
                refine ⟨12174776939095217806336177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16233035918793623741781569 12174776939095217806336177)
                ·
                  refine ⟨9131082704321413354752133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12174776939095217806336177 9131082704321413354752133)
                  ·
                    refine ⟨1712078007060265004016025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9131082704321413354752133 1712078007060265004016025)
                    ·
                      refine ⟨1284058505295198753012019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712078007060265004016025 1284058505295198753012019)
                      ·
                        rfl

theorem cell23_2500695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_2500695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500695 prefixEnd_2500695 := by exact prefixLift 2500695
  have htrace : WordTrace (prefixWord ++ tailWord_2500695) baseStart_2500695 baseEnd_2500695 := by
    simpa [prefixWord, tailWord_2500695, baseEnd_2500695] using wordTrace_append hprefix tailTrace_2500695
  have hstable : (prefixWord ++ tailWord_2500695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500695).length < 2 ^ (prefixWord ++ tailWord_2500695).sum := by decide
  have hdescent : baseEnd_2500695 < baseStart_2500695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500728 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2500728 : Nat := 118140960795 + 2500728 * 2 ^ 59
def prefixEnd_2500728 : Nat := 4983230072969 + 3 ^ 40 * 2500728 * 2
def baseEnd_2500728 : Nat := 1284075450156797123899367

theorem tailTrace_2500728 : CollatzResearch.WordTrace tailWord_2500728 prefixEnd_2500728 1284075450156797123899367 := by
  unfold tailWord_2500728
  simp only [CollatzResearch.WordTrace]
  refine ⟨45604521642148510592555419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60806028856198014123407225 45604521642148510592555419)
  ·
    refine ⟨68406782463222765888833129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45604521642148510592555419 68406782463222765888833129)
    ·
      refine ⟨51305086847417074416624847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68406782463222765888833129 51305086847417074416624847)
      ·
        refine ⟨76957630271125611624937271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51305086847417074416624847 76957630271125611624937271)
        ·
          refine ⟨115436445406688417437405907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76957630271125611624937271 115436445406688417437405907)
          ·
            refine ⟨173154668110032626156108861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115436445406688417437405907 173154668110032626156108861)
            ·
              refine ⟨64933000541262234808540823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173154668110032626156108861 64933000541262234808540823)
              ·
                refine ⟨97399500811893352212811235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64933000541262234808540823 97399500811893352212811235)
                ·
                  refine ⟨146099251217840028319216853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97399500811893352212811235 146099251217840028319216853)
                  ·
                    refine ⟨3424201200418125663731645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146099251217840028319216853 3424201200418125663731645)
                    ·
                      refine ⟨1284075450156797123899367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3424201200418125663731645 1284075450156797123899367)
                      ·
                        rfl

theorem cell23_2500728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2500728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500728 prefixEnd_2500728 := by exact prefixLift 2500728
  have htrace : WordTrace (prefixWord ++ tailWord_2500728) baseStart_2500728 baseEnd_2500728 := by
    simpa [prefixWord, tailWord_2500728, baseEnd_2500728] using wordTrace_append hprefix tailTrace_2500728
  have hstable : (prefixWord ++ tailWord_2500728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500728).length < 2 ^ (prefixWord ++ tailWord_2500728).sum := by decide
  have hdescent : baseEnd_2500728 < baseStart_2500728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500739 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 1, 4]
def baseStart_2500739 : Nat := 118140960795 + 2500739 * 2 ^ 59
def prefixEnd_2500739 : Nat := 4983230072969 + 3 ^ 40 * 2500739 * 2
def baseEnd_2500739 : Nat := 428027032814665526953939

theorem tailTrace_2500739 : CollatzResearch.WordTrace tailWord_2500739 prefixEnd_2500739 428027032814665526953939 := by
  unfold tailWord_2500739
  simp only [CollatzResearch.WordTrace]
  refine ⟨91209444487257170063761271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60806296324838113375840847 91209444487257170063761271)
  ·
    refine ⟨136814166730885755095641907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91209444487257170063761271 136814166730885755095641907)
    ·
      refine ⟨205221250096328632643462861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136814166730885755095641907 205221250096328632643462861)
      ·
        refine ⟨76957968786123237241298573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205221250096328632643462861 76957968786123237241298573)
        ·
          refine ⟨28859238294796213965486965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76957968786123237241298573 28859238294796213965486965)
          ·
            refine ⟨2705553590137145059264403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28859238294796213965486965 2705553590137145059264403)
            ·
              refine ⟨4058330385205717588896605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705553590137145059264403 4058330385205717588896605)
              ·
                refine ⟨1521873894452144095836227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4058330385205717588896605 1521873894452144095836227)
                ·
                  refine ⟨2282810841678216143754341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521873894452144095836227 2282810841678216143754341)
                  ·
                    refine ⟨428027032814665526953939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282810841678216143754341 428027032814665526953939)
                    ·
                      rfl

theorem cell23_2500739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 4].length) (baseStart_2500739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500739 prefixEnd_2500739 := by exact prefixLift 2500739
  have htrace : WordTrace (prefixWord ++ tailWord_2500739) baseStart_2500739 baseEnd_2500739 := by
    simpa [prefixWord, tailWord_2500739, baseEnd_2500739] using wordTrace_append hprefix tailTrace_2500739
  have hstable : (prefixWord ++ tailWord_2500739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500739).length < 2 ^ (prefixWord ++ tailWord_2500739).sum := by decide
  have hdescent : baseEnd_2500739 < baseStart_2500739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500748 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_2500748 : Nat := 118140960795 + 2500748 * 2 ^ 59
def prefixEnd_2500748 : Nat := 4983230072969 + 3 ^ 40 * 2500748 * 2
def baseEnd_2500748 : Nat := 428028573256629015216425

theorem tailTrace_2500748 : CollatzResearch.WordTrace tailWord_2500748 prefixEnd_2500748 428028573256629015216425 := by
  unfold tailWord_2500748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45604886372112282300419449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60806515162816376400559265 45604886372112282300419449)
  ·
    refine ⟨34203664779084211725314587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45604886372112282300419449 34203664779084211725314587)
    ·
      refine ⟨51305497168626317587971881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34203664779084211725314587 51305497168626317587971881)
      ·
        refine ⟨38479122876469738190978911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51305497168626317587971881 38479122876469738190978911)
        ·
          refine ⟨57718684314704607286468367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38479122876469738190978911 57718684314704607286468367)
          ·
            refine ⟨86578026472056910929702551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57718684314704607286468367 86578026472056910929702551)
            ·
              refine ⟨129867039708085366394553827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86578026472056910929702551 129867039708085366394553827)
              ·
                refine ⟨194800559562128049591830741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129867039708085366394553827 194800559562128049591830741)
                ·
                  refine ⟨4565638114737376162308533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 194800559562128049591830741 4565638114737376162308533)
                  ·
                    refine ⟨428028573256629015216425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4565638114737376162308533 428028573256629015216425)
                    ·
                      rfl

theorem cell23_2500748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_2500748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500748 prefixEnd_2500748 := by exact prefixLift 2500748
  have htrace : WordTrace (prefixWord ++ tailWord_2500748) baseStart_2500748 baseEnd_2500748 := by
    simpa [prefixWord, tailWord_2500748, baseEnd_2500748] using wordTrace_append hprefix tailTrace_2500748
  have hstable : (prefixWord ++ tailWord_2500748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500748).length < 2 ^ (prefixWord ++ tailWord_2500748).sum := by decide
  have hdescent : baseEnd_2500748 < baseStart_2500748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500756 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2500756 : Nat := 118140960795 + 2500756 * 2 ^ 59
def prefixEnd_2500756 : Nat := 4983230072969 + 3 ^ 40 * 2500756 * 2
def baseEnd_2500756 : Nat := 428029942538374338116413

theorem tailTrace_2500756 : CollatzResearch.WordTrace tailWord_2500756 prefixEnd_2500756 428029942538374338116413 := by
  unfold tailWord_2500756
  simp only [CollatzResearch.WordTrace]
  refine ⟨45605032264097790983565061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60806709685463721311420081 45605032264097790983565061)
  ·
    refine ⟨8550943549518335809418449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45605032264097790983565061 8550943549518335809418449)
    ·
      refine ⟨6413207662138751857063837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8550943549518335809418449 6413207662138751857063837)
      ·
        refine ⟨2404952873302031946398939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6413207662138751857063837 2404952873302031946398939)
        ·
          refine ⟨3607429309953047919598409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404952873302031946398939 3607429309953047919598409)
          ·
            refine ⟨2705571982464785939698807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607429309953047919598409 2705571982464785939698807)
            ·
              refine ⟨4058357973697178909548211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705571982464785939698807 4058357973697178909548211)
              ·
                refine ⟨6087536960545768364322317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058357973697178909548211 6087536960545768364322317)
                ·
                  refine ⟨2282826360204663136620869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6087536960545768364322317 2282826360204663136620869)
                  ·
                    refine ⟨428029942538374338116413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282826360204663136620869 428029942538374338116413)
                    ·
                      rfl

theorem cell23_2500756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2500756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500756 prefixEnd_2500756 := by exact prefixLift 2500756
  have htrace : WordTrace (prefixWord ++ tailWord_2500756) baseStart_2500756 baseEnd_2500756 := by
    simpa [prefixWord, tailWord_2500756, baseEnd_2500756] using wordTrace_append hprefix tailTrace_2500756
  have hstable : (prefixWord ++ tailWord_2500756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500756).length < 2 ^ (prefixWord ++ tailWord_2500756).sum := by decide
  have hdescent : baseEnd_2500756 < baseStart_2500756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500805 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_2500805 : Nat := 118140960795 + 2500805 * 2 ^ 59
def prefixEnd_2500805 : Nat := 4983230072969 + 3 ^ 40 * 2500805 * 2
def baseEnd_2500805 : Nat := 1284114988167193322636513

theorem tailTrace_2500805 : CollatzResearch.WordTrace tailWord_2500805 prefixEnd_2500805 1284114988167193322636513 := by
  unfold tailWord_2500805
  simp only [CollatzResearch.WordTrace]
  refine ⟨91211851705018063335663869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60807901136678708890442579 91211851705018063335663869)
  ·
    refine ⟨34204444389381773750873951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91211851705018063335663869 34204444389381773750873951)
    ·
      refine ⟨51306666584072660626310927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34204444389381773750873951 51306666584072660626310927)
      ·
        refine ⟨76959999876108990939466391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51306666584072660626310927 76959999876108990939466391)
        ·
          refine ⟨115439999814163486409199587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76959999876108990939466391 115439999814163486409199587)
          ·
            refine ⟨173159999721245229613799381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115439999814163486409199587 173159999721245229613799381)
            ·
              refine ⟨4058437493466685069073423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173159999721245229613799381 4058437493466685069073423)
              ·
                refine ⟨6087656240200027603610135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058437493466685069073423 6087656240200027603610135)
                ·
                  refine ⟨9131484360300041405415203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6087656240200027603610135 9131484360300041405415203)
                  ·
                    refine ⟨13697226540450062108122805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9131484360300041405415203 13697226540450062108122805)
                    ·
                      refine ⟨1284114988167193322636513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13697226540450062108122805 1284114988167193322636513)
                      ·
                        rfl

theorem cell23_2500805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_2500805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500805 prefixEnd_2500805 := by exact prefixLift 2500805
  have htrace : WordTrace (prefixWord ++ tailWord_2500805) baseStart_2500805 baseEnd_2500805 := by
    simpa [prefixWord, tailWord_2500805, baseEnd_2500805] using wordTrace_append hprefix tailTrace_2500805
  have hstable : (prefixWord ++ tailWord_2500805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500805).length < 2 ^ (prefixWord ++ tailWord_2500805).sum := by decide
  have hdescent : baseEnd_2500805 < baseStart_2500805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500829 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2500829 : Nat := 118140960795 + 2500829 * 2 ^ 59
def prefixEnd_2500829 : Nat := 4983230072969 + 3 ^ 40 * 2500829 * 2
def baseEnd_2500829 : Nat := 428042437234300409578801

theorem tailTrace_2500829 : CollatzResearch.WordTrace tailWord_2500829 prefixEnd_2500829 428042437234300409578801 := by
  unfold tailWord_2500829
  simp only [CollatzResearch.WordTrace]
  refine ⟨91212727056931115434537541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60808484704620743623025027 91212727056931115434537541)
  ·
    refine ⟨17102386323174584143975789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91212727056931115434537541 17102386323174584143975789)
    ·
      refine ⟨6413394871190469053990921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17102386323174584143975789 6413394871190469053990921)
      ·
        refine ⟨4810046153392851790493191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6413394871190469053990921 4810046153392851790493191)
        ·
          refine ⟨7215069230089277685739787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810046153392851790493191 7215069230089277685739787)
          ·
            refine ⟨10822603845133916528609681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215069230089277685739787 10822603845133916528609681)
            ·
              refine ⟨8116952883850437396457261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10822603845133916528609681 8116952883850437396457261)
              ·
                refine ⟨3043857331443914023671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8116952883850437396457261 3043857331443914023671473)
                ·
                  refine ⟨2282892998582935517753605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043857331443914023671473 2282892998582935517753605)
                  ·
                    refine ⟨428042437234300409578801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282892998582935517753605 428042437234300409578801)
                    ·
                      rfl

theorem cell23_2500829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2500829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500829 prefixEnd_2500829 := by exact prefixLift 2500829
  have htrace : WordTrace (prefixWord ++ tailWord_2500829) baseStart_2500829 baseEnd_2500829 := by
    simpa [prefixWord, tailWord_2500829, baseEnd_2500829] using wordTrace_append hprefix tailTrace_2500829
  have hstable : (prefixWord ++ tailWord_2500829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500829).length < 2 ^ (prefixWord ++ tailWord_2500829).sum := by decide
  have hdescent : baseEnd_2500829 < baseStart_2500829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500885 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2500885 : Nat := 118140960795 + 2500885 * 2 ^ 59
def prefixEnd_2500885 : Nat := 4983230072969 + 3 ^ 40 * 2500885 * 2
def baseEnd_2500885 : Nat := 428052022206517669878715

theorem tailTrace_2500885 : CollatzResearch.WordTrace tailWord_2500885 prefixEnd_2500885 428052022206517669878715 := by
  unfold tailWord_2500885
  simp only [CollatzResearch.WordTrace]
  refine ⟨91214769544728236998576109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60809846363152157999050739 91214769544728236998576109)
  ·
    refine ⟨34205538579273088874466041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91214769544728236998576109 34205538579273088874466041)
    ·
      refine ⟨25654153934454816655849531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34205538579273088874466041 25654153934454816655849531)
      ·
        refine ⟨38481230901682224983774297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25654153934454816655849531 38481230901682224983774297)
        ·
          refine ⟨28860923176261668737830723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38481230901682224983774297 28860923176261668737830723)
          ·
            refine ⟨43291384764392503106746085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28860923176261668737830723 43291384764392503106746085)
            ·
              refine ⟨8117134643323594332514891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43291384764392503106746085 8117134643323594332514891)
              ·
                refine ⟨12175701964985391498772337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117134643323594332514891 12175701964985391498772337)
                ·
                  refine ⟨9131776473739043624079253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12175701964985391498772337 9131776473739043624079253)
                  ·
                    refine ⟨428052022206517669878715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9131776473739043624079253 428052022206517669878715)
                    ·
                      rfl

theorem cell23_2500885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2500885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500885 prefixEnd_2500885 := by exact prefixLift 2500885
  have htrace : WordTrace (prefixWord ++ tailWord_2500885) baseStart_2500885 baseEnd_2500885 := by
    simpa [prefixWord, tailWord_2500885, baseEnd_2500885] using wordTrace_append hprefix tailTrace_2500885
  have hstable : (prefixWord ++ tailWord_2500885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500885).length < 2 ^ (prefixWord ++ tailWord_2500885).sum := by decide
  have hdescent : baseEnd_2500885 < baseStart_2500885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500896 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2500896 : Nat := 118140960795 + 2500896 * 2 ^ 59
def prefixEnd_2500896 : Nat := 4983230072969 + 3 ^ 40 * 2500896 * 2
def baseEnd_2500896 : Nat := 1284161714906752466598595

theorem tailTrace_2500896 : CollatzResearch.WordTrace tailWord_2500896 prefixEnd_2500896 1284161714906752466598595 := by
  unfold tailWord_2500896
  simp only [CollatzResearch.WordTrace]
  refine ⟨45607585373844192938613271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60810113831792257251484361 45607585373844192938613271)
  ·
    refine ⟨68411378060766289407919907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45607585373844192938613271 68411378060766289407919907)
    ·
      refine ⟨102617067091149434111879861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68411378060766289407919907 102617067091149434111879861)
      ·
        refine ⟨9620350039795259447988737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102617067091149434111879861 9620350039795259447988737)
        ·
          refine ⟨7215262529846444585991553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9620350039795259447988737 7215262529846444585991553)
          ·
            refine ⟨5411446897384833439493665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215262529846444585991553 5411446897384833439493665)
            ·
              refine ⟨4058585173038625079620249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411446897384833439493665 4058585173038625079620249)
              ·
                refine ⟨3043938879778968809715187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058585173038625079620249 3043938879778968809715187)
                ·
                  refine ⟨4565908319668453214572781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043938879778968809715187 4565908319668453214572781)
                  ·
                    refine ⟨1712215619875669955464793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4565908319668453214572781 1712215619875669955464793)
                    ·
                      refine ⟨1284161714906752466598595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712215619875669955464793 1284161714906752466598595)
                      ·
                        rfl

theorem cell23_2500896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2500896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500896 prefixEnd_2500896 := by exact prefixLift 2500896
  have htrace : WordTrace (prefixWord ++ tailWord_2500896) baseStart_2500896 baseEnd_2500896 := by
    simpa [prefixWord, tailWord_2500896, baseEnd_2500896] using wordTrace_append hprefix tailTrace_2500896
  have hstable : (prefixWord ++ tailWord_2500896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500896).length < 2 ^ (prefixWord ++ tailWord_2500896).sum := by decide
  have hdescent : baseEnd_2500896 < baseStart_2500896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500926 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_2500926 : Nat := 118140960795 + 2500926 * 2 ^ 59
def prefixEnd_2500926 : Nat := 4983230072969 + 3 ^ 40 * 2500926 * 2
def baseEnd_2500926 : Nat := 1284177119326387349223457

theorem tailTrace_2500926 : CollatzResearch.WordTrace tailWord_2500926 prefixEnd_2500926 1284177119326387349223457 := by
  unfold tailWord_2500926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402033117197462625102329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60810843291719800667212421 11402033117197462625102329)
  ·
    refine ⟨8551524837898096968826747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11402033117197462625102329 8551524837898096968826747)
    ·
      refine ⟨12827287256847145453240121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8551524837898096968826747 12827287256847145453240121)
      ·
        refine ⟨9620465442635359089930091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12827287256847145453240121 9620465442635359089930091)
        ·
          refine ⟨14430698163953038634895137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620465442635359089930091 14430698163953038634895137)
          ·
            refine ⟨10823023622964778976171353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14430698163953038634895137 10823023622964778976171353)
            ·
              refine ⟨8117267717223584232128515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823023622964778976171353 8117267717223584232128515)
              ·
                refine ⟨12175901575835376348192773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117267717223584232128515 12175901575835376348192773)
                ·
                  refine ⟨2282981545469133065286145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12175901575835376348192773 2282981545469133065286145)
                  ·
                    refine ⟨1712236159101849798964609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2282981545469133065286145 1712236159101849798964609)
                    ·
                      refine ⟨1284177119326387349223457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712236159101849798964609 1284177119326387349223457)
                      ·
                        rfl

theorem cell23_2500926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_2500926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500926 prefixEnd_2500926 := by exact prefixLift 2500926
  have htrace : WordTrace (prefixWord ++ tailWord_2500926) baseStart_2500926 baseEnd_2500926 := by
    simpa [prefixWord, tailWord_2500926, baseEnd_2500926] using wordTrace_append hprefix tailTrace_2500926
  have hstable : (prefixWord ++ tailWord_2500926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500926).length < 2 ^ (prefixWord ++ tailWord_2500926).sum := by decide
  have hdescent : baseEnd_2500926 < baseStart_2500926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500952 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_2500952 : Nat := 118140960795 + 2500952 * 2 ^ 59
def prefixEnd_2500952 : Nat := 4983230072969 + 3 ^ 40 * 2500952 * 2
def baseEnd_2500952 : Nat := 1284190469823404247498337

theorem tailTrace_2500952 : CollatzResearch.WordTrace tailWord_2500952 prefixEnd_2500952 1284190469823404247498337 := by
  unfold tailWord_2500952
  simp only [CollatzResearch.WordTrace]
  refine ⟨45608606617742753720632555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60811475490323671627510073 45608606617742753720632555)
  ·
    refine ⟨68412909926614130580948833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45608606617742753720632555 68412909926614130580948833)
    ·
      refine ⟨51309682444960597935711625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68412909926614130580948833 51309682444960597935711625)
      ·
        refine ⟨38482261833720448451783719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51309682444960597935711625 38482261833720448451783719)
        ·
          refine ⟨57723392750580672677675579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38482261833720448451783719 57723392750580672677675579)
          ·
            refine ⟨86585089125871009016513369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57723392750580672677675579 86585089125871009016513369)
            ·
              refine ⟨64938816844403256762385027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86585089125871009016513369 64938816844403256762385027)
              ·
                refine ⟨97408225266604885143577541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64938816844403256762385027 97408225266604885143577541)
                ·
                  refine ⟨18264042237488415964420789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97408225266604885143577541 18264042237488415964420789)
                  ·
                    refine ⟨1712253959764538996664449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18264042237488415964420789 1712253959764538996664449)
                    ·
                      refine ⟨1284190469823404247498337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712253959764538996664449 1284190469823404247498337)
                      ·
                        rfl

theorem cell23_2500952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_2500952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500952 prefixEnd_2500952 := by exact prefixLift 2500952
  have htrace : WordTrace (prefixWord ++ tailWord_2500952) baseStart_2500952 baseEnd_2500952 := by
    simpa [prefixWord, tailWord_2500952, baseEnd_2500952] using wordTrace_append hprefix tailTrace_2500952
  have hstable : (prefixWord ++ tailWord_2500952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500952).length < 2 ^ (prefixWord ++ tailWord_2500952).sum := by decide
  have hdescent : baseEnd_2500952 < baseStart_2500952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500985 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2500985 : Nat := 118140960795 + 2500985 * 2 ^ 59
def prefixEnd_2500985 : Nat := 4983230072969 + 3 ^ 40 * 2500985 * 2
def baseEnd_2500985 : Nat := 1284207414685002618385685

theorem tailTrace_2500985 : CollatzResearch.WordTrace tailWord_2500985 prefixEnd_2500985 1284207414685002618385685 := by
  unfold tailWord_2500985
  simp only [CollatzResearch.WordTrace]
  refine ⟨91218416844365954077216409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60812277896243969384810939 91218416844365954077216409)
  ·
    refine ⟨68413812633274465557912307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91218416844365954077216409 68413812633274465557912307)
    ·
      refine ⟨102620718949911698336868461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68413812633274465557912307 102620718949911698336868461)
      ·
        refine ⟨38482769606216886876325673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102620718949911698336868461 38482769606216886876325673)
        ·
          refine ⟨28862077204662665157244255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38482769606216886876325673 28862077204662665157244255)
          ·
            refine ⟨43293115806993997735866383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28862077204662665157244255 43293115806993997735866383)
            ·
              refine ⟨64939673710490996603799575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43293115806993997735866383 64939673710490996603799575)
              ·
                refine ⟨97409510565736494905699363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64939673710490996603799575 97409510565736494905699363)
                ·
                  refine ⟨146114265848604742358549045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97409510565736494905699363 146114265848604742358549045)
                  ·
                    refine ⟨13698212423306694596113973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146114265848604742358549045 13698212423306694596113973)
                    ·
                      refine ⟨1284207414685002618385685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13698212423306694596113973 1284207414685002618385685)
                      ·
                        rfl

theorem cell23_2500985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2500985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500985 prefixEnd_2500985 := by exact prefixLift 2500985
  have htrace : WordTrace (prefixWord ++ tailWord_2500985) baseStart_2500985 baseEnd_2500985 := by
    simpa [prefixWord, tailWord_2500985, baseEnd_2500985] using wordTrace_append hprefix tailTrace_2500985
  have hstable : (prefixWord ++ tailWord_2500985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500985).length < 2 ^ (prefixWord ++ tailWord_2500985).sum := by decide
  have hdescent : baseEnd_2500985 < baseStart_2500985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500999 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_2500999 : Nat := 118140960795 + 2500999 * 2 ^ 59
def prefixEnd_2500999 : Nat := 4983230072969 + 3 ^ 40 * 2500999 * 2
def baseEnd_2500999 : Nat := 1284214603414165563610621

theorem tailTrace_2500999 : CollatzResearch.WordTrace tailWord_2500999 prefixEnd_2500999 1284214603414165563610621 := by
  unfold tailWord_2500999
  simp only [CollatzResearch.WordTrace]
  refine ⟨91218927466315234468226051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60812618310876822978817367 91218927466315234468226051)
  ·
    refine ⟨136828391199472851702339077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91218927466315234468226051 136828391199472851702339077)
    ·
      refine ⟨25655323349901159694188577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136828391199472851702339077 25655323349901159694188577)
      ·
        refine ⟨19241492512425869770641433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25655323349901159694188577 19241492512425869770641433)
        ·
          refine ⟨14431119384319402327981075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19241492512425869770641433 14431119384319402327981075)
          ·
            refine ⟨21646679076479103491971613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431119384319402327981075 21646679076479103491971613)
            ·
              refine ⟨8117504653679663809489355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21646679076479103491971613 8117504653679663809489355)
              ·
                refine ⟨12176256980519495714234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117504653679663809489355 12176256980519495714234033)
                ·
                  refine ⟨9132192735389621785675525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12176256980519495714234033 9132192735389621785675525)
                  ·
                    refine ⟨1712286137885554084814161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9132192735389621785675525 1712286137885554084814161)
                    ·
                      refine ⟨1284214603414165563610621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1712286137885554084814161 1284214603414165563610621)
                      ·
                        rfl

theorem cell23_2500999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_2500999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2500999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2500999 prefixEnd_2500999 := by exact prefixLift 2500999
  have htrace : WordTrace (prefixWord ++ tailWord_2500999) baseStart_2500999 baseEnd_2500999 := by
    simpa [prefixWord, tailWord_2500999, baseEnd_2500999] using wordTrace_append hprefix tailTrace_2500999
  have hstable : (prefixWord ++ tailWord_2500999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500999).length < 2 ^ (prefixWord ++ tailWord_2500999).sum := by decide
  have hdescent : baseEnd_2500999 < baseStart_2500999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501016 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2501016 : Nat := 118140960795 + 2501016 * 2 ^ 59
def prefixEnd_2501016 : Nat := 4983230072969 + 3 ^ 40 * 2501016 * 2
def baseEnd_2501016 : Nat := 1284223332585291997098043

theorem tailTrace_2501016 : CollatzResearch.WordTrace tailWord_2501016 prefixEnd_2501016 1284223332585291997098043 := by
  unfold tailWord_2501016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45609773753626823185797451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60813031671502430914396601 45609773753626823185797451)
  ·
    refine ⟨68414660630440234778696177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45609773753626823185797451 68414660630440234778696177)
    ·
      refine ⟨51310995472830176084022133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68414660630440234778696177 51310995472830176084022133)
      ·
        refine ⟨4810405825577829007877075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51310995472830176084022133 4810405825577829007877075)
        ·
          refine ⟨7215608738366743511815613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810405825577829007877075 7215608738366743511815613)
          ·
            refine ⟨2705853276887528816930855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7215608738366743511815613 2705853276887528816930855)
            ·
              refine ⟨4058779915331293225396283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705853276887528816930855 4058779915331293225396283)
              ·
                refine ⟨6088169872996939838094425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058779915331293225396283 6088169872996939838094425)
                ·
                  refine ⟨4566127404747704878570819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6088169872996939838094425 4566127404747704878570819)
                  ·
                    refine ⟨6849191107121557317856229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4566127404747704878570819 6849191107121557317856229)
                    ·
                      refine ⟨1284223332585291997098043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6849191107121557317856229 1284223332585291997098043)
                      ·
                        rfl

theorem cell23_2501016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2501016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2501016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2501016 prefixEnd_2501016 := by exact prefixLift 2501016
  have htrace : WordTrace (prefixWord ++ tailWord_2501016) baseStart_2501016 baseEnd_2501016 := by
    simpa [prefixWord, tailWord_2501016, baseEnd_2501016] using wordTrace_append hprefix tailTrace_2501016
  have hstable : (prefixWord ++ tailWord_2501016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501016).length < 2 ^ (prefixWord ++ tailWord_2501016).sum := by decide
  have hdescent : baseEnd_2501016 < baseStart_2501016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
